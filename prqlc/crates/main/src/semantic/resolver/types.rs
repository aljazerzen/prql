use anyhow::Result;
use itertools::Itertools;

use crate::ir::decl::DeclKind;
use crate::ir::pl::*;
use crate::semantic::ast_expand::try_restrict_range;
use crate::semantic::{write_pl, NS_THAT, NS_THIS};
use crate::{Error, Reason, WithErrorInfo};

use super::Resolver;

/// Takes a resolved [Expr] and evaluates it a type expression that can be used to construct a type.
pub fn coerce_to_type(resolver: &mut Resolver, expr: Expr) -> Result<Ty> {
    coerce_kind_to_set(resolver, expr.kind)
}

fn coerce_to_aliased_type(resolver: &mut Resolver, expr: Expr) -> Result<(Option<String>, Ty)> {
    let name = expr.alias;
    let expr = coerce_kind_to_set(resolver, expr.kind).map_err(|e| e.with_span(expr.span))?;

    Ok((name, expr))
}

fn coerce_kind_to_set(resolver: &mut Resolver, expr: ExprKind) -> Result<Ty> {
    Ok(match expr {
        // already resolved type expressions (mostly primitives)
        ExprKind::Type(set_expr) => set_expr,

        // singletons
        ExprKind::Literal(lit) => Ty::new(TyKind::Singleton(lit)),

        // tuples
        ExprKind::Tuple(elements) => {
            let mut fields = Vec::with_capacity(elements.len());
            let mut has_other = false;

            for e in elements {
                match try_restrict_range(e) {
                    // special case: {x..}
                    Ok(Range { .. }) => {
                        has_other = true;
                    }

                    // base: case
                    Err(e) => {
                        let (name, ty) = coerce_to_aliased_type(resolver, e)?;
                        let ty = Some(ty);

                        fields.push((name, ty));
                    }
                }
            }

            Ty::new(TyKind::Tuple(TyTuple { fields, has_other }))
        }

        // arrays
        ExprKind::Array(elements) => {
            if elements.len() != 1 {
                return Err(Error::new_simple(
                    "For type expressions, arrays must contain exactly one element.",
                )
                .into());
            }
            let items_type = elements.into_iter().next().unwrap();
            let (_, items_type) = coerce_to_aliased_type(resolver, items_type)?;

            Ty::new(TyKind::Array(Box::new(items_type)))
        }

        // unions
        ExprKind::RqOperator { name, args } if name == "std.or" => {
            let [left, right]: [_; 2] = args.try_into().unwrap();
            let left = coerce_to_type(resolver, left)?;
            let right = coerce_to_type(resolver, right)?;

            // flatten nested unions
            let mut options = Vec::with_capacity(2);
            if let TyKind::Union(parts) = left.kind {
                options.extend(parts);
            } else {
                options.push((left.name.clone(), left));
            }
            if let TyKind::Union(parts) = right.kind {
                options.extend(parts);
            } else {
                options.push((right.name.clone(), right));
            }

            Ty::new(TyKind::Union(options))
        }

        // functions
        ExprKind::Func(func) => Ty::new(TyFunc {
            args: func
                .params
                .into_iter()
                .map(|p| p.ty.map(|t| t.into_ty().unwrap()))
                .collect_vec(),
            return_ty: Box::new(resolver.fold_type_expr(Some(func.body))?),
        }),

        _ => {
            return Err(Error::new_simple(format!(
                "not a type expression: {}",
                write_pl(Expr::new(expr))
            ))
            .into())
        }
    })
}

impl Resolver {
    pub fn fold_type_expr(&mut self, expr: Option<Box<Expr>>) -> Result<Option<Ty>> {
        Ok(match expr {
            Some(expr) => {
                let name = expr.kind.as_ident().map(|i| i.name.clone());

                let old = self.disable_type_checking;
                self.disable_type_checking = true;
                let expr = self.fold_expr(*expr)?;
                self.disable_type_checking = old;

                let mut set_expr = coerce_to_type(self, expr)?;
                set_expr.name = set_expr.name.or(name);
                Some(set_expr)
            }
            None => None,
        })
    }

    pub fn fold_ty_or_expr(&mut self, ty_or_expr: Option<TyOrExpr>) -> Result<Option<TyOrExpr>> {
        self.root_mod.module.shadow(NS_THIS);
        self.root_mod.module.shadow(NS_THAT);

        let res = match ty_or_expr {
            Some(TyOrExpr::Expr(ty_expr)) => {
                Some(TyOrExpr::Ty(self.fold_type_expr(Some(ty_expr))?.unwrap()))
            }
            _ => ty_or_expr,
        };

        self.root_mod.module.unshadow(NS_THIS);
        self.root_mod.module.unshadow(NS_THAT);
        Ok(res)
    }

    pub fn infer_type(&mut self, expr: &Expr) -> Result<Option<Ty>> {
        if let Some(ty) = &expr.ty {
            return Ok(Some(ty.clone()));
        }
        let mut lineage = None;
        let mut instance_of = None;

        let kind = match &expr.kind {
            ExprKind::Literal(ref literal) => match literal {
                Literal::Null => TyKind::Singleton(Literal::Null),
                Literal::Integer(_) => TyKind::Primitive(PrimitiveSet::Int),
                Literal::Float(_) => TyKind::Primitive(PrimitiveSet::Float),
                Literal::Boolean(_) => TyKind::Primitive(PrimitiveSet::Bool),
                Literal::String(_) => TyKind::Primitive(PrimitiveSet::Text),
                Literal::Date(_) => TyKind::Primitive(PrimitiveSet::Date),
                Literal::Time(_) => TyKind::Primitive(PrimitiveSet::Time),
                Literal::Timestamp(_) => TyKind::Primitive(PrimitiveSet::Timestamp),
                Literal::ValueAndUnit(_) => return Ok(None), // TODO
            },

            ExprKind::Ident(_) => {
                // an ident should always provide the type of what it is referring to
                unreachable!()
            }
            ExprKind::FuncCall(_) => {
                // function calls should be resolved to [ExprKind::Func] or evaluated away.
                unreachable!()
            }

            ExprKind::SString(_) => return Ok(Some(self.root_mod.find_std_type("scalar"))),
            ExprKind::FString(_) => TyKind::Primitive(PrimitiveSet::Text),

            ExprKind::TransformCall(call) => return self.infer_type_of_transform(call).map(Some),

            ExprKind::Tuple(fields) | ExprKind::TupleFields(fields) => {
                let mut ty_fields = Vec::with_capacity(fields.len());
                let mut has_other = false;

                for field in fields {
                    let ty = self.infer_type(field)?;

                    if let ExprKind::TupleFields(_) | ExprKind::TupleExclude { .. } = &field.kind {
                        let ty = ty.unwrap();
                        let ty_tuple = ty.kind.into_tuple().unwrap();
                        ty_fields.extend(ty_tuple.fields);
                        has_other |= ty_tuple.has_other;

                        lineage = lineage.or(ty.lineage);
                        instance_of = instance_of.or(ty.instance_of);
                        continue;
                    }

                    // TODO: this will not infer nested namespaces
                    let name = field
                        .alias
                        .clone()
                        .or_else(|| field.kind.as_ident().map(|i| i.name.clone()));

                    // remove names from previous fields with the same name
                    if name.is_some() {
                        for (n, _) in ty_fields.iter_mut() {
                            if n.as_ref() == name.as_ref() {
                                *n = None;
                            }
                        }
                    }

                    ty_fields.push((name, ty));
                }

                TyKind::Tuple(TyTuple {
                    fields: ty_fields,
                    has_other,
                })
            }
            ExprKind::TupleExclude { expr, exclude } => {
                // TODO: handle non-tuples gracefully
                let ty = expr.ty.as_ref().unwrap();
                lineage = ty.lineage;
                instance_of = ty.instance_of.clone();
                let tuple = ty.kind.as_tuple().unwrap();

                // special case: all
                if tuple.has_other {
                    // Tuple has a wildcard (i.e. we don't know all the columns)
                    // which means we cannot list all columns, and we must use TupleField::All.
                    // We could do this for all columns, but it is less transparent,
                    // so let's use it just as a last resort.

                    // TODO: could there be two TupleField::All?

                    TyKind::Tuple(TyTuple {
                        fields: Vec::new(),
                        has_other: true,
                    })
                } else {
                    // base case: convert rel_def into frame columns
                    let fields = tuple
                        .fields
                        .clone()
                        .into_iter()
                        .filter(|(name, _)| match name {
                            Some(name) => !exclude.contains(&Ident::from_name(name)),
                            None => true,
                        })
                        .collect_vec();

                    TyKind::Tuple(TyTuple {
                        fields,
                        has_other: false,
                    })
                }
            }

            ExprKind::Array(items) => {
                let mut intersection = None;
                for item in items {
                    let item_ty = self.infer_type(item)?;

                    intersection = maybe_type_intersection(intersection, item_ty)
                }
                if let Some(items_ty) = intersection {
                    TyKind::Array(Box::new(items_ty))
                } else {
                    TyKind::Array(Box::new(Ty::new(TyKind::Any)))
                }
            }

            ExprKind::Indirection { expr, .. } => {
                let Some(_) = self.infer_type(expr)? else {
                    return Ok(None);
                };
                unreachable!(
                    "this should never happen because ExprKind::Indirection is only
                    construct by the resolver with also sets the expr ty"
                )
            }

            ExprKind::Func(func) => TyKind::Function(Some(TyFunc {
                args: func
                    .params
                    .iter()
                    .skip(func.args.len())
                    .map(|a| a.ty.as_ref().map(|x| x.as_ty().cloned().unwrap()))
                    .collect(),
                return_ty: Box::new(func.return_ty.as_ref().map(|x| x.as_ty().cloned().unwrap())),
            })),
            ExprKind::Case(cases) => {
                let mut variants = Vec::new();
                for case in cases {
                    let ty = self.infer_type(&case.value)?;
                    if let Some(ty) = ty {
                        variants.push((None, ty));
                    }
                }
                TyKind::Union(variants)
            }
            ExprKind::Type(_) => TyKind::Set,

            ExprKind::Param(_) | ExprKind::Internal(_) | ExprKind::RqOperator { .. } => {
                return Ok(None)
            }
        };

        lineage = lineage.or(expr.id);

        Ok(Some(Ty {
            lineage,
            instance_of,
            ..Ty::new(kind)
        }))
    }

    /// Validates that found node has expected type. Returns assumed type of the node.
    pub fn validate_expr_type<F>(
        &mut self,
        found: &mut Expr,
        expected: Option<&Ty>,
        who: &F,
    ) -> Result<(), Error>
    where
        F: Fn() -> Option<String>,
    {
        if expected.is_none() {
            // expected is none: there is no validation to be done
            return Ok(());
        };

        let Some(found_ty) = &mut found.ty else {
            // found is none: infer from expected

            // TODO: what's up with this?
            // if found.lineage.is_none() && expected.is_relation() {
                // special case: infer a table type
                // inferred tables are needed for s-strings that represent tables
                // similarly as normal table references, we want to be able to infer columns
                // of this table, which means it needs to be defined somewhere in the module structure.
                // let ty =
                    // self.declare_table_for_literal(found.id.unwrap(), None, found.alias.clone());

                // override the empty frame with frame of the new table
                // found.ty = Some(ty)
            // }

            // base case: infer expected type
            found.ty = expected.cloned();

            return Ok(());
        };

        self.validate_type(found_ty, expected, who)
            .with_span(found.span)
    }

    /// Validates that found node has expected type. Returns assumed type of the node.
    pub fn validate_type<F>(
        &mut self,
        found: &mut Ty,
        expected: Option<&Ty>,
        who: &F,
    ) -> Result<(), Error>
    where
        F: Fn() -> Option<String>,
    {
        let Some(expected) = expected else {
            // expected is none: there is no validation to be done
            return Ok(());
        };

        let expected_is_above = expected.is_super_type_of(found);

        if expected_is_above {
            // validation succeeded, return
            return Ok(());
        }

        // infer types
        if found.infer {
            // This case will happen when variable is for example an `int || timestamp`, but the
            // expected type is just `int`. If the variable allows it, we infer that the
            // variable is actually just `int`.
            let is_found_above = found.is_super_type_of(expected);

            if is_found_above {
                // This if prevents variables of for example type `int || timestamp` to be inferred
                // as `text`.
                restrict_type(found, expected.clone());

                // propagate the inference to table declarations
                if let Some(instance_of) = &found.instance_of {
                    self.push_type_info(instance_of, expected.clone())
                }
                return Ok(());
            }
        }

        return Err(compose_type_error(found, expected, who));
    }

    // This is an old attempt to validate tuple types on Expr instead of Ty.
    // It does not work when the expr is syntactically not Tuple, but has a type of a tuple.
    // fn validate_tuple_type<F>(
    //     &mut self,
    //     found_fields: &mut [Expr],
    //     expected: &Ty,
    //     who: &F,
    // ) -> Result<bool, Error>
    // where
    //     F: Fn() -> Option<String>,
    // {
    //     let Some(expected_fields) = find_potential_tuple_fields(expected) else {
    //         return Ok(false);
    //     };

    //     let mut found = found_fields.iter_mut();

    //     for expected_field in expected_fields {
    //         match expected_field {
    //             TupleField::Single(_, expected_kind) => match found.next() {
    //                 Some(found_field) => {
    //                     self.validate_type(found_field, expected_kind.as_ref(), who)?
    //                 }
    //                 None => {
    //                     return Ok(false);
    //                 }
    //             },
    //             TupleField::All {
    //                 ty: expected_wildcard,
    //                 ..
    //             } => {
    //                 for found_field in found {
    //                     self.validate_type(found_field, expected_wildcard.as_ref(), who)?;
    //                 }
    //                 return Ok(true);
    //             }
    //         }
    //     }

    //     Ok(found.next().is_none())
    // }

    /// Saves information that declaration identified by `fq_ident` must be of type `sub_ty`.
    /// Param `sub_ty` must be a sub type of the current type of the declaration.
    pub fn push_type_info(&mut self, fq_ident: &Ident, sub_ty: Ty) {
        let decl = self.root_mod.module.get_mut(fq_ident).unwrap();

        match &mut decl.kind {
            DeclKind::Expr(expr) => {
                restrict_type_opt(&mut expr.ty, Some(sub_ty));
            }
            DeclKind::Param(ty) => {
                restrict_type(ty, sub_ty);
            }

            DeclKind::Module(_)
            | DeclKind::LayeredModules(_)
            | DeclKind::Column(_)
            | DeclKind::Infer(_)
            | DeclKind::InstanceOf { .. }
            | DeclKind::QueryDef(_) => {
                panic!("declaration {decl} cannot have a type")
            }
        }
    }
}

fn restrict_type_opt(ty: &mut Option<Ty>, sub_ty: Option<Ty>) {
    let Some(sub_ty) = sub_ty else {
        return;
    };
    if let Some(ty) = ty {
        restrict_type(ty, sub_ty)
    } else {
        *ty = Some(sub_ty);
    }
}

fn restrict_type(ty: &mut Ty, sub_ty: Ty) {
    match (&mut ty.kind, sub_ty.kind) {
        (TyKind::Any, sub) => ty.kind = sub,

        (TyKind::Union(variants), sub_kind) => {
            let sub_ty = Ty {
                kind: sub_kind,
                ..sub_ty
            };
            let drained = variants
                .drain(..)
                .filter(|(_, variant)| variant.is_super_type_of(&sub_ty))
                .map(|(name, mut ty)| {
                    restrict_type(&mut ty, sub_ty.clone());
                    (name, ty)
                })
                .collect_vec();
            variants.extend(drained);
        }

        (kind, TyKind::Union(sub_variants)) => {
            todo!("restrict {kind} to union of {sub_variants:?}")
        }

        (TyKind::Primitive(_), _) => {}

        (TyKind::Singleton(_), _) => {}

        (TyKind::Tuple(tuple), TyKind::Tuple(sub_tuple)) => {
            for (sub_name, sub_ty) in sub_tuple.fields {
                if let Some(sub_name) = sub_name {
                    let existing = tuple
                        .fields
                        .iter_mut()
                        .find(|f| f.0.as_ref() == Some(&sub_name));

                    if let Some((_, existing)) = existing {
                        restrict_type_opt(existing, sub_ty)
                    } else {
                        tuple.fields.push((Some(sub_name), sub_ty));
                    }
                } else {
                    // TODO: insert unnamed fields?
                }
            }
        }

        (TyKind::Array(ty), TyKind::Array(sub_ty)) => restrict_type(ty, *sub_ty),

        (TyKind::Function(ty), TyKind::Function(sub_ty)) => {
            if sub_ty.is_none() {
                return;
            }
            if ty.is_none() {
                *ty = sub_ty;
                return;
            }
            if let (Some(func), Some(sub_func)) = (ty, sub_ty) {
                todo!("restrict function {func:?} to function {sub_func:?}")
            }
        }

        _ => {
            panic!("trying to restrict a type with a non sub type")
        }
    }
}

fn compose_type_error<F>(found_ty: &mut Ty, expected: &Ty, who: &F) -> Error
where
    F: Fn() -> Option<String>,
{
    fn display_ty(ty: &Ty) -> String {
        if ty.name.is_none() && ty.is_tuple() {
            "a tuple".to_string()
        } else {
            format!("type `{ty}`")
        }
    }

    let who = who();
    let is_join = who
        .as_ref()
        .map(|x| x.contains("std.join"))
        .unwrap_or_default();

    let mut e = Error::new(Reason::Expected {
        who,
        expected: display_ty(expected),
        found: display_ty(&found_ty),
    });

    if found_ty.is_function() && !expected.is_function() {
        // let func_name = found.kind.as_func().and_then(|c| c.name_hint.as_ref());
        let func_name = Some("TODO");
        let to_what = func_name
            .map(|n| format!("to function {n}"))
            .unwrap_or_else(|| "in this function call?".to_string());

        e = e.push_hint(format!("Have you forgotten an argument {to_what}?"));
    }

    if is_join && found_ty.is_tuple() && !expected.is_tuple() {
        e = e.push_hint("Try using `(...)` instead of `{...}`");
    }

    if let Some(expected_name) = &expected.name {
        let expanded = expected.kind.to_string();
        e = e.push_hint(format!("Type `{expected_name}` expands to `{expanded}`"));
    }
    e
}

#[allow(dead_code)]
fn too_many_arguments(call: &FuncCall, expected_len: usize, passed_len: usize) -> Error {
    let err = Error::new(Reason::Expected {
        who: Some(write_pl(*call.name.clone())),
        expected: format!("{} arguments", expected_len),
        found: format!("{}", passed_len),
    });
    if passed_len >= 2 {
        err.push_hint(format!(
            "if you are calling a function, you may want to add parentheses `{} [{:?} {:?}]`",
            write_pl(*call.name.clone()),
            call.args[0],
            call.args[1]
        ))
    } else {
        err
    }
}

// fn find_potential_tuple_fields(expected: &Ty) -> Option<&Vec<TupleField>> {
//     match &expected.kind {
//         TyKind::Tuple(fields) => Some(fields),
//         TyKind::Union(variants) => {
//             for (_, variant) in variants {
//                 if let Some(fields) = find_potential_tuple_fields(variant) {
//                     return Some(fields);
//                 }
//             }
//             None
//         }
//         _ => None,
//     }
// }

fn maybe_type_intersection(a: Option<Ty>, b: Option<Ty>) -> Option<Ty> {
    match (a, b) {
        (Some(a), Some(b)) => Some(type_intersection(a, b)),
        (x, None) | (None, x) => x,
    }
}

pub fn type_intersection(a: Ty, b: Ty) -> Ty {
    match (&a.kind, &b.kind) {
        (a_kind, b_kind) if a_kind == b_kind => a,

        (TyKind::Any, _) => b,
        (_, TyKind::Any) => a,

        (TyKind::Union(_), _) => type_intersection_with_union(a, b),
        (_, TyKind::Union(_)) => type_intersection_with_union(b, a),

        (TyKind::Tuple(_), TyKind::Tuple(_)) => {
            let a = a.kind.into_tuple().unwrap();
            let b = b.kind.into_tuple().unwrap();

            type_intersection_of_tuples(a, b)
        }

        (TyKind::Array(_), TyKind::Array(_)) => {
            let a = a.kind.into_array().unwrap();
            let b = b.kind.into_array().unwrap();
            Ty::new(TyKind::Array(Box::new(type_intersection(*a, *b))))
        }

        _ => Ty::new(TyKind::never()),
    }
}
fn type_intersection_with_union(union: Ty, b: Ty) -> Ty {
    let variants = union.kind.into_union().unwrap();
    let variants = variants
        .into_iter()
        .map(|(name, variant)| {
            let inter = type_intersection(variant, b.clone());

            (name, inter)
        })
        .collect_vec();

    Ty::new(TyKind::Union(variants))
}

fn type_intersection_of_tuples(a: TyTuple, b: TyTuple) -> Ty {
    let mut a_fields = a.fields.into_iter();
    let mut b_fields = b.fields.into_iter();

    let mut fields = Vec::new();
    let mut has_other = false;
    loop {
        match (a_fields.next(), b_fields.next()) {
            (None, None) => break,
            (None, Some(b_field)) => {
                if !a.has_other {
                    return Ty::new(TyKind::never());
                }
                has_other = true;
                fields.push(b_field);
            }
            (Some(a_field), None) => {
                if !b.has_other {
                    return Ty::new(TyKind::never());
                }
                has_other = true;
                fields.push(a_field);
            }
            (Some((a_name, a_ty)), Some((b_name, b_ty))) => {
                let name = match (a_name, b_name) {
                    (None, None) | (Some(_), Some(_)) => None,
                    (None, Some(n)) | (Some(n), None) => Some(n),
                };
                let ty = maybe_type_intersection(a_ty, b_ty);

                fields.push((name, ty));
            }
        }
    }

    Ty::new(TyKind::Tuple(TyTuple { fields, has_other }))
}

#[cfg(test)]
mod test {
    use super::*;

    fn parse_type(source: &str) -> Ty {
        let source_tree = format!("type x = ({})", source).into();
        let ast = crate::parser::parse(&source_tree).unwrap();

        let root_mod = crate::semantic::resolve(ast, Default::default()).unwrap();

        let ident = Ident::from_name("x");
        let decl = &root_mod.module.get(&ident).unwrap().kind;

        decl.as_expr().unwrap().kind.as_type().unwrap().clone()
    }

    #[test]
    fn test_is_super_tuples_00() {
        assert!(parse_type("{any}").is_super_type_of(&parse_type("{int}")));
        assert!(parse_type("{any..}").is_super_type_of(&parse_type("{int..}")));
    }

    #[test]
    fn test_is_super_tuples_01() {
        assert!(parse_type("{any}").is_super_type_of(&parse_type("{(int || text)}")));
        assert!(parse_type("{any..}").is_super_type_of(&parse_type("{(int || text)..}")));
    }

    #[test]
    fn test_is_super_tuples_02() {
        assert!(parse_type("{(int || text)}").is_super_type_of(&parse_type("{int}")));
        assert!(parse_type("{(int || text)..}").is_super_type_of(&parse_type("{int..}")));
    }

    #[test]
    fn test_is_super_tuples_03() {
        assert!(parse_type("{int..}").is_super_type_of(&parse_type("{}")));
        assert!(parse_type("{int..}").is_super_type_of(&parse_type("{int}")));
        assert!(parse_type("{int..}").is_super_type_of(&parse_type("{int, int}")));
        assert!(parse_type("{int..}").is_super_type_of(&parse_type("{int, int, int}")));
    }

    #[test]
    fn test_is_super_tuples_04() {
        assert!(parse_type("{text, int..}").is_super_type_of(&parse_type("{text, }")));
        assert!(parse_type("{text, int..}").is_super_type_of(&parse_type("{text, int}")));
        assert!(parse_type("{text, int..}").is_super_type_of(&parse_type("{text, int, int}")));
        assert!(parse_type("{text, int..}").is_super_type_of(&parse_type("{text, int, int, int}")));
    }
}
