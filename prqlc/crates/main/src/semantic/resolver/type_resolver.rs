use anyhow::Result;
use itertools::Itertools;

use crate::ir::pl::*;
use crate::semantic::ast_expand::try_restrict_range;
use crate::semantic::write_pl;
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

            ExprKind::SString(_) => return Ok(Some(self.context.find_std_type("scalar"))),
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

                    if let Some(item_ty) = item_ty {
                        if let Some(intersection) = &intersection {
                            if intersection != &item_ty {
                                // TODO: compute type intersection instead
                                return Ok(None);
                            }
                        } else {
                            intersection = Some(item_ty);
                        }
                    }
                }
                let Some(items_ty) = intersection else {
                    // TODO: return Array(Infer) instead of Infer
                    return Ok(None);
                };
                TyKind::Array(Box::new(items_ty))
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
                let instance_of = found.instance_of.take();

                *found = expected.clone();

                // propagate the inference to table declarations
                // TODO: could this be unified with [Context::infer_decl]?
                if let Some(instance_of) = instance_of {
                    let _decl = self.context.root_mod.get(&instance_of).unwrap();

                    // TODO
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

#[cfg(test)]
mod test {
    use super::*;

    fn parse_type(source: &str) -> Ty {
        let source_tree = format!("type x = ({})", source).into();
        let ast = crate::parser::parse(&source_tree).unwrap();

        let root_mod = crate::semantic::resolve(ast, Default::default()).unwrap();

        let ident = Ident::from_name("x");
        let decl = &root_mod.root_mod.get(&ident).unwrap().kind;

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
