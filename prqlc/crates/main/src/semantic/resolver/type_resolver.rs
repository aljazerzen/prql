use std::collections::HashSet;

use anyhow::Result;
use itertools::Itertools;

use crate::ir::pl::*;
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
        ExprKind::Literal(lit) => Ty::from(TyKind::Singleton(lit)),

        // tuples
        ExprKind::Tuple(mut elements) => {
            let mut set_elements = Vec::with_capacity(elements.len());

            // special case: {x..}
            if elements.len() == 1 {
                let only = elements.remove(0);
                if let ExprKind::Range(Range { start, end: None }) = only.kind {
                    let inner = match start {
                        Some(x) => Some(coerce_to_type(resolver, *x)?),
                        None => None,
                    };

                    set_elements.push(TupleField::All {
                        ty: inner,
                        exclude: HashSet::new(),
                    })
                } else {
                    elements.push(only);
                }
            }

            for e in elements {
                let (name, ty) = coerce_to_aliased_type(resolver, e)?;
                let ty = Some(ty);

                set_elements.push(TupleField::Single(name, ty));
            }

            Ty::from(TyKind::Tuple(set_elements))
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

            Ty::from(TyKind::Array(Box::new(items_type)))
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

            Ty::from(TyKind::Union(options))
        }

        // functions
        ExprKind::Func(func) => Ty::from(TyKind::Function(Some(TyFunc {
            args: func
                .params
                .into_iter()
                .map(|p| p.ty.map(|t| t.into_ty().unwrap()))
                .collect_vec(),
            return_ty: Box::new(resolver.fold_type_expr(Some(func.body))?),
        }))),

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
            ExprKind::FuncCall(_) => return Ok(None),

            ExprKind::SString(_) => return Ok(None),
            ExprKind::FString(_) => TyKind::Primitive(PrimitiveSet::Text),
            ExprKind::Range(_) => return Ok(None), // TODO

            ExprKind::TransformCall(call) => return self.infer_type_of_transform(call).map(Some),

            ExprKind::Tuple(fields) | ExprKind::TupleFields(fields) => {
                let mut ty_fields = Vec::with_capacity(fields.len());

                for field in fields {
                    let ty = self.infer_type(field)?;

                    if let ExprKind::TupleFields(_) | ExprKind::TupleExclude { .. } = &field.kind {
                        let ty = ty.unwrap();
                        ty_fields.extend(ty.kind.into_tuple().unwrap());
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
                        for x in ty_fields.iter_mut() {
                            if let TupleField::Single(n, _) = x {
                                if n.as_ref() == name.as_ref() {
                                    *n = None;
                                }
                            }
                        }
                    }

                    ty_fields.push(TupleField::Single(name, ty));
                }

                TyKind::Tuple(ty_fields)
            }
            ExprKind::TupleExclude { expr, exclude } => {
                // TODO: handle non-tuples gracefully
                let ty = expr.ty.as_ref().unwrap();
                lineage = ty.lineage;
                instance_of = ty.instance_of.clone();
                let tuple = ty.kind.as_tuple().unwrap();

                // special case: all
                if let Some((t, e)) = tuple.iter().find_map(|c| c.as_all()) {
                    // Tuple has a wildcard (i.e. we don't know all the columns)
                    // which means we cannot list all columns, and we must use TupleField::All.
                    // We could do this for all columns, but it is less transparent,
                    // so let's use it just as a last resort.

                    // TODO: could there be two TupleField::All?

                    let mut e = e.clone();
                    e.extend(exclude.iter().cloned());

                    let mut t = t.clone();
                    if let Some(t) = &mut t {
                        t.lineage = lineage.clone();
                        t.instance_of = instance_of.clone();
                    }

                    TyKind::Tuple(vec![TupleField::All {
                        ty: t.clone(),
                        exclude: e,
                    }])
                } else {
                    // base case: convert rel_def into frame columns
                    let fields = tuple
                        .clone()
                        .into_iter()
                        .filter(|f| {
                            let (name, _) = f.as_single().unwrap();
                            match name {
                                Some(name) => !exclude.contains(&Ident::from_name(name)),
                                None => true,
                            }
                        })
                        .collect_vec();

                    TyKind::Tuple(fields)
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

            _ => return Ok(None),
        };
        Ok(Some(Ty {
            lineage,
            instance_of,
            ..Ty::from(kind)
        }))
    }

    /// Validates that found node has expected type. Returns assumed type of the node.
    pub fn validate_type<F>(
        &mut self,
        found: &mut Expr,
        expected: Option<&Ty>,
        who: &F,
    ) -> Result<(), Error>
    where
        F: Fn() -> Option<String>,
    {
        let found_ty = found.ty.clone();

        // infer
        let Some(expected) = expected else {
            // expected is none: there is no validation to be done
            return Ok(());
        };

        let Some(found_ty) = found_ty else {
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
            found.ty = Some(expected.clone());

            return Ok(());
        };

        let expected_is_above = match &mut found.kind {
            // special case of container type: tuple
            ExprKind::Tuple(found_fields) => {
                let ok = self.validate_tuple_type(found_fields, expected, who)?;
                if ok {
                    return Ok(());
                }
                false
            }

            // base case: compare types
            _ => expected.is_super_type_of(&found_ty),
        };
        if !expected_is_above {
            fn display_ty(ty: &Ty) -> String {
                if ty.is_tuple() {
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

            let mut e = Err(Error::new(Reason::Expected {
                who,
                expected: display_ty(expected),
                found: display_ty(&found_ty),
            })
            .with_span(found.span));

            if found_ty.is_function() && !expected.is_function() {
                let func_name = found.kind.as_func().and_then(|c| c.name_hint.as_ref());
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

            return e;
        }
        Ok(())
    }

    fn validate_tuple_type<F>(
        &mut self,
        found_fields: &mut [Expr],
        expected: &Ty,
        who: &F,
    ) -> Result<bool, Error>
    where
        F: Fn() -> Option<String>,
    {
        let Some(expected_fields) = find_potential_tuple_fields(expected) else {
            return Ok(false);
        };

        let mut found = found_fields.iter_mut();

        for expected_field in expected_fields {
            match expected_field {
                TupleField::Single(_, expected_kind) => match found.next() {
                    Some(found_field) => {
                        self.validate_type(found_field, expected_kind.as_ref(), who)?
                    }
                    None => {
                        return Ok(false);
                    }
                },
                TupleField::All {
                    ty: expected_wildcard,
                    ..
                } => {
                    for found_field in found {
                        self.validate_type(found_field, expected_wildcard.as_ref(), who)?;
                    }
                    return Ok(true);
                }
            }
        }

        Ok(found.next().is_none())
    }
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

fn find_potential_tuple_fields(expected: &Ty) -> Option<&Vec<TupleField>> {
    match &expected.kind {
        TyKind::Tuple(fields) => Some(fields),
        TyKind::Union(variants) => {
            for (_, variant) in variants {
                if let Some(fields) = find_potential_tuple_fields(variant) {
                    return Some(fields);
                }
            }
            None
        }
        _ => None,
    }
}
