use anyhow::Result;
use itertools::Itertools;
use prqlc_ast::Span;

use crate::ir::decl::Decl;
use crate::ir::pl::*;
use crate::semantic::{write_pl, NS_DEFAULT_DB, NS_INFER, NS_THIS};
use crate::WithErrorInfo;

use super::flatten::Flattener;
use super::Resolver;

impl PlFold for Resolver {
    fn fold_stmts(&mut self, _: Vec<Stmt>) -> Result<Vec<Stmt>> {
        unreachable!()
    }

    fn fold_var_def(&mut self, var_def: VarDef) -> Result<VarDef> {
        let value = Flattener::fold(self.fold_expr(*var_def.value)?);

        Ok(VarDef {
            name: var_def.name,
            value: Box::new(value),
            ty_expr: fold_optional_box(self, var_def.ty_expr)?,
            kind: var_def.kind,
        })
    }

    fn fold_expr(&mut self, node: Expr) -> Result<Expr> {
        if node.id.is_some() && !matches!(node.kind, ExprKind::Func(_)) {
            return Ok(node);
        }

        let id = self.id.gen();
        let alias = node.alias.clone();
        let span = node.span;

        if let Some(span) = span {
            self.root_mod.span_map.insert(id, span);
        }

        log::trace!("folding expr {node:?}");

        let r = match node.kind {
            ExprKind::Ident(ident) => {
                log::debug!("resolving ident {ident}...");
                let (ty, kind) = self.resolve_ident(&ident).with_span(node.span)?;
                log::debug!("... to {}", write_pl(Expr::new(kind.clone())));

                Expr {
                    kind,
                    ty: Some(ty),
                    ..node
                }
            }

            // special case for !{}
            ExprKind::FuncCall(FuncCall { name, args, .. })
                if (name.kind.as_ident()).map_or(false, |i| i.to_string() == "std.not")
                    && matches!(args[0].kind, ExprKind::Tuple(_)) =>
            {
                let this_fields = Expr {
                    span,
                    ..Expr::new(ExprKind::Ident(Ident::from_path(vec![NS_THIS, "*"])))
                };
                let this = Expr {
                    span,
                    ..Expr::new(ExprKind::Tuple(vec![this_fields]))
                };
                let this = self.fold_expr(this).with_span(span)?;

                let exclude_tuple = args.into_iter().exactly_one().unwrap();
                let exclude_tuple = self.fold_expr(exclude_tuple)?;

                create_tuple_exclude(this, exclude_tuple, span)?
            }

            ExprKind::FuncCall(FuncCall {
                name,
                args,
                named_args,
            }) => {
                // fold function name
                let old = self.in_func_call_name;
                self.in_func_call_name = true;
                let name = self.fold_expr(*name).with_span(span)?;
                self.in_func_call_name = old;

                let func = *name.try_cast(|n| n.into_func(), None, "a function")?;

                // fold function
                let func = self.apply_args_to_closure(func, args, named_args)?;
                self.fold_function(func, span)?
            }

            ExprKind::Func(closure) => self.fold_function(*closure, span)?,

            ExprKind::Tuple(exprs) => {
                let exprs = self.fold_exprs(exprs).with_span(span)?;

                // flatten
                let mut flattened = Vec::with_capacity(exprs.len());
                for expr in exprs {
                    match expr.kind {
                        ExprKind::TupleFields(fields) => flattened.extend(fields),
                        _ => flattened.push(expr),
                    }
                }

                Expr {
                    kind: ExprKind::Tuple(flattened),
                    ..node
                }
            }

            ExprKind::Array(exprs) => {
                let mut exprs = self.fold_exprs(exprs).with_span(span)?;

                // validate that all elements have the same type
                let mut expected_ty: Option<&Ty> = None;
                for expr in &mut exprs {
                    if expr.ty.is_some() {
                        if expected_ty.is_some() {
                            let who = || Some("array".to_string());
                            self.validate_expr_type(expr, expected_ty, &who)?;
                        }
                        expected_ty = expr.ty.as_ref();
                    }
                }

                Expr {
                    kind: ExprKind::Array(exprs),
                    ..node
                }
            }

            item => Expr {
                kind: fold_expr_kind(self, item).with_span(span)?,
                ..node
            },
        };
        let mut r = r;
        r.id = r.id.or(Some(id));
        let mut r = self.static_eval(r)?;
        r.id = r.id.or(Some(id));
        r.alias = r.alias.or(alias);
        r.span = r.span.or(span);

        if r.ty.is_none() {
            r.ty = self.infer_type(&r)?;

            if r.ty.is_none() {
                panic!("cannot infer type of: {:?}", r);
            }
        }
        if let Some(ty) = &mut r.ty {
            if let Some(alias) = r.alias.clone() {
                ty.rename_relation(alias);
            }
        }
        Ok(r)
    }
}

impl Resolver {
    /// Converts a identifier that points to a table declaration to a frame of that table.
    pub fn create_ty_instance_of_table(
        &mut self,
        table_fq: &Ident,
        input_name: String,
        input_id: usize,
    ) -> Ty {
        let table_decl = self.root_mod.module.get(table_fq).unwrap();
        let table_decl = table_decl.kind.as_expr().unwrap();

        let inner = (table_decl.ty.as_ref())
            .and_then(|t| t.as_relation())
            .cloned();
        let inner = inner.unwrap_or_else(|| TyTuple {
            fields: Vec::new(),
            has_other: true,
        });

        // wrap with the tuple name
        let mut inner = Ty::new(TyKind::Tuple(inner));
        inner.lineage = Some(input_id);
        inner.instance_of = Some(table_fq.clone());
        let tuple = TyTuple {
            fields: vec![(Some(input_name), Some(inner))],
            has_other: false,
        };

        log::debug!("instanced table {table_fq} as {tuple:?}");
        Ty::relation(tuple)
    }

    /// Declares a new table for a relation literal.
    /// This is needed for column inference to work properly.
    pub fn declare_table_for_literal(
        &mut self,
        input_id: usize,
        columns: Option<Vec<TyTupleField>>,
        name_hint: Option<String>,
    ) -> Ty {
        let id = input_id;
        let global_name = format!("_literal_{}", id);

        // declare a new table in the `default_db` module
        let default_db_ident = Ident::from_name(NS_DEFAULT_DB);
        let default_db = self.root_mod.module.get_mut(&default_db_ident).unwrap();
        let default_db = default_db.kind.as_module_mut().unwrap();

        let infer_default = default_db.get(&Ident::from_name(NS_INFER)).unwrap().clone();
        let mut infer_default = *infer_default.kind.into_infer().unwrap();

        let table_decl = infer_default.as_expr_mut().unwrap();
        table_decl.kind = ExprKind::Literal(Literal::Null);

        if let Some(fields) = columns {
            table_decl.ty = Some(Ty::relation(TyTuple {
                fields,
                has_other: false,
            }));
        }

        default_db
            .names
            .insert(global_name.clone(), Decl::from(infer_default));

        // produce a frame of that table
        let input_name = name_hint.unwrap_or_else(|| global_name.clone());
        let table_fq = default_db_ident + Ident::from_name(global_name);
        self.create_ty_instance_of_table(&table_fq, input_name, id)
    }
}

pub(super) fn create_tuple_exclude(
    expr: Expr,
    exclude_tuple: Expr,
    span: Option<Span>,
) -> Result<Expr> {
    // this should not fail because of type checking
    let exclude = exclude_tuple.ty.unwrap().kind.into_tuple().unwrap();

    let exclude = exclude
        .fields
        .into_iter()
        .filter_map(|(name, _)| name.map(Ident::from_name))
        .collect();

    let expr = Box::new(expr);

    Ok(Expr {
        span,
        ..Expr::new(ExprKind::TupleExclude { expr, exclude })
    })
}
