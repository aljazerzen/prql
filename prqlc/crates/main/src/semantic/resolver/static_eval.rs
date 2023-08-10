//! Static analysis - compile time expression evaluation

use anyhow::Result;
use prqlc_ast::error::Error;
use prqlc_ast::expr::Ident;

use crate::ir::decl::{Decl, DeclKind};
use crate::ir::pl::{Expr, ExprKind, Literal, PlFold};
use crate::WithErrorInfo;

use super::Resolver;

impl Resolver {
    pub fn static_eval(&mut self, expr: Expr) -> Result<Expr> {
        Ok(match &expr.kind {
            ExprKind::Ident(fq_ident) => {
                let Some(decl) = self.root_mod.module.get(fq_ident) else {
                    return Ok(expr);
                };

                let DeclKind::Expr(decl_expr) = &decl.kind else {
                    return Ok(expr);
                };

                // inline only specific types of expr kinds
                match decl_expr.kind {
                    ExprKind::Type(_) | ExprKind::Func(_) => {
                        self.inline_decl(fq_ident, decl.clone(), expr.id.unwrap())?
                    }

                    // don't inline by default
                    _ => expr,
                }
            }

            ExprKind::RqOperator { .. } => static_eval_rq_operator(expr),

            ExprKind::Case(_) => static_eval_case(expr),

            _ => expr,
        })
    }

    pub fn inline_decl(&mut self, fq_ident: &Ident, decl: Decl, id: usize) -> Result<Expr> {
        let mut expr = *decl.kind.into_expr().unwrap();

        for annotation in &decl.annotations {
            apply_annotation(&mut expr, &annotation.expr)?;
        }

        if expr.ty.as_ref().map_or(false, |x| x.is_relation()) {
            let input_name = fq_ident.name.clone();

            let ty = self.create_ty_instance_of_table(fq_ident, input_name, id);

            Ok(Expr {
                kind: ExprKind::Ident(fq_ident.clone()),
                ty: Some(ty),
                ..expr
            })
        } else {
            if let ExprKind::Func(closure) = expr.kind {
                let closure = self.resolve_function_types(*closure)?;

                expr = Expr::new(ExprKind::Func(Box::new(closure)));

                if self.in_func_call_name {
                    return Ok(expr);
                }
            }

            Ok(self.fold_expr(expr)?)
        }
    }
}

fn static_eval_rq_operator(mut expr: Expr) -> Expr {
    let (name, mut args) = expr.kind.into_rq_operator().unwrap();
    match name.as_str() {
        "std.not" => {
            if let ExprKind::Literal(Literal::Boolean(val)) = &args[0].kind {
                return Expr::new(Literal::Boolean(!val));
            }
        }
        "std.neg" => match &args[0].kind {
            ExprKind::Literal(Literal::Integer(val)) => return Expr::new(Literal::Integer(-val)),
            ExprKind::Literal(Literal::Float(val)) => return Expr::new(Literal::Float(-val)),
            _ => (),
        },

        "std.eq" => {
            if let (ExprKind::Literal(left), ExprKind::Literal(right)) =
                (&args[0].kind, &args[1].kind)
            {
                // don't eval comparisons between different types of literals
                if left.as_ref() == right.as_ref() {
                    return Expr::new(Literal::Boolean(left == right));
                }
            }
        }
        "std.ne" => {
            if let (ExprKind::Literal(left), ExprKind::Literal(right)) =
                (&args[0].kind, &args[1].kind)
            {
                // don't eval comparisons between different types of literals
                if left.as_ref() == right.as_ref() {
                    return Expr::new(Literal::Boolean(left != right));
                }
            }
        }
        "std.and" => {
            if let (
                ExprKind::Literal(Literal::Boolean(left)),
                ExprKind::Literal(Literal::Boolean(right)),
            ) = (&args[0].kind, &args[1].kind)
            {
                return Expr::new(Literal::Boolean(*left && *right));
            }
        }
        "std.or" => {
            if let (
                ExprKind::Literal(Literal::Boolean(left)),
                ExprKind::Literal(Literal::Boolean(right)),
            ) = (&args[0].kind, &args[1].kind)
            {
                return Expr::new(Literal::Boolean(*left || *right));
            }
        }
        "std.coalesce" => {
            if let ExprKind::Literal(Literal::Null) = &args[0].kind {
                return args.remove(1);
            }
        }

        _ => {}
    };
    expr.kind = ExprKind::RqOperator { name, args };
    expr
}

fn static_eval_case(mut expr: Expr) -> Expr {
    let items = expr.kind.into_case().unwrap();
    let mut res = Vec::with_capacity(items.len());
    for item in items {
        if let ExprKind::Literal(Literal::Boolean(condition)) = item.condition.kind {
            if condition {
                res.push(item);
                break;
            } else {
                // this case can be removed
                continue;
            }
        } else {
            res.push(item);
        }
    }
    if res.is_empty() {
        return Expr::new(Literal::Null);
    }

    if res.len() == 1 {
        let is_true = matches!(
            res[0].condition.kind,
            ExprKind::Literal(Literal::Boolean(true))
        );
        if is_true {
            return *res.remove(0).value;
        }
    }

    expr.kind = ExprKind::Case(res);
    expr
}

fn apply_annotation(value: &mut Expr, annotation: &Expr) -> Result<()> {
    if let ExprKind::FuncCall(call) = &annotation.kind {
        if call.name.kind.as_ident().map_or("", |x| x.name.as_str()) == "implicit_closure" {
            let on = *(call.named_args.get("on"))
                .and_then(|x| x.kind.as_literal())
                .and_then(|x| x.as_integer())
                .ok_or_else(|| {
                    Error::new_simple("param `on` expected an integer").with_span(annotation.span)
                })?;

            let param_names: Vec<String> = (call.named_args.get("param_names"))
                .and_then(|x| x.kind.as_array())
                .and_then(|ar| {
                    ar.iter()
                        .map(|e| e.kind.as_ident().map(|i| i.name.clone()))
                        .collect::<Option<Vec<String>>>()
                })
                .ok_or_else(|| {
                    Error::new_simple("param `param_names` expected an array of names")
                        .with_span(annotation.span)
                })?;

            if let ExprKind::Func(func) = &mut value.kind {
                if let Some(param) = func.params.get_mut(on as usize) {
                    param.implicit_closure = Some(param_names);
                }
            }
        }
    }
    Ok(())
}
