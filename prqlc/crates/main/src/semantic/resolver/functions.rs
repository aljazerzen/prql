use std::collections::HashMap;
use std::iter::zip;

use anyhow::Result;
use itertools::Itertools;

use crate::ir::decl::{Decl, DeclKind, Module};
use crate::ir::pl::*;
use crate::{Error, Span, WithErrorInfo};

use super::transforms;
use super::{Resolver, NS_PARAM};

impl Resolver {
    pub fn fold_function(&mut self, closure: Func, span: Option<Span>) -> Result<Expr> {
        let closure = self.resolve_function_types(closure)?;

        let closure = self.resolve_function_body(closure)?;

        log::debug!(
            "func {} {}/{} params",
            closure.as_debug_name(),
            closure.args.len(),
            closure.params.len()
        );

        if closure.args.len() > closure.params.len() {
            return Err(Error::new_simple(format!(
                "Too many arguments to function `{}`",
                closure.as_debug_name()
            ))
            .with_span(span)
            .into());
        }

        let enough_args = closure.args.len() == closure.params.len();
        if !enough_args {
            return Ok(expr_of_func(closure, span));
        }

        // make sure named args are pushed into params
        let closure = if !closure.named_params.is_empty() {
            self.apply_args_to_closure(closure, [].into(), [].into())?
        } else {
            closure
        };

        // push the env
        log::debug!(
            "resolving args of function {}",
            closure
                .name_hint
                .clone()
                .unwrap_or_else(|| Ident::from_name("<unnamed>"))
        );
        let res = self.resolve_function_args(closure)?;

        let closure = match res {
            Ok(func) => func,
            Err(func) => {
                return Ok(expr_of_func(func, span));
            }
        };

        // evaluate
        let res = if let ExprKind::Internal(operator_name) = &closure.body.kind {
            // special case: functions that have internal body

            if operator_name.starts_with("std.") {
                Expr {
                    ty: closure.return_ty.map(|t| t.into_ty().unwrap()),
                    ..Expr::new(ExprKind::RqOperator {
                        name: operator_name.clone(),
                        args: closure.args,
                    })
                }
            } else {
                let expr = transforms::resolve_special_func(self, closure)?;
                self.fold_expr(expr)?
            }
        } else {
            // base case: materialize
            log::debug!("stack_push for {}", closure.as_debug_name());

            let (func_env, body) = env_of_closure(closure);

            self.root_mod.module.stack_push(NS_PARAM, func_env);

            // fold again, to resolve inner variables & functions
            let body = self.fold_expr(body)?;

            // remove param decls
            log::debug!("stack_pop: {:?}", body.id);
            let func_env = self.root_mod.module.stack_pop(NS_PARAM).unwrap();

            if let ExprKind::Func(mut inner_closure) = body.kind {
                // body couldn't been resolved - construct a closure to be evaluated later

                inner_closure.env = func_env.into_exprs();

                let (got, missing) = inner_closure.params.split_at(inner_closure.args.len());
                let missing = missing.to_vec();
                inner_closure.params = got.to_vec();

                Expr::new(ExprKind::Func(Box::new(Func {
                    name_hint: None,
                    args: vec![],
                    params: missing,
                    named_params: vec![],
                    body: Box::new(Expr::new(ExprKind::Func(inner_closure))),
                    return_ty: None,
                    env: HashMap::new(),
                })))
            } else {
                // resolved, return result
                body
            }
        };

        Ok(Expr { span, ..res })
    }

    fn resolve_function_body(&mut self, mut func: Func) -> Result<Func> {
        if super::is_resolved(&func.body) || matches!(func.body.kind, ExprKind::Internal(_)) {
            return Ok(func);
        }

        self.root_mod.module.shadow(NS_PARAM);

        // insert type definitions of the params
        let module = self.root_mod.module.names.get_mut(NS_PARAM).unwrap();
        let module = module.kind.as_module_mut().unwrap();
        for param in func.params.iter().chain(func.named_params.iter()) {
            let mut ty = (param.ty)
                .clone()
                .map(|t| t.into_ty().unwrap())
                .unwrap_or_else(|| Ty::new(TyKind::Any));

            // infer types of params during resolution of the body
            ty.infer = true;

            module.names.insert(
                param.name.clone(),
                Decl::from(DeclKind::Param(Box::new(ty))),
            );

            // this should not be done in most cases, but only when this is an implicit closure
            // module.redirects.insert(Ident::from_name(&param.name));
        }

        // the beef: resolve body
        let body = self.fold_expr(*func.body);

        // retrieve type definitions of the params
        let module = self.root_mod.module.names.get_mut(NS_PARAM).unwrap();
        let module = module.kind.as_module_mut().unwrap();
        for param in func.params.iter_mut().chain(func.named_params.iter_mut()) {
            let Some(decl) = module.names.remove(&param.name) else {
                continue;
            };

            let DeclKind::Param(ty) = decl.kind else {
                continue;
            };

            param.ty = Some(TyOrExpr::Ty(*ty));
        }

        self.root_mod.module.unshadow(NS_PARAM);

        let mut body = body?;

        // validate return type
        if let Some(body_ty) = &mut body.ty {
            let expected = func.return_ty.as_ref().and_then(|x| x.as_ty());
            let who = || {
                if let Some(name_hint) = &func.name_hint {
                    Some(format!("return type of function {name_hint}"))
                } else {
                    Some("return type".to_string())
                }
            };
            self.validate_type(body_ty, expected, &who)?;

            func.return_ty = Some(TyOrExpr::Ty(body_ty.clone()));
        }

        func.body = Box::new(body);
        Ok(func)
    }

    pub fn resolve_function_types(&mut self, mut func: Func) -> Result<Func> {
        func.params = func
            .params
            .into_iter()
            .map(|p| -> Result<_> {
                Ok(FuncParam {
                    ty: self.fold_ty_or_expr(p.ty)?,
                    ..p
                })
            })
            .try_collect()?;
        func.return_ty = self.fold_ty_or_expr(func.return_ty)?;
        Ok(func)
    }

    pub fn apply_args_to_closure(
        &mut self,
        mut closure: Func,
        args: Vec<Expr>,
        mut named_args: HashMap<String, Expr>,
    ) -> Result<Func> {
        // named arguments are consumed only by the first function

        // named
        for mut param in closure.named_params.drain(..) {
            let param_name = param.name.split('.').last().unwrap_or(&param.name);
            let default = param.default_value.take().unwrap();

            let arg = named_args.remove(param_name).unwrap_or(*default);

            closure.args.push(arg);
            closure.params.insert(closure.args.len() - 1, param);
        }
        if let Some((name, _)) = named_args.into_iter().next() {
            // TODO: report all remaining named_args as separate errors
            anyhow::bail!(
                "unknown named argument `{name}` to closure {:?}",
                closure.name_hint
            )
        }

        // positional
        closure.args.extend(args);
        Ok(closure)
    }

    /// Resolves function arguments. Will return `Err(func)` is partial application is required.
    fn resolve_function_args(&mut self, to_resolve: Func) -> Result<Result<Func, Func>> {
        let mut closure = Func {
            args: Vec::with_capacity(to_resolve.args.len()),
            ..to_resolve
        };
        let mut partial_application_position = None;

        let func_name = &closure.name_hint;

        // resolve relational args

        for (index, (param, mut arg)) in zip(&closure.params, to_resolve.args).enumerate() {
            // just fold the argument alone
            if partial_application_position.is_none() {
                arg = self
                    .fold_and_type_check(arg, param, func_name)?
                    .unwrap_or_else(|a| {
                        partial_application_position = Some(index);
                        a
                    });
            }
            log::debug!("resolved arg to {}", arg.kind.as_ref());

            closure.args.push(arg);
        }

        Ok(if let Some(position) = partial_application_position {
            log::debug!(
                "partial application of {} at arg {position}",
                closure.as_debug_name()
            );

            Err(extract_partial_application(closure, position))
        } else {
            Ok(closure)
        })
    }

    fn fold_and_type_check(
        &mut self,
        arg: Expr,
        param: &FuncParam,
        func_name: &Option<Ident>,
    ) -> Result<Result<Expr, Expr>> {
        if let Some(param_names) = &param.implicit_closure {
            let arg = Expr::new(Func {
                name_hint: None,
                return_ty: param.ty.clone(),
                body: Box::new(arg),
                params: param_names
                    .iter()
                    .map(|name| FuncParam {
                        name: name.clone(),
                        ty: None,
                        default_value: None,
                        implicit_closure: None,
                    })
                    .collect_vec(),
                named_params: Vec::new(),
                args: Vec::new(),
                env: Default::default(),
            });
            return Ok(Ok(self.fold_expr(arg)?));
        }

        let mut arg = self.fold_within_namespace(arg, &param.name)?;

        // don't validate types of unresolved exprs
        if arg.id.is_some() && !self.disable_type_checking {
            // validate type

            let expects_func = param
                .ty
                .as_ref()
                .map(|t| t.as_ty().unwrap().is_function())
                .unwrap_or_default();
            if !expects_func && arg.kind.is_func() {
                return Ok(Err(arg));
            }

            let who = || {
                func_name
                    .as_ref()
                    .map(|n| format!("function {n}, param `{}`", param.name))
            };
            let ty = param.ty.as_ref().map(|t| t.as_ty().unwrap());
            self.validate_expr_type(&mut arg, ty, &who)?;
        }

        Ok(Ok(arg))
    }

    fn fold_within_namespace(&mut self, expr: Expr, param_name: &str) -> Result<Expr> {
        if param_name.starts_with("noresolve.") {
            Ok(expr)
        } else {
            self.fold_expr(expr)
        }
    }

    /// Simulates application of a function to a value.
    pub fn simulate_func_application(&mut self, func: &Func, val_ty: &mut Ty) -> Result<Ty> {
        log::debug!("simulate_func_application {:?}", func.name_hint);

        let next_param_applied = func.args.len();
        if let Some(param) = func.params.get(next_param_applied) {
            if let Some(param_ty) = &param.ty {
                let param_ty = param_ty.as_ty().unwrap();
                super::types::restrict_type(val_ty, param_ty.clone());
            }
        }

        let body_ty = func.return_ty.as_ref().unwrap().as_ty().unwrap().clone();

        dbg!(val_ty);
        Ok(dbg!(body_ty))
    }

    /// Simulates application of a function to each item of an array.
    pub fn simulate_array_map<'a>(
        &'a mut self,
        func: &Expr,
        arr: &'a mut Expr,
    ) -> Result<(&Ty, Ty)> {
        let closure = func.kind.as_func().unwrap();
        let tbl_ty = arr.ty.as_mut().unwrap();

        let row_ty = tbl_ty.kind.as_array_mut().unwrap();

        let result_row_ty = self.simulate_func_application(closure, row_ty)?;

        Ok((row_ty, result_row_ty))
    }
}

fn extract_partial_application(mut func: Func, position: usize) -> Func {
    // Input:
    // Func {
    //     params: [x, y, z],
    //     args: [
    //         x,
    //         Func {
    //             params: [a, b],
    //             args: [a],
    //             body: arg_body
    //         },
    //         z
    //     ],
    //     body: parent_body
    // }

    // Output:
    // Func {
    //     params: [b],
    //     args: [],
    //     body: Func {
    //         params: [x, y, z],
    //         args: [
    //             x,
    //             Func {
    //                 params: [a, b],
    //                 args: [a, b],
    //                 body: arg_body
    //             },
    //             z
    //         ],
    //         body: parent_body
    //     }
    // }

    // This is quite in-efficient, especially for long pipelines.
    // Maybe it could be special-cased, for when the arg func has a single param.
    // In that case, it may be possible to pull the arg func up and basically swap
    // it with the parent func.

    let arg = func.args.get_mut(position).unwrap();
    let arg_func = arg.kind.as_func_mut().unwrap();

    let param_name = format!("_partial_{}", arg.id.unwrap());
    let substitute_arg = Expr::new(Ident::from_path(vec![
        NS_PARAM.to_string(),
        param_name.clone(),
    ]));
    arg_func.args.push(substitute_arg);

    // set the arg func body to the parent func
    Func {
        name_hint: None,
        return_ty: None,
        body: Box::new(Expr::new(func)),
        params: vec![FuncParam {
            name: param_name,
            ty: None,
            default_value: None,
            implicit_closure: None,
        }],
        named_params: Default::default(),
        args: Default::default(),
        env: Default::default(),
    }
}

fn expr_of_func(func: Func, span: Option<Span>) -> Expr {
    Expr {
        span,
        ..Expr::new(ExprKind::Func(Box::new(func)))
    }
}

fn env_of_closure(closure: Func) -> (Module, Expr) {
    let mut func_env = Module::from_exprs(closure.env);

    for (param, arg) in zip(closure.params, closure.args) {
        let v = Decl {
            declared_at: arg.id,
            kind: DeclKind::Expr(Box::new(arg)),
            ..Default::default()
        };
        let param_name = param.name.split('.').last().unwrap();
        func_env.names.insert(param_name.to_string(), v);
    }

    (func_env, *closure.body)
}
