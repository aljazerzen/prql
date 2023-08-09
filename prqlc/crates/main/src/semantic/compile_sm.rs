use anyhow::Result;
use prqlc_ast::error::Error;
use prqlc_ast::expr::Ident;

use crate::ir::{pl, sm};
use crate::semantic::Context;
use crate::WithErrorInfo;

pub fn compile_to_sm(context: Context, main_path: &[String]) -> Result<(sm::RootExpr, Context)> {
    // find main
    log::debug!("lookup for main pipeline in {main_path:?}");
    let (_, main_ident) = context.find_main_rel(main_path).map_err(|hint| {
        Error::new_simple("Missing main pipeline")
            .with_code("E0001")
            .with_hints(hint)
    })?;

    // find & validate query def
    // let def = context.find_query_def(&main_ident);
    // let def = def.cloned().unwrap_or_default();
    // validate query def

    let mut compiler = SmCompiler {
        context,
        exprs: Vec::new(),
    };

    let _root_eid = compiler.compile_decl_as_expr(main_ident)?;

    let root_expr = sm::RootExpr {
        exprs: compiler.exprs,
    };

    Ok((root_expr, compiler.context))
}

struct SmCompiler {
    context: Context,
    exprs: Vec<sm::Expr>,
}

impl SmCompiler {
    fn compile_decl_as_expr(&mut self, ident: Ident) -> Result<sm::EId> {
        let decl = self.context.root_mod.get(&ident).unwrap();

        let expr = (decl.kind.as_expr())
            .ok_or_else(|| Error::new_simple(format!("expected `{ident}` to be an expression")))?;

        self.compile_expr(*expr.clone())
    }

    fn compile_expr(&mut self, expr: pl::Expr) -> Result<sm::EId> {
        let kind = match expr.kind {
            pl::ExprKind::Ident(ident) => todo!("ident: {ident}"),
            pl::ExprKind::Literal(lit) => sm::ExprKind::Literal(lit),

            pl::ExprKind::Tuple(fields) => sm::ExprKind::Tuple(self.compile_exprs(fields)?),
            pl::ExprKind::Array(items) => sm::ExprKind::Array(self.compile_exprs(items)?),

            pl::ExprKind::RqOperator { name, args } => {
                let args = self.compile_exprs(args)?;
                sm::ExprKind::Operator { name, args }
            }

            pl::ExprKind::Param(param_id) => sm::ExprKind::Param(param_id),

            pl::ExprKind::Func(_) => todo!(),

            pl::ExprKind::TupleFields(_) => todo!(),
            pl::ExprKind::TupleExclude { .. } => todo!(),

            pl::ExprKind::SString(_) => todo!(),
            pl::ExprKind::Case(_) => todo!(),

            pl::ExprKind::TransformCall(_) => todo!("this pl::ExprKind should be removed"),

            pl::ExprKind::FuncCall(_)
            | pl::ExprKind::Type(_)
            | pl::ExprKind::Internal(_)
            | pl::ExprKind::FString(_) => {
                unreachable!()
            }
        };

        let expr = sm::Expr {
            kind,
            ty: expr.ty.expect("expression type to be resolved"),
            span: expr.span,
        };

        let eid = sm::EId::from(self.exprs.len() as u32);
        self.exprs.push(expr);

        Ok(eid)
    }

    fn compile_exprs(&mut self, exprs: Vec<pl::Expr>) -> Result<Vec<sm::EId>> {
        exprs.into_iter().map(|e| self.compile_expr(e)).collect()
    }
}
