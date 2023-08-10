use anyhow::Result;
use std::collections::HashMap;

use crate::ir::decl::{Decl, DeclKind, Module};
use crate::ir::pl::*;
use crate::{Error, WithErrorInfo};

use super::{Resolver, NS_STD};

impl Resolver {
    // entry point to the resolver
    pub fn fold_statements(&mut self, stmts: Vec<Stmt>) -> Result<()> {
        for mut stmt in stmts {
            stmt.id = Some(self.id.gen());
            if let Some(span) = stmt.span {
                self.root_mod.span_map.insert(stmt.id.unwrap(), span);
            }

            let ident = Ident {
                path: self.current_module_path.clone(),
                name: stmt.name().to_string(),
            };

            let stmt_name = stmt.name().to_string();

            let mut def = match stmt.kind {
                StmtKind::QueryDef(d) => {
                    let decl = DeclKind::QueryDef(*d);
                    self.root_mod
                        .declare(ident, decl, stmt.id, Vec::new())
                        .with_span(stmt.span)?;
                    continue;
                }
                StmtKind::VarDef(var_def) => self.fold_var_def(var_def)?,
                StmtKind::TypeDef(ty_def) => {
                    let mut value = if let Some(value) = ty_def.value {
                        value
                    } else {
                        Box::new(Expr::new(Literal::Null))
                    };

                    // This is a hacky way to provide values to std.int and friends.
                    if self.current_module_path == vec![NS_STD] {
                        if let Some(kind) = get_stdlib_decl(&ident.name) {
                            value.kind = kind;
                        }
                    }

                    let mut ty = self.fold_type_expr(Some(value))?.unwrap();
                    ty.name = Some(ident.name.clone());

                    VarDef {
                        name: ty_def.name,
                        value: Box::new(Expr {
                            ty: Some(Ty::new(TyKind::Set)),
                            ..Expr::new(ExprKind::Type(ty))
                        }),
                        ty_expr: None,
                        kind: VarDefKind::Let,
                    }
                }
                StmtKind::ModuleDef(module_def) => {
                    if !self.options.allow_module_decls {
                        return Err(Error::new_simple(
                            "explicit module declarations are not allowed",
                        )
                        .with_span(stmt.span)
                        .into());
                    }

                    self.current_module_path.push(ident.name);

                    let decl = Decl {
                        declared_at: stmt.id,
                        kind: DeclKind::Module(Module {
                            names: HashMap::new(),
                            redirects: [].into(),
                            shadowed: None,
                        }),
                        ..Default::default()
                    };
                    let ident = Ident::from_path(self.current_module_path.clone());
                    self.root_mod
                        .module
                        .insert(ident, decl)
                        .with_span(stmt.span)?;

                    self.fold_statements(module_def.stmts)?;
                    self.current_module_path.pop();
                    continue;
                }
            };

            if let VarDefKind::Main = def.kind {
                def.ty_expr = Some(Box::new(Expr::new(ExprKind::Ident(Ident::from_path(
                    vec!["std", "relation"],
                )))));
            }

            if let ExprKind::Func(closure) = &mut def.value.kind {
                if closure.name_hint.is_none() {
                    closure.name_hint = Some(ident.clone());
                }
            }

            let expected_ty = self.fold_type_expr(def.ty_expr)?;
            if expected_ty.is_some() {
                let who = || Some(stmt_name.clone());
                self.validate_expr_type(&mut def.value, expected_ty.as_ref(), &who)?;
            }

            let decl = prepare_expr_decl(def.value);

            self.root_mod
                .declare(ident, decl, stmt.id, stmt.annotations)
                .with_span(stmt.span)?;
        }
        Ok(())
    }
}

pub(super) fn prepare_expr_decl(value: Box<Expr>) -> DeclKind {
    match &value.ty {
        Some(ty) if ty.is_relation() => {
            let mut ty = ty.clone();
            ty.flatten_tuples();

            let mut value = value;
            value.ty = Some(ty);

            DeclKind::Expr(value)
        }
        _ => DeclKind::Expr(value),
    }
}

fn get_stdlib_decl(name: &str) -> Option<ExprKind> {
    let set = match name {
        "int" => Ty::new(PrimitiveSet::Int),
        "float" => Ty::new(PrimitiveSet::Float),
        "bool" => Ty::new(PrimitiveSet::Bool),
        "text" => Ty::new(PrimitiveSet::Text),
        "date" => Ty::new(PrimitiveSet::Date),
        "time" => Ty::new(PrimitiveSet::Time),
        "timestamp" => Ty::new(PrimitiveSet::Timestamp),
        "func" => Ty::new(TyKind::Function(None)),
        "any" => Ty::new(TyKind::Any),
        _ => return None,
    };
    Some(ExprKind::Type(set))
}
