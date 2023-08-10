use std::collections::HashMap;

use anyhow::Result;
use prqlc_ast::stmt::QueryDef;

use crate::ir::decl::*;
use crate::ir::pl::{Annotation, Expr, Ident, Ty, TyKind, TyTuple};
use crate::Error;

use super::{
    NS_DEFAULT_DB, NS_INFER, NS_INFER_MODULE, NS_MAIN, NS_PARAM, NS_QUERY_DEF, NS_SELF, NS_STD,
    NS_THAT, NS_THIS,
};

impl Module {
    pub fn singleton<S: ToString>(name: S, entry: Decl) -> Module {
        Module {
            names: HashMap::from([(name.to_string(), entry)]),
            ..Default::default()
        }
    }

    pub fn new_root() -> Module {
        // Each module starts with a default namespace that contains a wildcard
        // and the standard library.
        Module {
            names: HashMap::from([
                (
                    NS_DEFAULT_DB.to_string(),
                    Decl::from(DeclKind::Module(Self::new_database())),
                ),
                (NS_STD.to_string(), Decl::from(DeclKind::default())),
            ]),
            shadowed: None,
            redirects: [
                Ident::from_name(NS_THIS),
                Ident::from_name(NS_THAT),
                Ident::from_name(NS_PARAM),
                Ident::from_name(NS_STD),
            ]
            .into(),
        }
    }

    pub fn new_database() -> Module {
        let mut col_ty = Ty::new(TyKind::Any);
        col_ty.infer = true;

        let table_ty = Ty::relation(TyTuple {
            fields: Vec::new(),
            has_other: true,
        });

        let names = HashMap::from([
            (
                NS_INFER.to_string(),
                Decl::from(DeclKind::Infer(Box::new(DeclKind::Expr(Box::new(Expr {
                    ty: Some(table_ty),
                    ..Expr::new(Ident::from_name(NS_INFER))
                }))))),
            ),
            (
                NS_INFER_MODULE.to_string(),
                Decl::from(DeclKind::Infer(Box::new(DeclKind::Module(Module {
                    names: HashMap::new(),
                    redirects: [].into(),
                    shadowed: None,
                })))),
            ),
        ]);
        Module {
            names,
            shadowed: None,
            redirects: [].into(),
        }
    }

    pub fn insert(&mut self, fq_ident: Ident, decl: Decl) -> Result<Option<Decl>, Error> {
        if fq_ident.path.is_empty() {
            Ok(self.names.insert(fq_ident.name, decl))
        } else {
            let (top_level, remaining) = fq_ident.pop_front();
            let entry = self.names.entry(top_level).or_default();

            if let DeclKind::Module(inner) = &mut entry.kind {
                inner.insert(remaining.unwrap(), decl)
            } else {
                Err(Error::new_simple(
                    "path does not resolve to a module or a table",
                ))
            }
        }
    }

    pub fn get_mut(&mut self, ident: &Ident) -> Option<&mut Decl> {
        let mut ns = self;

        for part in &ident.path {
            let entry = ns.names.get_mut(part);

            match entry {
                Some(Decl {
                    kind: DeclKind::Module(inner),
                    ..
                }) => {
                    ns = inner;
                }
                _ => return None,
            }
        }

        ns.names.get_mut(&ident.name)
    }

    /// Get namespace entry using a fully qualified ident.
    pub fn get(&self, fq_ident: &Ident) -> Option<&Decl> {
        let mut ns = self;

        for (index, part) in fq_ident.path.iter().enumerate() {
            let decl = ns.names.get(part);
            if let Some(decl) = decl {
                match &decl.kind {
                    DeclKind::Module(inner) => {
                        ns = inner;
                    }
                    DeclKind::LayeredModules(stack) => {
                        let next = fq_ident.path.get(index + 1).unwrap_or(&fq_ident.name);
                        let mut found = false;
                        for n in stack.iter().rev() {
                            if n.names.contains_key(next) {
                                ns = n;
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            return None;
                        }
                    }
                    _ => return None,
                }
            } else {
                return None;
            }
        }

        ns.names.get(&fq_ident.name)
    }

    pub(super) fn insert_relation(&mut self, expr: &Expr, namespace: &str) {
        let ty = expr.ty.as_ref().unwrap();
        let tuple = ty.kind.as_array().unwrap();

        self.insert_ty(namespace.to_string(), tuple, 0);
    }

    /// Creates a name resolution declaration that allows lookups into the given type.
    fn insert_ty(&mut self, name: String, ty: &Ty, order: usize) {
        log::debug!("inserting `{name}`: {ty}");

        let decl_kind = match &ty.kind {
            // for tuples, create a submodule
            TyKind::Tuple(tuple) => {
                let mut sub_mod = Module::default();

                if let Some(instance_of) = &ty.instance_of {
                    let lineage = ty.lineage.unwrap();

                    let self_decl = Decl {
                        declared_at: None,
                        kind: DeclKind::InstanceOf {
                            table_fq: instance_of.clone(),
                            lineage,
                        },
                        ..Default::default()
                    };
                    sub_mod.names.insert(NS_SELF.to_string(), self_decl);
                }

                for (index, (name, ty)) in tuple.fields.iter().enumerate() {
                    if let Some(name) = name {
                        sub_mod.insert_ty(name.clone(), ty.as_ref().unwrap(), index + 1);
                    } else {
                        // unnamed tuple fields cannot be references,
                        // so there is no point of having them in the module
                    }
                }
                if tuple.has_other {
                    let field_ty = Ty {
                        lineage: ty.lineage,
                        ..Ty::new(TyKind::Any)
                    };

                    let decl_kind = DeclKind::Infer(Box::new(DeclKind::Column(field_ty)));

                    let mut decl = Decl::from(decl_kind);
                    decl.order = tuple.fields.len() + 1;
                    sub_mod.names.insert(NS_INFER.to_string(), decl);
                }

                self.redirects.insert(Ident::from_name(&name));
                DeclKind::Module(sub_mod)
            }

            // for anything else, create a plain column
            _ => DeclKind::Column(ty.clone()),
        };

        let mut decl = Decl::from(decl_kind);
        decl.order = order;
        self.names.insert(name, decl);
    }

    pub fn shadow(&mut self, ident: &str) {
        let shadowed = self.names.remove(ident).map(Box::new);
        let entry = DeclKind::Module(Module {
            shadowed,
            ..Default::default()
        });
        self.names.insert(ident.to_string(), entry.into());
    }

    pub fn unshadow(&mut self, ident: &str) {
        if let Some(entry) = self.names.remove(ident) {
            let ns = entry.kind.into_module().unwrap();

            if let Some(shadowed) = ns.shadowed {
                self.names.insert(ident.to_string(), *shadowed);
            }
        }
    }

    pub fn stack_push(&mut self, ident: &str, namespace: Module) {
        let entry = self
            .names
            .entry(ident.to_string())
            .or_insert_with(|| DeclKind::LayeredModules(Vec::new()).into());
        let stack = entry.kind.as_layered_modules_mut().unwrap();

        stack.push(namespace);
    }

    pub fn stack_pop(&mut self, ident: &str) -> Option<Module> {
        (self.names.get_mut(ident))
            .and_then(|e| e.kind.as_layered_modules_mut())
            .and_then(|stack| stack.pop())
    }

    pub(crate) fn into_exprs(self) -> HashMap<String, Expr> {
        self.names
            .into_iter()
            .map(|(k, v)| (k, *v.kind.into_expr().unwrap()))
            .collect()
    }

    pub(crate) fn from_exprs(exprs: HashMap<String, Expr>) -> Module {
        Module {
            names: exprs
                .into_iter()
                .map(|(key, expr)| {
                    let decl = Decl {
                        kind: DeclKind::Expr(Box::new(expr)),
                        ..Default::default()
                    };
                    (key, decl)
                })
                .collect(),
            ..Default::default()
        }
    }

    pub fn as_decls(&self) -> Vec<(Ident, &Decl)> {
        let mut r = Vec::new();
        for (name, decl) in &self.names {
            match &decl.kind {
                DeclKind::Module(module) => r.extend(
                    module
                        .as_decls()
                        .into_iter()
                        .map(|(inner, decl)| (Ident::from_name(name) + inner, decl)),
                ),
                _ => r.push((Ident::from_name(name), decl)),
            }
        }
        r
    }

    /// Recursively finds all declarations that end in suffix.
    pub fn find_by_suffix(&self, suffix: &str) -> Vec<Ident> {
        let mut res = Vec::new();

        for (name, decl) in &self.names {
            if let DeclKind::Module(module) = &decl.kind {
                let nested = module.find_by_suffix(suffix);
                res.extend(nested.into_iter().map(|x| x.prepend(vec![name.clone()])));
                continue;
            }

            if name == suffix {
                res.push(Ident::from_name(name));
            }
        }

        res
    }
}

impl RootModule {
    pub(super) fn declare(
        &mut self,
        ident: Ident,
        decl: DeclKind,
        id: Option<usize>,
        annotations: Vec<Annotation>,
    ) -> Result<()> {
        let existing = self.module.get(&ident);
        if existing.is_some() {
            return Err(Error::new_simple(format!("duplicate declarations of {ident}")).into());
        }

        let decl = Decl {
            kind: decl,
            declared_at: id,
            order: 0,
            annotations,
        };
        self.module.insert(ident, decl).unwrap();
        Ok(())
    }

    /// Finds that main pipeline given a path to either main itself or its parent module.
    /// Returns main expr and fq ident of the decl.
    pub fn find_main_rel(&self, path: &[String]) -> Result<(&Expr, Ident), Option<String>> {
        let (decl, ident) = self.find_main(path)?;

        let decl = (decl.kind.as_expr()).ok_or(Some(format!("{ident} is not an expression")))?;

        Ok((decl, ident))
    }

    pub fn find_main(&self, path: &[String]) -> Result<(&Decl, Ident), Option<String>> {
        let mut tried_idents = Vec::new();

        // is path referencing the relational var directly?
        if !path.is_empty() {
            let ident = Ident::from_path(path.to_vec());
            let decl = self.module.get(&ident);

            if let Some(decl) = decl {
                return Ok((decl, ident));
            } else {
                tried_idents.push(ident.to_string());
            }
        }

        // is path referencing the parent module?
        {
            let mut path = path.to_vec();
            path.push(NS_MAIN.to_string());

            let ident = Ident::from_path(path);
            let decl = self.module.get(&ident);

            if let Some(decl) = decl {
                return Ok((decl, ident));
            } else {
                tried_idents.push(ident.to_string());
            }
        }

        Err(Some(format!(
            "Expected a declaration at {}",
            tried_idents.join(" or ")
        )))
    }

    pub fn find_query_def(&self, main: &Ident) -> Option<&QueryDef> {
        let ident = Ident {
            path: main.path.clone(),
            name: NS_QUERY_DEF.to_string(),
        };

        let decl = self.module.get(&ident)?;
        decl.kind.as_query_def()
    }

    /// Finds all main pipelines.
    pub fn find_mains(&self) -> Vec<Ident> {
        self.module.find_by_suffix(NS_MAIN)
    }

    pub(super) fn find_std_type(&self, name: &str) -> Ty {
        let ident = Ident::from_path(vec![NS_STD, name]);
        let decl = self.module.get(&ident).unwrap().kind.as_expr().unwrap();
        decl.kind.as_type().unwrap().clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::pl::{Expr, ExprKind, Literal};

    #[test]
    fn test_module_shadow_unshadow() {
        let mut module = Module::default();

        let ident = Ident::from_name("test_name");
        let expr: Expr = Expr::new(ExprKind::Literal(Literal::Integer(42)));
        let decl: Decl = DeclKind::Expr(Box::new(expr)).into();

        module.insert(ident.clone(), decl.clone()).unwrap();

        module.shadow("test_name");
        assert!(module.get(&ident) != Some(&decl));

        module.unshadow("test_name");
        assert_eq!(module.get(&ident).unwrap(), &decl);
    }
}
