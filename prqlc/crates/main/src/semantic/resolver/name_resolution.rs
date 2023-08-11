use anyhow::Result;
use itertools::Itertools;
use std::collections::HashSet;

use prqlc_ast::expr::Ident;

use crate::ir::decl::{Decl, DeclKind, Module, RootModule};
use crate::ir::pl::{Expr, ExprKind, Ty, TyKind, TyTuple};
use crate::semantic::{write_pl, NS_INFER, NS_INFER_MODULE, NS_SELF, NS_THIS};
use crate::{Error, WithErrorInfo};

use super::Resolver;

impl Resolver {
    pub fn resolve_ident(&mut self, ident: &Ident) -> Result<(Ty, ExprKind), Error> {
        let mut ident_parts = ident.iter();
        let first = ident_parts.next().unwrap();

        // find base module
        let (base, fq_ident) = find_lookup_base(
            &self.root_mod.module,
            self.current_module_path.iter().collect(),
            first,
        )?;

        // lookup each of the parts
        let mut base = base;
        let mut fq_ident = fq_ident;
        let mut indirections = Vec::new();
        for part in ident_parts {
            // convert current base into a lookup subject
            let subject = base.into_indirection_subject()?;

            // lookup and raise errors
            let results = subject.lookup(part);
            let result = raise_if_ambiguous(results)?;
            let (res, path) = result
                .ok_or_else(|| Error::new_simple(format!("unknown field or declaration {part}")))?;

            // save the result
            match subject {
                IndirectionSubject::Module(_) => fq_ident.extend(path.into_iter().cloned()),

                IndirectionSubject::Tuple(_) | IndirectionSubject::TupleToInfer => {
                    // tuple indirection cannot contain redirects
                    let part = path.into_iter().exactly_one().unwrap();
                    indirections.push(part.clone());
                }
            }

            // set base for the next lookup or the result
            base = res;
        }
        let fq_ident = Ident::from_path(fq_ident);

        // extract target type
        let res_ty = if base != IndirectionResult::ToInfer {
            base.into_ty()?
        } else {
            let ty_tuple = tuple_indirections_into_ty(&indirections);
            self.push_type_info(&fq_ident, ty_tuple);
            Ty {
                infer: true,
                ..Ty::new(TyKind::Any)
            }
        };

        // compose result
        let mut res = ExprKind::Ident(fq_ident);
        for name in indirections {
            res = ExprKind::Indirection {
                expr: Box::new(Expr::new(res)),
                name,
            };
        }

        Ok((res_ty, res))
    }
}

// Looks for an ident part relative to current module,
// then to parent, then grandparent until root.
fn find_lookup_base<'a>(
    root: &'a Module,
    mut current_path: Vec<&'a String>,
    name: &'a String,
) -> Result<(IndirectionResult<'a>, Vec<String>), Error> {
    let mut module_stack = root
        .lookup_module(&current_path)
        .expect("current path does not exist");

    while let Some(module) = module_stack.pop() {
        log::trace!("looking into {current_path:?}");

        let results = IndirectionSubject::Module(module).lookup(name);
        let result = raise_if_ambiguous(results)?;
        if let Some((res, path)) = result {
            current_path.extend(path);
            let path = current_path.into_iter().cloned().collect();

            return Ok((res, path));
        }

        current_path.pop();
    }

    log::debug!("{:#?}", root);
    Err(Error::new_simple(format!("unknown name {name}")))
}

/// A structure that supports indirection (a lookup by name).
#[derive(Clone, Copy)]
enum IndirectionSubject<'a> {
    Module(&'a Module),
    Tuple(&'a TyTuple),
    TupleToInfer,
}

#[derive(PartialEq)]
enum IndirectionResult<'a> {
    Decl(&'a Decl),
    Ty(Option<&'a Ty>),
    ToInfer,
}

impl<'a> IndirectionSubject<'a> {
    fn lookup(self, name: &'a String) -> Vec<(IndirectionResult<'a>, Vec<&String>)> {
        let mut res = Vec::new();

        match self {
            IndirectionSubject::Module(module) => {
                if let Some(decl) = module.names.get(name) {
                    res.push((IndirectionResult::Decl(decl), vec![name]));
                }

                for redirect in &module.redirects {
                    if let Some(red) = module.get(redirect) {
                        if let Ok(red) = IndirectionResult::Decl(red).into_indirection_subject() {
                            for (r, n) in red.lookup(name) {
                                let path = redirect.iter().chain(n.into_iter()).collect_vec();
                                res.push((r, path));
                            }
                        }
                    }
                }
            }
            IndirectionSubject::Tuple(ty_tuple) => {
                let field = if let Ok(index) = name.parse::<usize>() {
                    ty_tuple.fields.get(index)
                } else {
                    ty_tuple
                        .fields
                        .iter()
                        .find(|(n, _)| n.as_ref() == Some(name))
                };

                if let Some((_, ty)) = field {
                    res.push((IndirectionResult::Ty(ty.as_ref()), vec![name]))
                } else if ty_tuple.has_other {
                    res.push((IndirectionResult::ToInfer, vec![name]))
                }
            }
            IndirectionSubject::TupleToInfer => res.push((IndirectionResult::ToInfer, vec![name])),
        }
        res
    }
}

impl<'a> IndirectionResult<'a> {
    fn into_indirection_subject(self) -> Result<IndirectionSubject<'a>, Error> {
        match self {
            IndirectionResult::Decl(decl) => match &decl.kind {
                DeclKind::Module(module) => Ok(IndirectionSubject::Module(module)),
                DeclKind::Expr(expr) => {
                    IndirectionResult::Ty(expr.ty.as_ref()).into_indirection_subject()
                }
                DeclKind::Param(ty) => IndirectionResult::Ty(Some(ty)).into_indirection_subject(),
                k => Err(Error::new_simple(format!("cannot lookup into {k}"))),
            },

            IndirectionResult::Ty(Some(ty)) => {
                let a_tuple = Ty::new(TyKind::Tuple(TyTuple {
                    fields: Vec::new(),
                    has_other: true,
                }));

                if !ty.is_super_type_of(&a_tuple) {
                    return Err(Error::new_simple(format!("cannot lookup into {ty}")));
                }

                Ok(match &ty.kind {
                    TyKind::Tuple(tuple) => IndirectionSubject::Tuple(tuple),
                    _ => IndirectionSubject::TupleToInfer,
                })
            }
            IndirectionResult::Ty(None) => Err(Error::new_simple("cannot lookup unknown type")),
            IndirectionResult::ToInfer => Ok(IndirectionSubject::TupleToInfer),
        }
    }

    fn into_ty(self) -> Result<Ty, Error> {
        match self {
            IndirectionResult::Decl(decl) => match &decl.kind {
                DeclKind::Expr(expr) => {
                    let ty = expr.ty.as_ref().cloned();
                    let ty = ty.ok_or_else(|| {
                        Error::new_simple(format!("Unknown type of `{}`", write_pl(*expr.clone())))
                    })?;
                    Ok(ty)
                }

                DeclKind::Param(ty) => Ok(*ty.clone()),

                k => Err(Error::new_simple(format!(
                    "cannot reference {k} as a value"
                ))),
            },

            IndirectionResult::Ty(ty) => Ok(if let Some(x) = ty {
                x.clone()
            } else {
                Ty {
                    infer: true,
                    ..Ty::new(TyKind::Any)
                }
            }),

            IndirectionResult::ToInfer => unreachable!(),
        }
    }
}

impl RootModule {
    #[allow(dead_code)]
    pub(super) fn resolve_ident(&mut self, ident: &Ident) -> Result<Ident, Error> {
        // special case: wildcard
        if ident.name.contains('*') {
            if ident.name != "*" {
                return Err(Error::new_simple(
                    "Unsupported feature: advanced wildcard column matching",
                ));
            }
            return self.resolve_ident_wildcard(ident).map_err(|e| {
                log::debug!("{:#?}", self.module);
                Error::new_simple(e)
            });
        }

        // base case: direct lookup
        let decls = lookup(&self.module, ident);
        match decls.len() {
            // no match: try match *
            0 => {}

            // single match, great!
            1 => return Ok(decls.into_iter().next().unwrap()),

            // ambiguous
            _ => return Err(ambiguous_error(decls, None)),
        }

        let ident = ident.clone();

        // fallback case: try to match with NS_INFER and infer the declaration from the original ident.
        match self.resolve_ident_fallback(ident, NS_INFER) {
            // The declaration and all needed parent modules were created
            // -> just return the fq ident
            Ok(inferred_ident) => Ok(inferred_ident),

            // Was not able to infer.
            Err(None) => Err(Error::new_simple("Unknown name".to_string())),
            Err(Some(msg)) => Err(msg),
        }
    }

    /// Try lookup of the ident with name replaced. If unsuccessful, recursively retry parent ident.
    fn resolve_ident_fallback(
        &mut self,
        ident: Ident,
        name_replacement: &'static str,
    ) -> Result<Ident, Option<Error>> {
        let infer_ident = ident.clone().with_name(name_replacement);

        // lookup of infer_ident
        let mut decls = lookup(&self.module, &infer_ident);

        if decls.is_empty() {
            if let Some(parent) = infer_ident.clone().pop() {
                // try to infer parent
                let _ = self.resolve_ident_fallback(parent, NS_INFER_MODULE)?;

                // module was successfully inferred, retry the lookup
                decls = lookup(&self.module, &infer_ident)
            }
        }

        match decls.len() {
            1 => {
                // single match, great!
                let infer_ident = decls.into_iter().next().unwrap();
                self.infer_decl(infer_ident, &ident)
                    .map_err(|x| Some(Error::new_simple(x)))
            }
            0 => Err(None),
            _ => Err(Some(ambiguous_error(decls, Some(&ident.name)))),
        }
    }

    /// Create a declaration of [original] from template provided by declaration of [infer_ident].
    fn infer_decl(&mut self, infer_ident: Ident, original: &Ident) -> Result<Ident, String> {
        let infer = self.module.get(&infer_ident).unwrap();
        let mut infer_default = *infer.kind.as_infer().cloned().unwrap();

        if let DeclKind::Module(new_module) = &mut infer_default {
            // Modules are inferred only for database inference.
            // Because we want to infer database modules that nested arbitrarily deep,
            // we cannot store the template in DeclKind::Infer, but we override it here.
            *new_module = Module::new_database();
        }

        let module_ident = infer_ident.pop().unwrap();
        let module = self.module.get_mut(&module_ident).unwrap();
        let module = module.kind.as_module_mut().unwrap();

        // insert default
        module
            .names
            .insert(original.name.clone(), Decl::from(infer_default));

        // infer table columns
        if let Some(decl) = module.names.get(NS_SELF).cloned() {
            if let DeclKind::InstanceOf { table_fq, .. } = decl.kind {
                log::debug!("inferring {original} to be from table {table_fq}");
                self.infer_table_column(&table_fq, &original.name)?;
            }
        }

        Ok(module_ident + Ident::from_name(original.name.clone()))
    }

    fn resolve_ident_wildcard(&mut self, ident: &Ident) -> Result<Ident, String> {
        let mod_ident = self.find_module_of_wildcard(ident)?;
        let mod_decl = self.module.get(&mod_ident).unwrap();

        let (instance_of, _) = mod_decl.kind.as_instance_of().unwrap();
        let decl = self.module.get(instance_of).unwrap();
        let decl = decl.kind.as_expr().unwrap();

        let tuple = decl.ty.as_ref().unwrap().as_relation().unwrap();

        let fields = tuple
            .fields
            .iter()
            .flat_map(|(name, _)| match name {
                None => None,
                Some(name) => Some(Expr::new(mod_ident.clone() + Ident::from_name(name))),
            })
            .collect_vec();

        // This a clever way of returning an arbitrary Expr from this function.
        // We wrap the expr into DeclKind::Expr and save it into context.
        let tuple_with_all_cols = Expr::new(ExprKind::TupleFields(fields));

        let cols_expr = DeclKind::Expr(Box::new(tuple_with_all_cols));
        let save_as = "_wildcard_match";
        self.module
            .names
            .insert(save_as.to_string(), cols_expr.into());

        // Then we can return ident to that decl.
        Ok(Ident::from_name(save_as))
    }

    fn find_module_of_wildcard(&self, wildcard_ident: &Ident) -> Result<Ident, String> {
        let mod_ident = wildcard_ident.clone().pop().unwrap() + Ident::from_name(NS_SELF);

        let fq_mod_idents = lookup(&self.module, &mod_ident);

        // TODO: gracefully handle this
        Ok(fq_mod_idents.into_iter().exactly_one().unwrap())
    }

    fn infer_table_column(&mut self, table_ident: &Ident, col_name: &str) -> Result<(), String> {
        let table = self.module.get_mut(table_ident).unwrap();
        let table_decl = table.kind.as_expr_mut().unwrap();

        let Some(ty_tuple) = table_decl.ty.as_mut().and_then(|t| t.as_relation_mut()) else {
            return Err(format!("Variable {table_ident:?} is not a relation."));
        };

        if !ty_tuple.has_other {
            return Err(format!("Table {table_ident:?} does not have wildcard."));
        };

        let exists = ty_tuple.fields.iter().any(|(name, _)| match name {
            Some(n) => n == col_name,
            _ => false,
        });
        if exists {
            return Ok(());
        }

        let ty = Some(Ty::new(TyKind::Any));
        ty_tuple.fields.push((Some(col_name.to_string()), ty));

        // also add into input tables of this table expression
        if let Some(ty) = &table_decl.ty {
            if let Some(tuple) = ty.as_relation() {
                if tuple.has_other {
                    todo!("column inference")
                    // let (wildcard_ty, _) = wildcard_inputs.into_iter().next().unwrap();
                    // let wildcard_ty = wildcard_ty.as_ref().unwrap();
                    // let table_fq = wildcard_ty.instance_of.clone().unwrap();

                    // self.infer_table_column(&table_fq, col_name)?;
                }
            }
        }

        Ok(())
    }
}

fn lookup(module: &Module, ident: &Ident) -> HashSet<Ident> {
    log::trace!("lookup: {ident}");

    let mut res = HashSet::new();

    res.extend(lookup_in(module, ident.clone()));

    for redirect in &module.redirects {
        log::trace!("... following redirect {redirect}");
        let r = lookup_in(module, redirect.clone() + ident.clone());
        log::trace!("... result of redirect {redirect}: {r:?}");
        res.extend(r);
    }
    res
}

fn lookup_in(module: &Module, ident: Ident) -> HashSet<Ident> {
    let (prefix, ident) = ident.pop_front();

    if let Some(ident) = ident {
        if let Some(entry) = module.names.get(&prefix) {
            let redirected = match &entry.kind {
                DeclKind::Module(ns) => lookup(ns, &ident),
                DeclKind::LayeredModules(stack) => {
                    let mut r = HashSet::new();
                    for ns in stack.iter().rev() {
                        r = lookup(ns, &ident);

                        if !r.is_empty() {
                            break;
                        }
                    }
                    r
                }
                _ => HashSet::new(),
            };

            return redirected
                .into_iter()
                .map(|i| Ident::from_name(&prefix) + i)
                .collect();
        }
    } else if let Some(decl) = module.names.get(&prefix) {
        if let DeclKind::Module(inner) = &decl.kind {
            if inner.names.contains_key(NS_SELF) {
                return HashSet::from([Ident::from_path(vec![prefix, NS_SELF.to_string()])]);
            }
        }

        return HashSet::from([Ident::from_name(prefix)]);
    }
    HashSet::new()
}

fn raise_if_ambiguous<'a, 'b>(
    results: Vec<(IndirectionResult<'a>, Vec<&'b String>)>,
) -> Result<Option<(IndirectionResult<'a>, Vec<&'b String>)>, Error> {
    if results.len() <= 1 {
        return Ok(results.into_iter().next());
    }

    let idents = results
        .iter()
        .map(|(_, path)| Ident::from_path(path.clone()))
        .collect::<HashSet<_>>();

    if idents.len() <= 1 {
        return Ok(results.into_iter().next());
    }

    Err(ambiguous_error(idents, None))
}

fn ambiguous_error(idents: HashSet<Ident>, replace_name: Option<&String>) -> Error {
    let all_this = idents.iter().all(|d| d.starts_with_part(NS_THIS));

    let mut chunks = Vec::new();
    for mut ident in idents {
        if all_this {
            let (_, rem) = ident.pop_front();
            if let Some(rem) = rem {
                ident = rem;
            } else {
                continue;
            }
        }

        if let Some(name) = replace_name {
            ident.name = name.clone();
        }
        chunks.push(ident.to_string());
    }
    chunks.sort();
    let hint = format!("could be any of: {}", chunks.join(", "));
    Error::new_simple("Ambiguous name").push_hint(hint)
}

/// Given indirection steps that were taken into a tuple,
/// constructs a tuple type that would support such steps.
fn tuple_indirections_into_ty(indirections: &Vec<String>) -> Ty {
    let mut base = Ty::new(TyKind::Any);
    let mut current = &mut base;
    for indirection in indirections {
        let new_ty = Ty {
            infer: true,
            ..Ty::new(TyKind::Any)
        };
        current.kind = TyKind::Tuple(TyTuple {
            fields: vec![(Some(indirection.clone()), Some(new_ty))],
            has_other: true,
        });
        let the_new_tuple = current.kind.as_tuple_mut().unwrap();
        let the_new_field = the_new_tuple.fields.last_mut().unwrap();
        current = the_new_field.1.as_mut().unwrap();
    }

    base.infer = true;
    base
}
#[cfg(test)]
mod tests {
    use prqlc_ast::expr::Literal;

    use super::*;

    // TODO: tests / docstrings for `stack_pop` & `stack_push` & `insert_frame`
    #[test]
    fn test_module() {
        let mut module = Module::default();

        let ident = Ident::from_name("test_name");
        let expr: Expr = Expr::new(ExprKind::Literal(Literal::Integer(42)));
        let decl: Decl = DeclKind::Expr(Box::new(expr)).into();

        assert!(module.insert(ident.clone(), decl.clone()).is_ok());
        assert_eq!(module.get(&ident).unwrap(), &decl);
        assert_eq!(module.get_mut(&ident).unwrap(), &decl);

        // Lookup
        let lookup_result = lookup(&module, &ident);
        assert_eq!(lookup_result.len(), 1);
        assert!(lookup_result.contains(&ident));
    }
}
