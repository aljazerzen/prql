use std::collections::{HashMap, HashSet};

use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use prqlc_ast::{expr::Ident, Span};
use serde::{Deserialize, Serialize};

use crate::semantic::write_pl;

use super::pl;

/// Context of the pipeline.
#[derive(Default, Serialize, Deserialize, Clone)]
pub struct RootModule {
    /// Map of all accessible names (for each namespace)
    pub module: Module,

    pub span_map: HashMap<usize, Span>,
}

#[derive(Default, PartialEq, Serialize, Deserialize, Clone)]
pub struct Module {
    /// Names declared in this module. This is the important thing.
    pub names: HashMap<String, Decl>,

    /// List of relative paths to include in search path when doing lookup in
    /// this module.
    ///
    /// Assuming we want to lookup `average`, which is in `std`. The root module
    /// does not contain the `average`. So instead:
    /// - look for `average` in root module and find nothing,
    /// - follow redirects in root module,
    /// - because of redirect `std`, so we look for `average` in `std`,
    /// - there is `average` is `std`,
    /// - result of the lookup is FQ ident `std.average`.
    pub redirects: HashSet<Ident>,

    /// A declaration that has been shadowed (overwritten) by this module.
    pub shadowed: Option<Box<Decl>>,
}

/// A struct containing information about a single declaration.
#[derive(Debug, PartialEq, Default, Serialize, Deserialize, Clone)]
pub struct Decl {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub declared_at: Option<usize>,

    pub kind: DeclKind,

    /// Some declarations (like relation columns) have an order to them.
    /// 0 means that the order is irrelevant.
    #[serde(skip_serializing_if = "is_zero")]
    pub order: usize,

    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub annotations: Vec<pl::Annotation>,
}

/// The Declaration itself.
#[derive(Debug, PartialEq, Serialize, Deserialize, Clone, EnumAsInner)]
pub enum DeclKind {
    /// A nested namespace
    Module(Module),

    /// Nested namespaces that do lookup in layers from top to bottom, stopping at first match.
    LayeredModules(Vec<Module>),

    InstanceOf {
        table_fq: Ident,
        lineage: usize,
    },

    Column(pl::Ty),

    /// Contains a default value to be created in parent namespace when NS_INFER is matched.
    Infer(Box<DeclKind>),

    Expr(Box<pl::Expr>),

    Param(Box<pl::Ty>),

    QueryDef(pl::QueryDef),
}

#[derive(Debug, PartialEq, Serialize, Deserialize, Clone)]
pub struct TableDecl {
    /// This will always be `TyKind::Array(TyKind::Tuple)`.
    /// It is being preparing to be merged with [DeclKind::Expr].
    /// It used to keep track of columns.
    pub ty: Option<pl::Ty>,

    pub expr: TableExpr,
}

#[derive(Debug, PartialEq, Serialize, Deserialize, Clone, EnumAsInner)]
pub enum TableExpr {
    /// In SQL, this is a CTE
    RelationVar(Box<pl::Expr>),

    /// Actual table in a database. In SQL it can be referred to by name.
    LocalTable,

    /// No expression (this decl just tracks a relation literal).
    None,

    /// A placeholder for a relation that will be provided later.
    Param(String),
}

impl std::fmt::Debug for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ds = f.debug_struct("Module");

        if !self.redirects.is_empty() {
            let redirects = self.redirects.iter().map(|x| x.to_string()).collect_vec();
            ds.field("redirects", &redirects);
        }

        if self.names.len() < 15 {
            ds.field("names", &self.names);
        } else {
            ds.field("names", &format!("... {} entries ...", self.names.len()));
        }
        if let Some(shadowed) = &self.shadowed {
            ds.field("shadowed", shadowed);
        }
        ds.finish()
    }
}

impl Default for DeclKind {
    fn default() -> Self {
        DeclKind::Module(Module::default())
    }
}

impl std::fmt::Debug for RootModule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.module.fmt(f)
    }
}

impl From<DeclKind> for Decl {
    fn from(kind: DeclKind) -> Self {
        Decl {
            kind,
            declared_at: None,
            order: 0,
            annotations: Vec::new(),
        }
    }
}

impl std::fmt::Display for Decl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.kind, f)
    }
}

impl std::fmt::Display for DeclKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Module(arg0) => f.debug_tuple("Module").field(arg0).finish(),
            Self::LayeredModules(arg0) => f.debug_tuple("LayeredModules").field(arg0).finish(),
            Self::InstanceOf {
                table_fq: arg0,
                lineage: _,
            } => write!(f, "InstanceOf: {arg0}"),
            Self::Column(arg0) => write!(f, "Column (target {arg0})"),
            Self::Infer(arg0) => write!(f, "Infer (default: {arg0})"),
            Self::Expr(arg0) => write!(f, "Expr: {}", write_pl(*arg0.clone())),
            Self::Param(arg0) => write!(f, "Param: {arg0}"),
            Self::QueryDef(_) => write!(f, "QueryDef"),
        }
    }
}

fn is_zero(x: &usize) -> bool {
    *x == 0
}
