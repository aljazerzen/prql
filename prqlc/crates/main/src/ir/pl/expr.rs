use std::collections::{HashMap, HashSet};

use enum_as_inner::EnumAsInner;
use prqlc_ast::expr::{Ident, Literal};
use serde::{Deserialize, Serialize};

use prqlc_ast::expr::generic;
use prqlc_ast::Span;

pub use prqlc_ast::expr::{BinOp, UnOp};

use super::{TransformCall, Ty, TyOrExpr};

// The following code is tested by the tests_misc crate to match expr.rs in prql_ast.

/// Expr is anything that has a value and thus a type.
/// If it cannot contain nested Exprs, is should be under [ExprKind::Literal].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Expr {
    #[serde(flatten)]
    pub kind: ExprKind,

    #[serde(skip)]
    pub span: Option<Span>,

    #[serde(skip_serializing_if = "Option::is_none")]
    pub alias: Option<String>,

    /// Unique identificator of the node. Set exactly once during semantic::resolve.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<usize>,

    /// For [Ident]s, this is id of node referenced by the ident
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_id: Option<usize>,

    /// Type of expression this node represents.
    /// [None] means that type should be inferred.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ty: Option<Ty>,

    #[serde(skip)]
    pub needs_window: bool,
}

#[derive(Debug, EnumAsInner, PartialEq, Clone, Serialize, Deserialize, strum::AsRefStr)]
pub enum ExprKind {
    Ident(Ident),
    Literal(Literal),

    /// Container type with a static number of fields.
    /// Fields don't have to have same type.
    Tuple(Vec<Expr>),
    /// Container type with a dynamic number of items.
    /// All items must have same type.
    Array(Vec<Expr>),

    FuncCall(FuncCall),
    Func(Box<Func>),
    TransformCall(TransformCall),
    SString(Vec<InterpolateItem>),
    FString(Vec<InterpolateItem>),
    Case(Vec<SwitchCase>),
    RqOperator {
        name: String,
        args: Vec<Expr>,
    },

    Type(Ty),

    /// placeholder for values provided after query is compiled
    Param(String),

    /// When used instead of function body, the function will be translated to a RQ operator.
    /// Contains ident of the RQ operator.
    Internal(String),

    /// Tuple fields, compounded together into an Expr, except actually being a tuple.
    /// Syntactically, this would be `a, b, c` (a tuple without braces).
    ///
    /// Can only be used inside a tuple, where it will be evaluated to fields of that tuple.
    ///
    /// Example:
    /// ```yaml
    /// Tuple:
    /// - a
    /// - TupleFields:
    ///   - b
    ///   - c
    /// - d
    /// ```
    /// ... would be equivalent to:
    /// ```yaml
    /// Tuple:
    /// - a
    /// - b
    /// - c
    /// - d
    /// ```
    TupleFields(Vec<Expr>),

    /// An indirection (field access), but instead of selecting mentioned fields,
    /// selecting all unmentioned fields and as TupleFields.
    TupleExclude {
        expr: Box<Expr>,

        /// Set of relative field identifiers that should be excluded.
        /// Relative to the expr.
        exclude: HashSet<Ident>,
    },
}

/// Function call.
#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
pub struct FuncCall {
    pub name: Box<Expr>,
    pub args: Vec<Expr>,
    #[serde(default, skip_serializing_if = "HashMap::is_empty")]
    pub named_args: HashMap<String, Expr>,
}

/// Function called with possibly missing positional arguments.
/// May also contain environment that is needed to evaluate the body.
#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
pub struct Func {
    /// Name of the function. Used for user-facing messages only.
    pub name_hint: Option<Ident>,

    /// Type requirement for the function body expression.
    pub return_ty: Option<TyOrExpr>,

    /// Expression containing parameter (and environment) references.
    pub body: Box<Expr>,

    /// Positional function parameters.
    pub params: Vec<FuncParam>,

    /// Named function parameters.
    pub named_params: Vec<FuncParam>,

    /// Arguments that have already been provided.
    pub args: Vec<Expr>,

    /// Additional variables that the body of the function may need to be
    /// evaluated.
    pub env: HashMap<String, Expr>,
}

#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
pub struct FuncParam {
    pub name: String,

    #[serde(skip_serializing_if = "Option::is_none")]
    pub ty: Option<TyOrExpr>,

    pub default_value: Option<Box<Expr>>,

    pub implicit_closure: Option<Vec<String>>
}

pub type Range = generic::Range<Box<Expr>>;
pub type InterpolateItem = generic::InterpolateItem<Expr>;
pub type SwitchCase = generic::SwitchCase<Box<Expr>>;

impl Func {
    pub(crate) fn as_debug_name(&self) -> &str {
        let ident = self.name_hint.as_ref();

        ident.map(|n| n.name.as_str()).unwrap_or("<anonymous>")
    }
}
