use enum_as_inner::EnumAsInner;
use prqlc_ast::expr::Literal;
use serde::{Deserialize, Serialize};

use prqlc_ast::Span;

pub use prqlc_ast::expr::{BinOp, UnOp};

use crate::ir::pl;

/// Expr is anything that has a value and thus a type.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Expr {
    pub kind: ExprKind,

    /// Type of the expression
    pub ty: pl::Ty,

    pub span: Option<Span>,
}

#[derive(Debug, EnumAsInner, PartialEq, Clone, Serialize, Deserialize, strum::AsRefStr)]
pub enum ExprKind {
    /// placeholder for a value provided later
    Param(String),

    /// A constant value, known at compile time
    Literal(Literal),

    /// Container type with a static number of fields.
    /// Fields don't have to have same type.
    Tuple(Vec<Expr>),
    /// Container type with a dynamic number of items.
    /// All items must have same type.
    Array(Vec<Expr>),

    Func {
        /// Expression containing parameter references.
        body: Box<Expr>,

        /// Positional function parameters.
        params: Vec<String>,
    },

    Operator {
        name: String,
        args: Vec<Expr>,
    },
}
