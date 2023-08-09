use enum_as_inner::EnumAsInner;
use prqlc_ast::expr::Literal;
use serde::{Deserialize, Serialize};

use prqlc_ast::Span;

pub use prqlc_ast::expr::{BinOp, UnOp};

use crate::ir::pl;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RootExpr {
    /// Vector of all expressions. Indexed by EId.
    /// Last item in the vector is the root expr.
    pub exprs: Vec<Expr>,
}

/// SM Expr Id
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EId(u32);

impl From<u32> for EId {
    fn from(id: u32) -> Self {
        EId(id)
    }
}

/// Expr is anything that has a value and thus a type.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Expr {
    pub kind: ExprKind,

    /// Type of the expression
    pub ty: pl::Ty,

    pub span: Option<Span>,
}

#[derive(Debug, Clone, Serialize, Deserialize, EnumAsInner, strum::AsRefStr)]
pub enum ExprKind {
    /// placeholder for a value provided later
    Param(String),

    /// A constant value, known at compile time
    Literal(Literal),

    /// Container type with a static number of fields.
    /// Fields don't have to have same type.
    Tuple(Vec<EId>),
    /// Container type with a dynamic number of items.
    /// All items must have same type.
    Array(Vec<EId>),

    Func {
        /// Expression containing parameter references.
        body: Box<Expr>,

        /// Positional function parameters.
        params: Vec<String>,
    },

    Operator {
        name: String,
        args: Vec<EId>,
    },
}
