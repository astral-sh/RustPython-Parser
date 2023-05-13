use crate::{Constant, Excepthandler, Expr, Pattern, Stmt};
use static_assertions::const_assert_eq;

impl<R> Expr<R> {
    /// Returns a short name for the node suitable for use in error messages.
    pub fn python_name(&self) -> &'static str {
        match self {
            Expr::BoolOp { .. } | Expr::BinOp { .. } | Expr::UnaryOp { .. } => "operator",
            Expr::Subscript { .. } => "subscript",
            Expr::Await { .. } => "await expression",
            Expr::Yield { .. } | Expr::YieldFrom { .. } => "yield expression",
            Expr::Compare { .. } => "comparison",
            Expr::Attribute { .. } => "attribute",
            Expr::Call { .. } => "function call",
            Expr::Constant(crate::ExprConstant { value, .. }) => match value {
                Constant::Str(_)
                | Constant::Int(_)
                | Constant::Float(_)
                | Constant::Complex { .. }
                | Constant::Bytes(_) => "literal",
                Constant::Tuple(_) => "tuple",
                Constant::Bool(b) => {
                    if *b {
                        "True"
                    } else {
                        "False"
                    }
                }
                Constant::None => "None",
                Constant::Ellipsis => "ellipsis",
            },
            Expr::List { .. } => "list",
            Expr::Tuple { .. } => "tuple",
            Expr::Dict { .. } => "dict display",
            Expr::Set { .. } => "set display",
            Expr::ListComp { .. } => "list comprehension",
            Expr::DictComp { .. } => "dict comprehension",
            Expr::SetComp { .. } => "set comprehension",
            Expr::GeneratorExp { .. } => "generator expression",
            Expr::Starred { .. } => "starred",
            Expr::Slice { .. } => "slice",
            Expr::JoinedStr(crate::ExprJoinedStr { values, .. }) => {
                if values.iter().any(|e| e.is_joined_str_expr()) {
                    "f-string expression"
                } else {
                    "literal"
                }
            }
            Expr::FormattedValue { .. } => "f-string expression",
            Expr::Name { .. } => "name",
            Expr::Lambda { .. } => "lambda",
            Expr::IfExp { .. } => "conditional expression",
            Expr::NamedExpr { .. } => "named expression",
        }
    }
}

#[cfg(target_arch = "x86_64")]
const_assert_eq!(std::mem::size_of::<Expr>(), 72);
#[cfg(target_arch = "x86_64")]
const_assert_eq!(std::mem::size_of::<Stmt>(), 136);
#[cfg(target_arch = "x86_64")]
const_assert_eq!(std::mem::size_of::<Pattern>(), 96);
#[cfg(target_arch = "x86_64")]
const_assert_eq!(std::mem::size_of::<Excepthandler>(), 64);
