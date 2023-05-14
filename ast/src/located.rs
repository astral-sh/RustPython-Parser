#![allow(clippy::derive_partial_eq_without_eq)]

use crate::source_code::{SourceLocation, SourceRange};
use thin_vec::ThinVec;

pub trait Located {
    fn range(&self) -> SourceRange;

    fn location(&self) -> SourceLocation {
        self.range().start
    }

    fn end_location(&self) -> Option<SourceLocation> {
        self.range().end
    }
}

pub type Suite = ThinVec<Stmt>;

pub use crate::builtin::*;
include!("gen/located.rs");
