use crate::text_size::{TextRange, TextSize};

pub use crate::builtin::*;

pub trait Ranged {
    fn range(&self) -> TextRange;

    fn start(&self) -> TextSize {
        self.range().start()
    }

    fn end(&self) -> TextSize {
        self.range().end()
    }
}

impl<T> Ranged for &T
where
    T: Ranged,
{
    fn range(&self) -> TextRange {
        self.range()
    }
}

include!("gen/ranged.rs");
