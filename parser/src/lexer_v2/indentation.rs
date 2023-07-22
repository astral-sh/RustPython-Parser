use static_assertions::assert_eq_size;
use std::cmp::Ordering;
use std::fmt::Debug;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Default)]
pub(super) struct Column(u32);

impl Column {
    pub(super) const fn new(column: u32) -> Self {
        Self(column)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Default)]
pub(super) struct Character(u32);

impl Character {
    pub(super) const fn new(characters: u32) -> Self {
        Self(characters)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
pub(super) struct Indentation {
    column: Column,
    character: Character,
}

impl Indentation {
    pub(super) const fn root() -> Self {
        Self {
            column: Column::new(0),
            character: Character::new(0),
        }
    }

    pub(super) const fn new(column: Column, character: Character) -> Self {
        Self { character, column }
    }

    pub(super) const fn column(&self) -> Column {
        self.column
    }

    pub(super) const fn character(&self) -> Character {
        self.character
    }

    pub(super) fn try_compare(
        &self,
        other: &Indentation,
    ) -> Result<Ordering, UnexpectedIndentation> {
        let column_ordering = self.column.cmp(&other.column);
        let character_ordering = self.character.cmp(&other.character);

        if column_ordering == character_ordering {
            Ok(column_ordering)
        } else {
            Err(UnexpectedIndentation)
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub(super) struct UnexpectedIndentation;

// The indentations stack is used to keep track of the current indentation level.
// Similar to the CPython implementation, the Indentations stack always has at
// least one level which is never popped. See Reference 2.1.8.
#[derive(Debug, Clone)]
pub(super) struct Indentations {
    stack: Vec<Indentation>,
}

impl Indentations {
    pub fn is_empty(&self) -> bool {
        self.stack.len() == 1
    }

    pub fn push(&mut self, indent: Indentation) {
        debug_assert_eq!(self.current().try_compare(&indent), Ok(Ordering::Less));

        self.stack.push(indent);
    }

    pub fn pop(&mut self) -> Option<Indentation> {
        if self.is_empty() {
            None
        } else {
            self.stack.pop()
        }
    }

    pub fn current(&self) -> &Indentation {
        self.stack.last().expect("Expected indentation")
    }
}

impl Default for Indentations {
    fn default() -> Self {
        Self {
            stack: vec![Indentation::root()],
        }
    }
}

assert_eq_size!(Indentation, u64);

#[cfg(test)]
mod tests {
    use crate::lexer_v2::indentation::{Character, Column, Indentation};
    use std::cmp::Ordering;
    

    #[test]
    fn indentation_try_compare() {
        let tab = Indentation::new(Column::new(8), Character::new(1));

        assert_eq!(tab.try_compare(&tab), Ok(Ordering::Equal));

        let two_tabs = Indentation::new(Column::new(16), Character::new(2));
        assert_eq!(two_tabs.try_compare(&tab), Ok(Ordering::Greater));
        assert_eq!(tab.try_compare(&two_tabs), Ok(Ordering::Less));
    }
}
