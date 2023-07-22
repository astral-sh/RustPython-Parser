//! Token type for Python source code created by the lexer and consumed by the parser.
//!
//! This module defines the tokens that the lexer recognizes. The tokens are
//! loosely based on the token definitions found in the [CPython source].
//!
//! [CPython source]: https://github.com/python/cpython/blob/dfc2e065a2e71011017077e549cd2f9bf4944c54/Include/internal/pycore_token.h
use crate::text_size::TextSize;
use bitflags::bitflags;
use num_bigint::BigInt;
use std::borrow::Cow;
use std::error::Error;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Token<'source> {
    pub kind: TokenKind,
    pub length: TextSize,
    pub value: TokenValue<'source>,
    pub flags: TokenFlags,
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub enum TokenValue<'source> {
    #[default]
    None,
    String(Cow<'source, str>),
    BigInt(BigInt),
}

impl<'source> TokenValue<'source> {
    pub(crate) fn unwrap_into_string(self) -> String {
        match self {
            TokenValue::String(value) => value.into_owned(),
            TokenValue::None | TokenValue::BigInt(_) => panic!("Expected string"),
        }
    }

    pub(crate) fn unwrap_into_bigint(self) -> BigInt {
        match self {
            TokenValue::BigInt(value) => value,
            TokenValue::String(_) | TokenValue::None => {
                panic!("Expected bigint")
            }
        }
    }
}

impl<'source> Token<'source> {
    pub const fn new(kind: TokenKind, length: TextSize) -> Self {
        Self {
            kind,
            length,
            flags: TokenFlags::empty(),
            value: TokenValue::None,
        }
    }

    pub const fn eof() -> Self {
        Self::new(TokenKind::EndOfFile, TextSize::new(0))
    }

    pub fn with_string_value(mut self, value: Cow<'source, str>) -> Self {
        self.value = TokenValue::String(value);
        self
    }

    pub fn with_bigint_value(mut self, value: BigInt) -> Self {
        self.value = TokenValue::BigInt(value);
        self
    }

    pub fn with_flags(mut self, flags: TokenFlags) -> Self {
        self.flags = flags;
        self
    }
}

bitflags! {
    #[derive(Debug, Copy, Clone, Eq, PartialEq)]
    pub struct TokenFlags: u8 {
        const Unterminated     = 0x0000_0001;

        // TODO(micha): Consider storing the parsed Text for all Literals and then re-parsing the
        // triple-quoted, fstring, bytes (and values for numbers) on demand. Can avoid many heap allocations
        // if we use stack allocated strings / imstr.
        // Strings
        const TripleQuoted     = 0b0000_0010;

        /// A f-string literal, with a `f` or `F` prefix.
        const FString          = 0b0000_0100;

        /// A byte string literal, with a `b` or `B` prefix.
        const Bytes            = 0b0000_1000;

        /// A raw string literal, with a `r` or `R` prefix.
        const Raw        = 0b0001_0000;

        /// A unicode string literal, with a `u` or `U` prefix.
        const Unicode          = 0b1000_0000;
    }
}

impl TokenFlags {
    pub fn as_string_kind(self) -> crate::StringKind {
        if self.contains(TokenFlags::Bytes) {
            if self.contains(TokenFlags::Raw) {
                crate::StringKind::RawBytes
            } else {
                crate::StringKind::Bytes
            }
        } else if self.contains(TokenFlags::FString) {
            if self.contains(TokenFlags::Raw) {
                crate::StringKind::RawFString
            } else {
                crate::StringKind::FString
            }
        } else if self.contains(TokenFlags::Unicode) {
            crate::StringKind::Unicode
        } else if self.contains(TokenFlags::Raw) {
            crate::StringKind::RawString
        } else {
            crate::StringKind::String
        }
    }
}

/// The set of tokens the Python source code can be tokenized in.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
#[repr(u8)]
pub enum TokenKind {
    /** Literals **/
    /// Token value for an integer.
    Int,
    /// Token value for a floating point number.
    Float,
    /// Token value for a complex number.
    Complex,
    /// Token value for a string.
    String,

    /// Token value for a name, commonly known as an identifier.
    Identifier,

    /** Trivia */
    /// Token value for a comment. These are filtered out of the token stream prior to parsing.
    Comment,
    /// Token value for a newline that is not a logical line break. These are filtered out of
    /// the token stream prior to parsing.
    NonLogicalNewline,

    LineContinuation,

    EndOfFile,

    Whitespace,

    /* Semantic Whitespace */
    /// Token value for a newline.
    Newline,

    /// Token value for an indent.
    Indent,
    /// Token value for a dedent.
    Dedent,

    /* Punctuation */
    /// Token value for a left parenthesis `(`.
    Lpar,
    /// Token value for a right parenthesis `)`.
    Rpar,
    /// Token value for a left square bracket `[`.
    Lsqb,
    /// Token value for a right square bracket `]`.
    Rsqb,
    /// Token value for a colon `:`.
    Colon,
    /// Token value for a comma `,`.
    Comma,
    /// Token value for a semicolon `;`.
    Semi,
    /// Token value for plus `+`.
    Plus,
    /// Token value for minus `-`.
    Minus,
    /// Token value for star `*`.
    Star,
    /// Token value for slash `/`.
    Slash,
    /// Token value for vertical bar `|`.
    Vbar,
    /// Token value for ampersand `&`.
    Amper,
    /// Token value for less than `<`.
    Less,
    /// Token value for greater than `>`.
    Greater,
    /// Token value for equal `=`.
    Equal,
    /// Token value for dot `.`.
    Dot,
    /// Token value for percent `%`.
    Percent,
    /// Token value for left bracket `{`.
    Lbrace,
    /// Token value for right bracket `}`.
    Rbrace,
    /// Token value for double equal `==`.
    EqEqual,
    /// Token value for not equal `!=`.
    NotEqual,
    /// Token value for less than or equal `<=`.
    LessEqual,
    /// Token value for greater than or equal `>=`.
    GreaterEqual,
    /// Token value for tilde `~`.
    Tilde,
    /// Token value for caret `^`.
    CircumFlex,
    /// Token value for left shift `<<`.
    LeftShift,
    /// Token value for right shift `>>`.
    RightShift,
    /// Token value for double star `**`.
    DoubleStar,
    /// Token value for double star equal `**=`.
    DoubleStarEqual,
    /// Token value for plus equal `+=`.
    PlusEqual,
    /// Token value for minus equal `-=`.
    MinusEqual,
    /// Token value for star equal `*=`.
    StarEqual,
    /// Token value for slash equal `/=`.
    SlashEqual,
    /// Token value for percent equal `%=`.
    PercentEqual,
    /// Token value for ampersand equal `&=`.
    AmperEqual,
    /// Token value for vertical bar equal `|=`.
    VbarEqual,
    /// Token value for caret equal `^=`.
    CircumflexEqual,
    /// Token value for left shift equal `<<=`.
    LeftShiftEqual,
    /// Token value for right shift equal `>>=`.
    RightShiftEqual,
    /// Token value for double slash `//`.
    DoubleSlash,
    /// Token value for double slash equal `//=`.
    DoubleSlashEqual,
    /// Token value for colon equal `:=`.
    ColonEqual,
    /// Token value for at `@`.
    At,
    /// Token value for at equal `@=`.
    AtEqual,
    /// Token value for arrow `->`.
    Rarrow,
    /// Token value for ellipsis `...`.
    Ellipsis,

    // Self documenting.
    // Keywords:
    False,
    None,
    True,

    And,
    As,
    Assert,
    Async,
    Await,
    Break,
    Class,
    Continue,
    Def,
    Del,
    Elif,
    Else,
    Except,
    Finally,
    For,
    From,
    Global,
    If,
    Import,
    In,
    Is,
    Lambda,
    Nonlocal,
    Not,
    Or,
    Pass,
    Raise,
    Return,
    Try,
    While,
    With,
    Yield,

    // Contextual keywords
    Match,
    Case,
    Type,

    // Ruff specific tokens
    Bogus,
}

impl TokenKind {
    #[inline(always)]
    pub fn is_keyword(self) -> bool {
        self >= TokenKind::False && self <= TokenKind::Case
    }

    #[inline(always)]
    pub fn is_contextual_keyword(self) -> bool {
        self >= TokenKind::Match && self <= TokenKind::Case
    }

    #[inline(always)]
    pub fn is_non_contextual_keyword(self) -> bool {
        self.is_keyword() && !self.is_contextual_keyword()
    }

    #[inline(always)]
    pub fn is_punctuation(self) -> bool {
        self >= TokenKind::Lpar && self <= TokenKind::Ellipsis
    }

    #[inline(always)]
    pub fn is_literal(self) -> bool {
        matches!(
            self,
            TokenKind::Int | TokenKind::Float | TokenKind::Complex | TokenKind::String
        )
    }

    #[inline(always)]
    pub const fn is_trivia(self) -> bool {
        matches!(
            self,
            TokenKind::Comment
                | TokenKind::Whitespace
                | TokenKind::NonLogicalNewline
                | TokenKind::EndOfFile
        )
    }
}

/// The kind of string literal as described in the [String and Bytes literals]
/// section of the Python reference.
///
/// [String and Bytes literals]: https://docs.python.org/3/reference/lexical_analysis.html#string-and-bytes-literals
#[derive(PartialEq, Eq, Debug, Clone, Hash, Copy)] // TODO: is_macro::Is
pub enum StringKind {
    /// A normal string literal with no prefix.
    String,
    /// A f-string literal, with a `f` or `F` prefix.
    FString,
    /// A byte string literal, with a `b` or `B` prefix.
    Bytes,
    /// A raw string literal, with a `r` or `R` prefix.
    RawString,
    /// A raw f-string literal, with a `rf`/`fr` or `rF`/`Fr` or `Rf`/`fR` or `RF`/`FR` prefix.
    RawFString,
    /// A raw byte string literal, with a `rb`/`br` or `rB`/`Br` or `Rb`/`bR` or `RB`/`BR` prefix.
    RawBytes,
    /// A unicode string literal, with a `u` or `U` prefix.
    Unicode,
}

impl TryFrom<char> for StringKind {
    type Error = UnexpectedStringPrefixError;

    fn try_from(ch: char) -> Result<Self, UnexpectedStringPrefixError> {
        match ch {
            'r' | 'R' => Ok(StringKind::RawString),
            'f' | 'F' => Ok(StringKind::FString),
            'u' | 'U' => Ok(StringKind::Unicode),
            'b' | 'B' => Ok(StringKind::Bytes),
            c => Err(UnexpectedStringPrefixError {
                first: c,
                second: None,
            }),
        }
    }
}

impl TryFrom<[char; 2]> for StringKind {
    type Error = UnexpectedStringPrefixError;

    fn try_from(chars: [char; 2]) -> Result<Self, UnexpectedStringPrefixError> {
        match chars {
            ['r' | 'R', 'f' | 'F'] => Ok(StringKind::RawFString),
            ['f' | 'F', 'r' | 'R'] => Ok(StringKind::RawFString),
            ['r' | 'R', 'b' | 'B'] => Ok(StringKind::RawBytes),
            ['b' | 'B', 'r' | 'R'] => Ok(StringKind::RawBytes),
            [c1, c2] => Err(UnexpectedStringPrefixError {
                first: c1,
                second: Some(c2),
            }),
        }
    }
}

pub struct UnexpectedStringPrefixError {
    first: char,
    second: Option<char>,
}

impl Display for UnexpectedStringPrefixError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(second) = self.second {
            write!(f, "Unexpected string prefix: {}{second}", self.first)
        } else {
            write!(f, "Unexpected string prefix: {}", self.first)
        }
    }
}

impl Debug for UnexpectedStringPrefixError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl Error for UnexpectedStringPrefixError {}

impl fmt::Display for StringKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use StringKind::*;
        match self {
            String => f.write_str(""),
            FString => f.write_str("f"),
            Bytes => f.write_str("b"),
            RawString => f.write_str("r"),
            RawFString => f.write_str("rf"),
            RawBytes => f.write_str("rb"),
            Unicode => f.write_str("u"),
        }
    }
}

impl StringKind {
    /// Returns true if the string is a raw string, i,e one of
    /// [`StringKind::RawString`] or [`StringKind::RawFString`] or [`StringKind::RawBytes`].
    pub fn is_raw(&self) -> bool {
        use StringKind::{RawBytes, RawFString, RawString};
        matches!(self, RawString | RawFString | RawBytes)
    }

    /// Returns true if the string is an f-string, i,e one of
    /// [`StringKind::FString`] or [`StringKind::RawFString`].
    pub fn is_any_fstring(&self) -> bool {
        use StringKind::{FString, RawFString};
        matches!(self, FString | RawFString)
    }

    /// Returns true if the string is a byte string, i,e one of
    /// [`StringKind::Bytes`] or [`StringKind::RawBytes`].
    pub fn is_any_bytes(&self) -> bool {
        use StringKind::{Bytes, RawBytes};
        matches!(self, Bytes | RawBytes)
    }

    /// Returns true if the string is a unicode string, i,e [`StringKind::Unicode`].
    pub fn is_unicode(&self) -> bool {
        matches!(self, StringKind::Unicode)
    }

    /// Returns the number of characters in the prefix.
    pub fn prefix_len(&self) -> TextSize {
        use StringKind::*;
        let len = match self {
            String => 0,
            RawString | FString | Unicode | Bytes => 1,
            RawFString | RawBytes => 2,
        };
        len.into()
    }

    pub(crate) fn flags(&self) -> TokenFlags {
        match self {
            StringKind::String => TokenFlags::empty(),
            StringKind::FString => TokenFlags::FString,
            StringKind::Bytes => TokenFlags::Bytes,
            StringKind::RawString => TokenFlags::Raw,
            StringKind::RawFString => TokenFlags::Raw | TokenFlags::FString,
            StringKind::RawBytes => TokenFlags::Raw | TokenFlags::Bytes,
            StringKind::Unicode => TokenFlags::Unicode,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer_v2::{Token, TokenKind};
    use std::borrow::Cow;

    static_assertions::assert_eq_size!(TokenKind, [u8; 1]);
    static_assertions::assert_eq_size!(Cow<'_, str>, [u8; 24]);
    static_assertions::assert_eq_size!(Token, [u8; 40]);
}
