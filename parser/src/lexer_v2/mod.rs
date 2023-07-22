//! This module takes care of lexing Python source text.
//!
//! This means source code is scanned and translated into separate tokens. The rules
//! governing what is and is not a valid token are defined in the Python reference
//! guide section on [Lexical analysis].
//!
//! The primary function in this module is [`lex`], which takes a string slice
//! and returns an iterator over the tokens in the source code. The tokens are currently returned
//! as a `Result<Spanned, LexicalError>`, where [`Spanned`] is a tuple containing the
//! start and end [`TextSize`] and a [`TokenKind`] denoting the token.
//!
//! # Example
//!
//! ```
//! use rustpython_parser::{lexer::lex, Tok, Mode, StringKind};
//!
//! let source = "x = 'RustPython'";
//! let tokens = lex(source, Mode::Module)
//!     .map(|tok| tok.expect("Failed to lex"))
//!     .collect::<Vec<_>>();
//!
//! for (token, range) in tokens {
//!     println!(
//!         "{token:?}@{range:?}",
//!     );
//! }
//! ```
//!
//! [Lexical analysis]: https://docs.python.org/3/reference/lexical_analysis.html
use std::borrow::Cow;
use std::str::FromStr;
use std::{char, cmp::Ordering};

use num_bigint::BigInt;
use num_traits::Num;
use unic_emoji_char::is_emoji_presentation;
use unic_ucd_ident::{is_xid_continue, is_xid_start};

pub use token::{Token, TokenFlags, TokenKind};

use crate::lexer_v2::cursor::{Cursor, EOF_CHAR};
use crate::lexer_v2::indentation::{Character, Column, Indentation, Indentations};
use crate::lexer_v2::token::StringKind;
use crate::text_size::{TextRange, TextSize};
use crate::Mode;

pub(crate) mod compat_adapter;
mod cursor;
mod indentation;
mod token;

#[derive(Debug, Clone)]
pub struct LexDiagnostic {
    range: TextRange,
    message: String,
}

/// A lexer for Python source code.
#[derive(Clone, Debug)]
pub struct Lexer<'source> {
    cursor: Cursor<'source>,

    source: &'source str,

    // Are we at the beginning of a line?
    new_logical_line: bool,
    is_blank: bool,
    left_parens: u32,

    // Indentation levels.
    indentations: Indentations,
    pending_indentation: Option<Indentation>,

    diagnostics: Vec<LexDiagnostic>,
}

/// Create a new lexer from a source string.
///
/// # Examples
///
/// ```
/// use rustpython_parser::{Mode, lexer::lex};
///
/// let source = "def hello(): return 'world'";
/// let lexer = lex(source, Mode::Module);
///
/// for token in lexer {
///    println!("{:?}", token);
/// }
/// ```
#[inline]
pub fn lex(source: &str, mode: Mode) -> Lexer<'_> {
    lex_starts_at(source, mode, TextSize::default())
}

/// Create a new lexer from a source string, starting at a given location.
/// You probably want to use [`lex`] instead.
pub fn lex_starts_at(source: &str, _mode: Mode, start_offset: TextSize) -> Lexer<'_> {
    Lexer::new(source, start_offset)
}

impl<'source> Lexer<'source> {
    /// Create a new lexer from T and a starting location. You probably want to use
    /// [`lex`] instead.
    pub fn new(source: &'source str, _start: TextSize) -> Self {
        let mut lexer = Lexer {
            new_logical_line: true,
            is_blank: true,
            left_parens: 0,
            indentations: Indentations::default(),
            cursor: Cursor::new(source),
            diagnostics: Vec::new(),
            pending_indentation: None,
            source,
        };

        // TODO: Handle possible mismatch between BOM and explicit encoding declaration.
        // spell-checker:ignore feff
        lexer.cursor.eat_char('\u{feff}');

        lexer
    }

    pub fn finish(self) -> Vec<LexDiagnostic> {
        self.diagnostics
    }

    pub fn next_token(&mut self) -> Token<'source> {
        if let Some(indentation) = self.pending_indentation.take() {
            match self.indentations.current().try_compare(&indentation) {
                Ok(Ordering::Greater) => {
                    self.pending_indentation = Some(indentation);
                    self.indentations.pop();
                    return Token::new(TokenKind::Dedent, TextSize::new(0));
                }
                Ok(Ordering::Equal) => {
                    if indentation.character() != Character::new(0) {
                        return Token::new(TokenKind::Whitespace, self.cursor.token_len());
                    }
                }
                _ => {
                    unreachable!("Invalid indentation stack. Parent indentation was smaller than this indentation.")
                }
            }
        }

        if self.cursor.is_eof() {
            return if !self.new_logical_line {
                self.new_logical_line = true;
                Token::new(TokenKind::Newline, TextSize::new(0))
            } else if let Some(dedent) = self.handle_indentation(Indentation::root()) {
                dedent
            } else {
                Token::eof()
            };
        }

        // #[cfg(debug_assertions)]
        // {
        //     if self.new_logical_line {
        //         debug_assert!(matches!(
        //             self.cursor.previous(),
        //             '\n' | '\r' | cursor::EOF_CHAR
        //         ));
        //     }
        // }

        self.cursor.start_token();

        let first = self.cursor.first();

        if let Some(trivia) = self.eat_trivia(first) {
            return trivia;
        }

        self.is_blank = false;
        self.cursor.bump();
        self.lex_non_trivia(first)
    }

    fn lex_non_trivia(&mut self, first: char) -> Token<'source> {
        if first.is_ascii() {
            match first {
                'a'..='z' | 'A'..='Z' | '_' => self.lex_identifier(first),
                '0'..='9' => self.lex_number(first),
                '"' | '\'' => self.lex_string(StringKind::String, first),
                '=' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::EqEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::Equal, TextSize::new(1))
                    }
                }
                '+' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::PlusEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::Plus, TextSize::new(1))
                    }
                }
                '*' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::StarEqual, TextSize::new(2))
                    } else if self.cursor.eat_char('*') {
                        if self.cursor.eat_char('=') {
                            Token::new(TokenKind::DoubleStarEqual, TextSize::new(3))
                        } else {
                            Token::new(TokenKind::DoubleStar, TextSize::new(2))
                        }
                    } else {
                        Token::new(TokenKind::Star, TextSize::new(1))
                    }
                }
                '/' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::SlashEqual, TextSize::new(2))
                    } else if self.cursor.eat_char('/') {
                        if self.cursor.eat_char('=') {
                            Token::new(TokenKind::DoubleSlashEqual, TextSize::new(3))
                        } else {
                            Token::new(TokenKind::DoubleSlash, TextSize::new(2))
                        }
                    } else {
                        Token::new(TokenKind::Slash, TextSize::new(1))
                    }
                }
                '%' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::PercentEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::Percent, TextSize::new(1))
                    }
                }
                '|' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::VbarEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::Vbar, TextSize::new(1))
                    }
                }
                '^' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::CircumflexEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::CircumFlex, TextSize::new(1))
                    }
                }
                '&' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::AmperEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::Amper, TextSize::new(1))
                    }
                }
                '-' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::MinusEqual, TextSize::new(2))
                    } else if self.cursor.eat_char('>') {
                        Token::new(TokenKind::Rarrow, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::Minus, TextSize::new(1))
                    }
                }
                '@' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::AtEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::At, TextSize::new(1))
                    }
                }
                '!' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::NotEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::Bogus, TextSize::new(1))
                    }
                }
                '~' => Token::new(TokenKind::Tilde, TextSize::new(1)),
                // TODO emit an error token if below zero? No, because we also don't emit an error
                // token for extra parens?
                '(' => {
                    self.left_parens = self.left_parens.saturating_add(1);
                    Token::new(TokenKind::Lpar, TextSize::new(1))
                }
                ')' => {
                    self.left_parens = self.left_parens.saturating_sub(1);
                    Token::new(TokenKind::Rpar, TextSize::new(1))
                }
                '[' => {
                    self.left_parens = self.left_parens.saturating_add(1);
                    Token::new(TokenKind::Lsqb, TextSize::new(1))
                }
                ']' => {
                    self.left_parens = self.left_parens.saturating_sub(1);
                    Token::new(TokenKind::Rsqb, TextSize::new(1))
                }
                '{' => {
                    self.left_parens = self.left_parens.saturating_add(1);
                    Token::new(TokenKind::Lbrace, TextSize::new(1))
                }
                '}' => {
                    self.left_parens = self.left_parens.saturating_sub(1);
                    Token::new(TokenKind::Rbrace, TextSize::new(1))
                }
                ':' => {
                    if self.cursor.eat_char('=') {
                        Token::new(TokenKind::ColonEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::Colon, TextSize::new(1))
                    }
                }
                ';' => Token::new(TokenKind::Semi, TextSize::new(1)),
                '<' => {
                    if self.cursor.eat_char('<') {
                        if self.cursor.eat_char('=') {
                            Token::new(TokenKind::LeftShiftEqual, TextSize::new(3))
                        } else {
                            Token::new(TokenKind::LeftShift, TextSize::new(2))
                        }
                    } else if self.cursor.eat_char('=') {
                        Token::new(TokenKind::LessEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::Less, TextSize::new(1))
                    }
                }
                '>' => {
                    if self.cursor.eat_char('>') {
                        if self.cursor.eat_char('=') {
                            Token::new(TokenKind::RightShiftEqual, TextSize::new(3))
                        } else {
                            Token::new(TokenKind::RightShift, TextSize::new(2))
                        }
                    } else if self.cursor.eat_char('=') {
                        Token::new(TokenKind::GreaterEqual, TextSize::new(2))
                    } else {
                        Token::new(TokenKind::Greater, TextSize::new(1))
                    }
                }
                ',' => Token::new(TokenKind::Comma, TextSize::new(1)),
                '.' => match self.cursor.first() {
                    '0'..='9' => self.lex_number('.'),
                    '.' if self.cursor.second() == '.' => {
                        self.cursor.bump();
                        self.cursor.bump();
                        Token::new(TokenKind::Ellipsis, TextSize::new(3))
                    }

                    _ => Token::new(TokenKind::Dot, TextSize::new(1)),
                },
                '#' => self.lex_comment(),
                // Line continuation. We should emit a token for the line continuation
                '\\' => {
                    let continuation = if self.cursor.eat_char('\r') {
                        self.cursor.eat_char('\n');
                        true
                    } else {
                        self.cursor.eat_char('\n')
                    };

                    if continuation {
                        self.new_logical_line = false;
                        // FIXME The new line should really not be consumed... but that's kind of hard
                        Token::new(TokenKind::LineContinuation, self.cursor.token_len())
                    } else {
                        // TODO emit diagnostic

                        Token::new(TokenKind::Bogus, TextSize::new(1))
                    }
                }
                _ => Token::new(TokenKind::Bogus, TextSize::new(1)),
            }
        } else if is_non_ascii_identifier_start(first) {
            self.lex_identifier(first)
        } else if is_emoji_presentation(first) {
            Token::new(TokenKind::Identifier, self.cursor.token_len())
        } else {
            Token::new(TokenKind::Bogus, self.cursor.text_len())
        }
    }

    // TODO handle \x0C

    fn eat_trivia(&mut self, first: char) -> Option<Token<'source>> {
        let token = match first {
            prev @ (' ' | '\t') => {
                self.cursor.bump();

                if self.new_logical_line {
                    let indentation = self.lex_indentation(prev);

                    // Indention of an all whitespace line or comment only line. Indention rules don't apply
                    if matches!(self.cursor.first(), '\n' | '\r' | '#' | EOF_CHAR) {
                        Token::new(TokenKind::Whitespace, self.cursor.token_len())
                    } else {
                        self.new_logical_line = false;
                        return self.handle_indentation(indentation);
                    }
                } else {
                    // Skip over whitespace
                    self.cursor.eat_while(|c| matches!(c, ' ' | '\t'));
                    Token::new(TokenKind::Whitespace, self.cursor.token_len())
                }
            }

            '#' => {
                self.cursor.bump();
                self.lex_comment()
            }

            '\n' => {
                self.cursor.bump();
                let kind = self.newline_token_kind();
                self.new_logical_line = self.new_logical_line || kind == TokenKind::Newline;
                self.is_blank = true;
                Token::new(kind, TextSize::new(1))
            }
            //  `\r` or `\r\n`
            '\r' => {
                self.cursor.bump();
                let kind = self.newline_token_kind();
                self.new_logical_line = self.new_logical_line || kind == TokenKind::Newline;
                self.is_blank = true;
                let len = if self.cursor.eat_char('\n') {
                    TextSize::new(2)
                } else {
                    TextSize::new(1)
                };
                Token::new(kind, len)
            }

            '\x0C' => {
                // Skip over whitespace
                self.cursor.bump();
                self.cursor.eat_while(|c| matches!(c, ' ' | '\t' | '\x0C'));
                self.is_blank = true;
                Token::new(TokenKind::Whitespace, self.cursor.token_len())
            }

            _ => {
                return if self.new_logical_line {
                    self.new_logical_line = false;
                    self.handle_indentation(Indentation::root())
                } else {
                    None
                };
            }
        };

        Some(token)
    }

    fn newline_token_kind(&self) -> TokenKind {
        if self.is_blank || self.left_parens > 0 {
            TokenKind::NonLogicalNewline
        } else {
            TokenKind::Newline
        }
    }

    fn lex_indentation(&mut self, first: char) -> Indentation {
        debug_assert!(self.new_logical_line);
        debug_assert!(matches!(first, ' ' | '\t'));

        let mut column = 0u32;
        let mut character = 0u32;

        if first == ' ' {
            column += 1;
            character += 1;
        } else {
            column += 8;
            character += 1;
        }

        loop {
            match self.cursor.first() {
                ' ' => {
                    column += 1;
                }
                '\t' => column = (column % 8) + column,
                _ => break,
            }

            self.cursor.bump();
            character += 1;
        }

        Indentation::new(Column::new(column), Character::new(character))
    }

    fn handle_indentation(&mut self, indentation: Indentation) -> Option<Token<'source>> {
        match self.indentations.current().try_compare(&indentation) {
            // Dedent
            Ok(Ordering::Greater) => {
                self.indentations.pop();
                self.pending_indentation = Some(indentation);

                Some(Token::new(TokenKind::Dedent, TextSize::new(0)))
            }

            Ok(Ordering::Equal) => {
                if indentation.character() != Character::new(0) {
                    Some(Token::new(TokenKind::Whitespace, self.cursor.token_len()))
                } else {
                    None
                }
            }

            // Indent
            Ok(Ordering::Less) => {
                self.indentations.push(indentation);
                Some(Token::new(TokenKind::Indent, self.cursor.token_len()))
            }
            Err(_) => {
                self.diagnostics.push(LexDiagnostic {
                    // TODO add right range
                    range: self.token_range(),
                    message: "Unexpected indent".to_string(),
                });

                Some(Token::new(TokenKind::Bogus, self.cursor.token_len()))
            }
        }
    }

    #[inline]
    fn token_range(&self) -> TextRange {
        let end = self.offset();
        let len = self.cursor.token_len();

        TextRange::at(end - len, len)
    }

    #[inline]
    fn offset(&self) -> TextSize {
        TextSize::new(self.source.len() as u32) - self.cursor.text_len()
    }

    fn lex_comment(&mut self) -> Token<'source> {
        #[cfg(debug_assertions)]
        debug_assert_eq!(self.cursor.previous(), '#');

        self.cursor.eat_while(|c| !matches!(c, '\n' | '\r'));

        let range = self.token_range();
        let comment = Cow::Borrowed(&self.source[range]);

        Token::new(TokenKind::Comment, self.cursor.token_len()).with_string_value(comment)
    }

    /// Lex an identifier. Also used for keywords and string/bytes literals with a prefix.
    fn lex_identifier(&mut self, first: char) -> Token<'source> {
        match self.cursor.first() {
            quote @ ('\'' | '"') => {
                if let Ok(string_kind) = StringKind::try_from(first) {
                    self.cursor.bump();
                    return self.lex_string(string_kind, quote);
                }
            }
            second @ ('f' | 'F' | 'r' | 'R' | 'b' | 'B') if is_quote(self.cursor.second()) => {
                self.cursor.bump();

                if let Ok(string_kind) = StringKind::try_from([first, second]) {
                    let quote = self.cursor.bump().unwrap();
                    return self.lex_string(string_kind, quote);
                }
            }
            _ => {}
        }

        self.cursor.eat_while(is_identifier_continuation);

        let range = self.token_range();
        let text = &self.source[range];

        let keyword = match text {
            "False" => TokenKind::False,
            "None" => TokenKind::None,
            "True" => TokenKind::True,
            "and" => TokenKind::And,
            "as" => TokenKind::As,
            "assert" => TokenKind::Assert,
            "async" => TokenKind::Async,
            "await" => TokenKind::Await,
            "break" => TokenKind::Break,
            "case" => TokenKind::Case,
            "class" => TokenKind::Class,
            "continue" => TokenKind::Continue,
            "def" => TokenKind::Def,
            "del" => TokenKind::Del,
            "elif" => TokenKind::Elif,
            "else" => TokenKind::Else,
            "except" => TokenKind::Except,
            "finally" => TokenKind::Finally,
            "for" => TokenKind::For,
            "from" => TokenKind::From,
            "global" => TokenKind::Global,
            "if" => TokenKind::If,
            "import" => TokenKind::Import,
            "in" => TokenKind::In,
            "is" => TokenKind::Is,
            "lambda" => TokenKind::Lambda,
            "match" => TokenKind::Match,
            "nonlocal" => TokenKind::Nonlocal,
            "not" => TokenKind::Not,
            "or" => TokenKind::Or,
            "pass" => TokenKind::Pass,
            "raise" => TokenKind::Raise,
            "return" => TokenKind::Return,
            "try" => TokenKind::Try,
            "type" => TokenKind::Type,
            "while" => TokenKind::While,
            "with" => TokenKind::With,
            "yield" => TokenKind::Yield,
            _ => {
                return Token::new(TokenKind::Identifier, range.len())
                    .with_string_value(Cow::Borrowed(text))
            }
        };

        Token::new(keyword, range.len())
    }

    /// Numeric lexing. The feast can start!
    fn lex_number(&mut self, first: char) -> Token<'source> {
        if first == '0' {
            if self.cursor.eat_if(|c| matches!(c, 'x' | 'X')).is_some() {
                // Hex! (0xdeadbeef)
                return self.lex_number_radix(Radix::Hex);
            } else if self.cursor.eat_if(|c| matches!(c, 'o' | 'O')).is_some() {
                // Octal style! (0o377)
                return self.lex_number_radix(Radix::Octal);
            } else if self.cursor.eat_if(|c| matches!(c, 'b' | 'B')).is_some() {
                // Binary! (0b_1110_0101)
                return self.lex_number_radix(Radix::Binary);
            }
        }

        self.lex_decimal_number(first)
    }

    /// Lex a hex/octal/decimal/binary number without a decimal point.
    fn lex_number_radix(&mut self, radix: Radix) -> Token<'source> {
        #[cfg(debug_assertions)]
        debug_assert!(matches!(
            self.cursor.previous().to_ascii_lowercase(),
            'x' | 'o' | 'b'
        ));

        let value_text = self.radix_run(radix, self.offset());

        // TODO Create our own `Write` and write the value to it. Returns `Borrowed` if the
        // formatted radix is the same as the source text.
        let value = match BigInt::from_str_radix(&value_text, radix.as_u32()) {
            Ok(value) => value,
            Err(_) => {
                // TODO emit diagnostic
                return Token::new(TokenKind::Bogus, self.cursor.token_len());
            }
        };

        Token::new(TokenKind::Int, self.cursor.token_len()).with_bigint_value(value)
    }

    /// Consume a sequence of numbers with the given radix,
    /// the digits can be decorated with underscores
    /// like this: '1_2_3_4' == '1234'
    fn radix_run(&mut self, radix: Radix, start: TextSize) -> Cow<'source, str> {
        loop {
            if self.eat_digit(radix).is_some() {
                // nothing
            } else if self.cursor.first() == '_' && radix.is_digit(self.cursor.second()) {
                break;
            } else {
                return Cow::Borrowed(&self.source[TextRange::new(start, self.offset())]);
            }
        }

        let len = self.offset() - start;
        let mut cleaned = String::from(&self.source[TextRange::at(start, len)]);

        loop {
            if let Some(c) = self.eat_digit(radix) {
                cleaned.push(c);
            } else if self.cursor.first() == '_' && radix.is_digit(self.cursor.second()) {
                cleaned.push(self.cursor.second());
                self.cursor.bump();
                self.cursor.bump();
            } else {
                break;
            }
        }
        Cow::Owned(cleaned)
    }

    /// Consume a single character with the given radix.
    fn eat_digit(&mut self, radix: Radix) -> Option<char> {
        self.cursor.eat_if(|c| radix.is_digit(c))
    }

    // TODO implement parsing manually
    /// Lex a normal number, that is, no octal, hex or binary number.
    fn lex_decimal_number(&mut self, first_digit_or_dot: char) -> Token<'source> {
        #[cfg(debug_assertions)]
        debug_assert!(self.cursor.previous().is_ascii_digit() || self.cursor.previous() == '.');

        let start = self.offset() - TextSize::new(1);
        let start_is_zero = first_digit_or_dot == '0';

        // Normal number:
        let value_text = self.radix_run(Radix::Decimal, start);

        // If float:
        let (is_float, before_exponent) = if self.cursor.eat_char('.') || first_digit_or_dot == '.'
        {
            if self.cursor.eat_char('_') {
                // TODO emit a diagnostic;
                return Token::new(TokenKind::Bogus, self.cursor.token_len());
            }

            let after_dot = self.radix_run(Radix::Decimal, self.offset());
            let text = if matches!(value_text, Cow::Borrowed(_))
                && matches!(after_dot, Cow::Borrowed(_))
            {
                Cow::Borrowed(&self.source[self.token_range()])
            } else {
                Cow::Owned(format!("{}.{}", value_text, after_dot))
            };

            (true, text)
        } else {
            (false, value_text)
        };

        let (is_float, number) = match self.cursor.rest().as_bytes() {
            [b'e' | b'E', b'0'..=b'9', ..] => {
                self.cursor.bump();

                let exponent = self.radix_run(Radix::Decimal, self.offset());

                let number = match (before_exponent, exponent) {
                    (Cow::Borrowed(_), Cow::Borrowed(_)) => {
                        Cow::Borrowed(&self.source[self.token_range()])
                    }

                    (Cow::Owned(mut owned), exponent) => {
                        owned.push('e');
                        owned.push_str(&exponent);
                        Cow::Owned(owned)
                    }
                    (before, exponent) => Cow::Owned(format!("{before}e{exponent}")),
                };

                (true, number)
            }
            [b'e' | b'E', b'+' | b'-', b'0'..=b'9', ..] => {
                self.cursor.bump();
                let sign = self.cursor.bump().unwrap();
                let exponent = self.radix_run(Radix::Decimal, self.offset());

                let number = match (before_exponent, exponent) {
                    (Cow::Borrowed(_), Cow::Borrowed(_)) => {
                        Cow::Borrowed(&self.source[self.token_range()])
                    }
                    (Cow::Owned(mut owned), exponent) => {
                        owned.push('e');
                        owned.push(sign);
                        owned.push_str(&exponent);
                        Cow::Owned(owned)
                    }
                    (before, exponent) => Cow::Owned(format!("{before}e{sign}{exponent}")),
                };

                (true, number)
            }
            _ => (is_float, before_exponent),
        };

        if is_float {
            if self.cursor.eat_char('_') {
                // TODO emit a diagnostic;
                return Token::new(TokenKind::Bogus, self.cursor.token_len());
            }

            let n = match f64::from_str(&number) {
                Ok(n) => n,
                Err(_) => {
                    // TODO emit diagnostic
                    return Token::new(TokenKind::Bogus, self.cursor.token_len());
                }
            };

            // Parse trailing 'j':
            let kind = if self.cursor.eat_if(|c| matches!(c, 'j' | 'J')).is_some() {
                TokenKind::Complex
            } else {
                TokenKind::Float
            };

            return Token::new(kind, self.cursor.token_len())
                .with_string_value(Cow::Owned(n.to_string()));
        }

        // Parse trailing 'j':
        if self.cursor.eat_if(|c| matches!(c, 'j' | 'J')).is_some() {
            // TODO what's the right way to represent these numbers
            // TODO handle panic
            let imag = f64::from_str(&number).unwrap();

            Token::new(TokenKind::Complex, self.cursor.token_len())
                .with_string_value(Cow::Owned(imag.to_string()))
        } else {
            // TODO handle errors?
            // leading zeros in decimal integer literals are not permitted
            if start_is_zero && number != "0" {
                // TODO emit diagnostic
                // return Err(LexicalError {
                //     error: LexicalErrorType::OtherError("Invalid Token".to_owned()),
                //     location: self.get_pos(),
                // });
                Token::new(TokenKind::Bogus, self.cursor.token_len())
            } else {
                Token::new(TokenKind::Int, self.cursor.token_len()).with_string_value(number)
            }
        }
    }

    /// Lex a string literal.
    fn lex_string(&mut self, kind: StringKind, quote: char) -> Token<'source> {
        #[cfg(debug_assertions)]
        debug_assert_eq!(self.cursor.previous(), quote);

        let mut flags = kind.flags();

        // If the next two characters are also the quote character, then we have a triple-quoted
        // string; consume those two characters and ensure that we require a triple-quote to close
        let triple_quoted = if self.cursor.first() == quote && self.cursor.second() == quote {
            self.cursor.bump();
            self.cursor.bump();
            flags |= TokenFlags::TripleQuoted;
            true
        } else {
            false
        };

        let value_start = self.offset();
        let mut value_end = None;
        while let Some(c) = self.cursor.bump() {
            match c {
                // TODO remove escape character.
                '\\' => {
                    if self.cursor.eat_char('\r') {
                        self.cursor.eat_char('\n');
                    } else if self.cursor.eat_char('\n') {
                        // Line continuation
                    } else {
                        // TODO handle incorrect escape sequences
                        self.cursor.bump();
                    }
                }

                // TODO handle backslash at enw line
                // TODO validate escape sequences?

                // TODO handle line feed?
                // TODO normalize line breaks to newlines?
                '\n' | '\r' if !triple_quoted => {
                    break;
                }
                c if c == quote => {
                    if triple_quoted {
                        if self.cursor.first() == quote && self.cursor.second() == quote {
                            self.cursor.bump();
                            self.cursor.bump();
                            value_end = Some(self.offset() - TextSize::new(3));
                            break;
                        }
                    } else {
                        value_end = Some(self.offset() - TextSize::new(1));
                        break;
                    }
                }
                _ => {}
            }
        }

        let value_end = match value_end {
            Some(end) => end,
            None => {
                self.diagnostics.push(LexDiagnostic {
                    range: self.token_range(),
                    message: "Unterminated string literal".to_string(),
                });

                flags |= TokenFlags::Unterminated;
                self.offset()
            }
        };

        Token::new(TokenKind::String, self.cursor.token_len())
            .with_string_value(Cow::Borrowed(
                &self.source[TextRange::new(value_start, value_end)],
            ))
            .with_flags(flags)
    }
}

// Checks if the character c is a valid continuation character as described
// in https://docs.python.org/3/reference/lexical_analysis.html#identifiers
fn is_identifier_continuation(c: char) -> bool {
    if c.is_ascii() {
        matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '0'..='9')
    } else {
        is_xid_continue(c)
    }
}

fn is_non_ascii_identifier_start(c: char) -> bool {
    is_xid_start(c)
}

#[derive(Copy, Clone, Debug)]
enum Radix {
    Binary,
    Octal,
    Hex,
    Decimal,
}

impl Radix {
    /// Test if a digit is of a certain radix.
    fn is_digit(self, c: char) -> bool {
        c.is_digit(self.as_u32())
    }

    const fn as_u32(self) -> u32 {
        match self {
            Radix::Binary => 2,
            Radix::Octal => 8,
            Radix::Hex => 16,
            Radix::Decimal => 10,
        }
    }
}

const fn is_quote(c: char) -> bool {
    matches!(c, '\'' | '"')
}

#[cfg(test)]
mod tests {
    use insta::assert_debug_snapshot;
    use itertools::Itertools;

    use super::*;

    const WINDOWS_EOL: &str = "\r\n";
    const MAC_EOL: &str = "\r";
    const UNIX_EOL: &str = "\n";

    pub fn lex_source(source: &str) -> Vec<Token> {
        let mut lexer = lex(source, Mode::Module);
        let mut result = vec![];

        loop {
            let next = lexer.next_token();

            let is_eof = next.kind == TokenKind::EndOfFile;
            result.push(next);

            if is_eof {
                break;
            }
        }

        result
    }

    #[test]
    fn comment() {
        let source = r#"# Module comment

# New line comment

    # Indented comment
"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn identifier() {
        let source = r#"x
nonlocal
"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    // TODO special lexing for fstrings rather than doing in the parser, which feels odd.

    #[test]
    fn string() {
        let source = r#""test"
'test'
"""test"""
'''test'''
r'raw'
u'unicode'
"""a multiline string
that continues here"""

"An unterminated string
"Recovers here"
"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn binary() {
        let source = r#"0b000_0001
0B000_0000"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn octal() {
        let source = r#"0o000_0075
0O000_0012"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn hex() {
        let source = r#"0x000_00a5
0X000_1b12"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn float() {
        let source = r#"0.0123
.123
0.123_345
134344444.333
1e45
1E45
1.3e3
3.3E4"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn numbers() {
        let source = "0x2f 0o12 0b1101 0 123 123_45_67_890 0.2 1e+2 2.1e3 2j 2.2j";
        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }
    #[test]
    fn assignment() {
        let source = r"a_variable = 99 + 2-0";
        let tokens = lex_source(source);
        assert_debug_snapshot!(tokens);
    }

    macro_rules! test_indentation_with_eol {
            ($($name:ident: $eol:expr,)*) => {
                $(
                #[test]
                fn $name() {
                    let source = format!("def foo():{}   return 99{}{}", $eol, $eol, $eol);
                    let tokens = lex_source(&source);
                    assert_debug_snapshot!(tokens);
                }
                )*
            };
        }

    fn eol_test_case(eol: &str) -> String {
        format!("def foo():{}   return 99{}{}", eol, eol, eol)
    }

    #[test]
    fn windows_eol() {
        let source = eol_test_case(WINDOWS_EOL);

        let tokens = lex_source(&source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn mac_eol() {
        let source = eol_test_case(MAC_EOL);

        let tokens = lex_source(&source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn unix_eol() {
        let source = eol_test_case(UNIX_EOL);

        let tokens = lex_source(&source);

        assert_debug_snapshot!(tokens);
    }

    fn create_double_dedent_with_eol(eol: &str) -> String {
        format!("def foo():{eol} if x:{eol}{eol}  return 99{eol}{eol}")
    }

    #[test]
    fn double_dedent_with_eol_windows() {
        let source = create_double_dedent_with_eol(WINDOWS_EOL);
        let tokens = lex_source(&source);
        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn double_dedent_with_eol_mac() {
        let source = create_double_dedent_with_eol(MAC_EOL);
        let tokens = lex_source(&source);
        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn double_dedent_with_eol_unix() {
        let source = create_double_dedent_with_eol(UNIX_EOL);
        let tokens = lex_source(&source);
        assert_debug_snapshot!(tokens);
    }

    fn create_double_dedent_with_tabs(eol: &str) -> String {
        format!("def foo():{eol}\tif x:{eol}{eol}\t return 99{eol}{eol}")
    }

    #[test]
    fn double_dedent_with_tabs_windows() {
        let source = create_double_dedent_with_tabs(WINDOWS_EOL);
        let tokens = lex_source(&source);
        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn double_dedent_with_tabs_mac() {
        let source = create_double_dedent_with_tabs(MAC_EOL);
        let tokens = lex_source(&source);
        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn double_dedent_with_tabs_unix() {
        let source = create_double_dedent_with_tabs(UNIX_EOL);
        let tokens = lex_source(&source);
        assert_debug_snapshot!(tokens);
    }

    fn create_newline_in_brackets_code(eol: &str) -> String {
        r"x = [

        1,2
    ,(3,
    4,
    ), {
    5,
    6,\
    7}]
    "
        .replace('\n', eol)
    }

    #[test]
    fn newline_in_brackets_windows() {
        let code = create_newline_in_brackets_code(WINDOWS_EOL);
        let tokens = lex_source(&code);
        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn newline_in_brackets_mac() {
        let code = create_newline_in_brackets_code(MAC_EOL);
        let tokens = lex_source(&code);
        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn newline_in_brackets_unix() {
        let code = create_newline_in_brackets_code(UNIX_EOL);
        let tokens = lex_source(&code);
        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn test_non_logical_newline_in_string_continuation() {
        let source = r"(
        'a'
        'b'

        'c' \
        'd'
    )";
        let tokens = lex_source(source);
        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn logical_newline_line_comment() {
        let source = "#Hello\n#World\n";
        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn operators() {
        let source = "//////=/ /";
        let tokens = lex_source(source);
        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn string_single_line() {
        let source = r#""double" 'single' 'can\'t' "\\\"" '\t\r\n' '\g' r'raw\'' '\420' '\200\0a'"#;
        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    fn string_continuation_test_case(eol: &str) -> String {
        format!(
            "\"abc{}def\"",
            eol.chars().map(|c| format!("\\{c}")).join("")
        )
    }

    #[test]
    fn string_continuation_windows() {
        let source = string_continuation_test_case(WINDOWS_EOL);
        let tokens = lex_source(&source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn string_continuation_mac() {
        let source = string_continuation_test_case(MAC_EOL);
        let tokens = lex_source(&source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn string_continuation_unix() {
        let source = string_continuation_test_case(UNIX_EOL);
        let tokens = lex_source(&source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn test_escape_unicode_name() {
        let source = r#""\N{EN SPACE}""#;
        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
        // assert_eq!(tokens, vec![str_tok(r"\N{EN SPACE}"), TokenKind::Newline])
    }

    fn triple_quoted_test_source(eol: &str) -> String {
        format!("\"\"\"{eol} test string{eol} \"\"\"")
    }

    #[test]
    fn triple_quoted_windows() {
        let source = triple_quoted_test_source(WINDOWS_EOL);
        let tokens = lex_source(&source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn triple_quoted_mac() {
        let source = triple_quoted_test_source(MAC_EOL);
        let tokens = lex_source(&source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn triple_quoted_unix() {
        let source = triple_quoted_test_source(UNIX_EOL);
        let tokens = lex_source(&source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn while_else() {
        let source = r#"
while a:
    break
else:
    continue"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn match_statement() {
        let source = r#"
# case test_patma_098
match x:
    case -0j:
        y = 0
# case test_patma_142
y"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn type_with_continuation() {
        let source = r#"# multine definitions
type \
	X = int"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }

    #[test]
    fn regression_1() {
        let source = r#"
def __new__(cls):
    # ensure that only one instance exists
    if not cls.__instance:
        cls.__instance = super().__new__(cls)
    return cls.__instance"#;

        let tokens = lex_source(source);

        assert_debug_snapshot!(tokens);
    }
}
