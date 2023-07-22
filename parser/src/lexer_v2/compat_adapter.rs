use crate::lexer::{LexResult, LexicalError, LexicalErrorType};
use crate::lexer_v2::token::TokenValue;
use crate::lexer_v2::{Lexer, TokenFlags, TokenKind};
use crate::text_size::{TextRange, TextSize};
use crate::Tok;
use num_bigint::BigInt;
use num_traits::Num;
use std::iter::FusedIterator;

pub struct CompatAdapter<'a> {
    offset: TextSize,
    lexer: Lexer<'a>,
}

impl<'a> CompatAdapter<'a> {
    pub fn new(offset: TextSize, lexer: Lexer<'a>) -> Self {
        Self { offset, lexer }
    }
}

impl<'a> Iterator for CompatAdapter<'a> {
    type Item = LexResult;

    fn next(&mut self) -> Option<Self::Item> {
        let (tok, range) = loop {
            let item = self.lexer.next_token();
            let start = self.offset;
            self.offset += item.length;

            let tok = match item.kind {
                TokenKind::Int => {
                    let value = match item.value {
                        TokenValue::BigInt(value) => value,
                        TokenValue::String(value) => BigInt::from_str_radix(&value, 10).unwrap(),
                        _ => panic!("Expected bigint"),
                    };
                    Tok::Int { value }
                }
                TokenKind::Float => Tok::Float { value: 0.0 },
                TokenKind::Complex => Tok::Complex {
                    real: 0.0,
                    imag: 0.0,
                },
                TokenKind::String => Tok::String {
                    value: item.value.unwrap_into_string(),
                    kind: item.flags.as_string_kind(),
                    triple_quoted: item.flags.contains(TokenFlags::TripleQuoted),
                },
                TokenKind::Identifier => Tok::Name {
                    name: item.value.unwrap_into_string(),
                },
                TokenKind::Comment => Tok::Comment(item.value.unwrap_into_string()),
                TokenKind::NonLogicalNewline => Tok::NonLogicalNewline,
                TokenKind::LineContinuation => continue,
                TokenKind::EndOfFile => {
                    return None;
                }
                TokenKind::Whitespace => continue,
                TokenKind::Newline => Tok::Newline,
                TokenKind::Indent => Tok::Indent,
                TokenKind::Dedent => Tok::Dedent,
                TokenKind::Lpar => Tok::Lpar,
                TokenKind::Rpar => Tok::Rpar,
                TokenKind::Lsqb => Tok::Lsqb,
                TokenKind::Rsqb => Tok::Rsqb,
                TokenKind::Colon => Tok::Colon,
                TokenKind::Comma => Tok::Comma,
                TokenKind::Semi => Tok::Semi,
                TokenKind::Plus => Tok::Plus,
                TokenKind::Minus => Tok::Minus,
                TokenKind::Star => Tok::Star,
                TokenKind::Slash => Tok::Slash,
                TokenKind::Vbar => Tok::Vbar,
                TokenKind::Amper => Tok::Amper,
                TokenKind::Less => Tok::Less,
                TokenKind::Greater => Tok::Greater,
                TokenKind::Equal => Tok::Equal,
                TokenKind::Dot => Tok::Dot,
                TokenKind::Percent => Tok::Percent,
                TokenKind::Lbrace => Tok::Lbrace,
                TokenKind::Rbrace => Tok::Rbrace,
                TokenKind::EqEqual => Tok::EqEqual,
                TokenKind::NotEqual => Tok::NotEqual,
                TokenKind::LessEqual => Tok::LessEqual,
                TokenKind::GreaterEqual => Tok::GreaterEqual,
                TokenKind::Tilde => Tok::Tilde,
                TokenKind::CircumFlex => Tok::CircumFlex,
                TokenKind::LeftShift => Tok::LeftShift,
                TokenKind::RightShift => Tok::RightShift,
                TokenKind::DoubleStar => Tok::DoubleStar,
                TokenKind::DoubleStarEqual => Tok::DoubleStarEqual,
                TokenKind::PlusEqual => Tok::PlusEqual,
                TokenKind::MinusEqual => Tok::MinusEqual,
                TokenKind::StarEqual => Tok::StarEqual,
                TokenKind::SlashEqual => Tok::SlashEqual,
                TokenKind::PercentEqual => Tok::PercentEqual,
                TokenKind::AmperEqual => Tok::AmperEqual,
                TokenKind::VbarEqual => Tok::VbarEqual,
                TokenKind::CircumflexEqual => Tok::CircumflexEqual,
                TokenKind::LeftShiftEqual => Tok::LeftShiftEqual,
                TokenKind::RightShiftEqual => Tok::RightShiftEqual,
                TokenKind::DoubleSlash => Tok::DoubleSlash,
                TokenKind::DoubleSlashEqual => Tok::DoubleSlashEqual,
                TokenKind::ColonEqual => Tok::ColonEqual,
                TokenKind::At => Tok::At,
                TokenKind::AtEqual => Tok::AtEqual,
                TokenKind::Rarrow => Tok::Rarrow,
                TokenKind::Ellipsis => Tok::Ellipsis,
                TokenKind::False => Tok::False,
                TokenKind::None => Tok::None,
                TokenKind::True => Tok::True,
                TokenKind::And => Tok::And,
                TokenKind::As => Tok::As,
                TokenKind::Assert => Tok::Assert,
                TokenKind::Async => Tok::Async,
                TokenKind::Await => Tok::Await,
                TokenKind::Break => Tok::Break,
                TokenKind::Class => Tok::Class,
                TokenKind::Continue => Tok::Continue,
                TokenKind::Def => Tok::Def,
                TokenKind::Del => Tok::Del,
                TokenKind::Elif => Tok::Elif,
                TokenKind::Else => Tok::Else,
                TokenKind::Except => Tok::Except,
                TokenKind::Finally => Tok::Finally,
                TokenKind::For => Tok::For,
                TokenKind::From => Tok::From,
                TokenKind::Global => Tok::Global,
                TokenKind::If => Tok::If,
                TokenKind::Import => Tok::Import,
                TokenKind::In => Tok::In,
                TokenKind::Is => Tok::Is,
                TokenKind::Lambda => Tok::Lambda,
                TokenKind::Nonlocal => Tok::Nonlocal,
                TokenKind::Not => Tok::Not,
                TokenKind::Or => Tok::Or,
                TokenKind::Pass => Tok::Pass,
                TokenKind::Raise => Tok::Raise,
                TokenKind::Return => Tok::Return,
                TokenKind::Try => Tok::Try,
                TokenKind::While => Tok::While,
                TokenKind::With => Tok::With,
                TokenKind::Yield => Tok::Yield,
                TokenKind::Match => Tok::Match,
                TokenKind::Case => Tok::Case,
                TokenKind::Type => Tok::Type,
                TokenKind::Bogus => {
                    return Some(Err(LexicalError::new(
                        LexicalErrorType::OtherError("Compat error".to_string()),
                        start,
                    )))
                }
            };

            break (tok, TextRange::new(start, self.offset));
        };

        Some(Ok((tok, range)))
    }
}

impl<'a> FusedIterator for CompatAdapter<'a> {}
