//! Contains the interface to the Python ruff_python_parser.
//!
//! Functions in this module can be used to parse Python code into an [Abstract Syntax Tree]
//! (AST) that is then transformed into bytecode.
//!
//! There are three ways to parse Python code corresponding to the different [`Mode`]s
//! defined in the [`mode`] module.
//!
//! All functions return a [`Result`](std::result::Result) containing the parsed AST or
//! a [`ParseError`] if parsing failed.
//!
//! [Abstract Syntax Tree]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
//! [`Mode`]: crate::mode

use std::{fmt, iter};

use itertools::Itertools;
pub(super) use lalrpop_util::ParseError as LalrpopError;
use ruff_text_size::TextSize;

use crate::lexer::{lex, lex_starts_at};
use crate::{
    lexer::{self, LexResult, LexicalError, LexicalErrorType},
    python,
    token::Tok,
    Mode,
};
use ruff_python_ast::{self as ast, Ranged};

/// Parse Python code string to implementor's type.
///
/// # Example
///
/// For example, parsing a simple function definition and a call to that function:
///
/// ```
/// use ruff_python_parser::{self as parser, Parse};
/// use ruff_python_ast as ast;
/// let source = r#"
/// def foo():
///    return 42
///
/// print(foo())
/// "#;
/// let program = ast::Suite::parse(source, "<embedded>");
/// assert!(program.is_ok());
/// ```
///
/// Parsing a single expression denoting the addition of two numbers, but this time specifying a different,
/// somewhat silly, location:
///
/// ```
/// # use ruff_text_size::TextSize;
/// # use ruff_python_ast as ast;
/// # use ruff_python_parser::{self as parser, Parse};
///
/// let expr = ast::Expr::parse_starts_at("1 + 2", "<embedded>", TextSize::from(400));
/// assert!(expr.is_ok());
pub trait Parse
where
    Self: Sized,
{
    const MODE: Mode;

    fn parse(source: &str, source_path: &str) -> Result<Self, ParseError> {
        let tokens = lex(source, Self::MODE);

        Self::parse_tokens(tokens, source_path)
    }

    fn parse_without_path(source: &str) -> Result<Self, ParseError> {
        Self::parse(source, "<unknown>")
    }

    fn parse_starts_at(
        source: &str,
        source_path: &str,
        offset: TextSize,
    ) -> Result<Self, ParseError> {
        let tokens = lex_starts_at(source, Self::MODE, offset);

        Self::parse_tokens(tokens, source_path)
    }

    fn parse_tokens(
        lxr: impl IntoIterator<Item = LexResult>,
        source_path: &str,
    ) -> Result<Self, ParseError>;
}

impl Parse for ast::ModModule {
    const MODE: Mode = Mode::Module;

    fn parse_tokens(
        lxr: impl IntoIterator<Item = LexResult>,
        source_path: &str,
    ) -> Result<Self, ParseError> {
        match parse_tokens(lxr, Mode::Module, source_path)? {
            ast::Mod::Module(m) => Ok(m),
            _ => unreachable!("Mode::Module doesn't return other variant"),
        }
    }
}

impl Parse for ast::ModExpression {
    const MODE: Mode = Mode::Expression;

    fn parse_tokens(
        lxr: impl IntoIterator<Item = LexResult>,
        source_path: &str,
    ) -> Result<Self, ParseError> {
        match parse_tokens(lxr, Mode::Expression, source_path)? {
            ast::Mod::Expression(m) => Ok(m),
            _ => unreachable!("Mode::Module doesn't return other variant"),
        }
    }
}

impl Parse for ast::ModInteractive {
    const MODE: Mode = Mode::Interactive;
    fn parse_tokens(
        lxr: impl IntoIterator<Item = LexResult>,
        source_path: &str,
    ) -> Result<Self, ParseError> {
        match parse_tokens(lxr, Mode::Interactive, source_path)? {
            ast::Mod::Interactive(m) => Ok(m),
            _ => unreachable!("Mode::Module doesn't return other variant"),
        }
    }
}

impl Parse for ast::Suite {
    const MODE: Mode = Mode::Module;

    fn parse_tokens(
        lxr: impl IntoIterator<Item = LexResult>,
        source_path: &str,
    ) -> Result<Self, ParseError> {
        Ok(ast::ModModule::parse_tokens(lxr, source_path)?.body)
    }
}

impl Parse for ast::Stmt {
    const MODE: Mode = Mode::Module;

    fn parse_tokens(
        lxr: impl IntoIterator<Item = LexResult>,
        source_path: &str,
    ) -> Result<Self, ParseError> {
        let mut statements = ast::ModModule::parse_tokens(lxr, source_path)?.body;
        let statement = match statements.len() {
            0 => {
                return Err(ParseError {
                    error: ParseErrorType::Eof,
                    offset: TextSize::default(),
                    source_path: source_path.to_owned(),
                })
            }
            1 => statements.pop().unwrap(),
            _ => {
                return Err(ParseError {
                    error: ParseErrorType::InvalidToken,
                    offset: statements[1].range().start(),
                    source_path: source_path.to_owned(),
                })
            }
        };
        Ok(statement)
    }
}

impl Parse for ast::Expr {
    const MODE: Mode = Mode::Expression;

    fn parse_tokens(
        lxr: impl IntoIterator<Item = LexResult>,
        source_path: &str,
    ) -> Result<Self, ParseError> {
        Ok(*ast::ModExpression::parse_tokens(lxr, source_path)?.body)
    }
}

impl Parse for ast::Identifier {
    const MODE: Mode = Mode::Expression;

    fn parse_tokens(
        lxr: impl IntoIterator<Item = LexResult>,
        source_path: &str,
    ) -> Result<Self, ParseError> {
        let expr = ast::Expr::parse_tokens(lxr, source_path)?;
        match expr {
            ast::Expr::Name(name) => {
                let range = name.range();
                Ok(ast::Identifier::new(name.id, range))
            }
            expr => Err(ParseError {
                error: ParseErrorType::InvalidToken,
                offset: expr.range().start(),
                source_path: source_path.to_owned(),
            }),
        }
    }
}

impl Parse for ast::Constant {
    const MODE: Mode = Mode::Expression;

    fn parse_tokens(
        lxr: impl IntoIterator<Item = LexResult>,
        source_path: &str,
    ) -> Result<Self, ParseError> {
        let expr = ast::Expr::parse_tokens(lxr, source_path)?;
        match expr {
            ast::Expr::Constant(c) => Ok(c.value),
            expr => Err(ParseError {
                error: ParseErrorType::InvalidToken,
                offset: expr.range().start(),
                source_path: source_path.to_owned(),
            }),
        }
    }
}

/// Parse a full Python program usually consisting of multiple lines.
///
/// This is a convenience function that can be used to parse a full Python program without having to
/// specify the [`Mode`] or the location. It is probably what you want to use most of the time.
///
/// # Example
///
/// For example, parsing a simple function definition and a call to that function:
///
/// ```
/// use ruff_python_parser as parser;
/// let source = r#"
/// def foo():
///    return 42
///
/// print(foo())
/// "#;
/// let program = parser::parse_program(source, "<embedded>");
/// assert!(program.is_ok());
/// ```
#[deprecated = "Use ruff_python_ast::Suite::parse from rustpython_parser::Parse trait."]
pub fn parse_program(source: &str, source_path: &str) -> Result<ast::Suite, ParseError> {
    parse(source, Mode::Module, source_path).map(|top| match top {
        ast::Mod::Module(ast::ModModule { body, .. }) => body,
        _ => unreachable!(),
    })
}

/// Parses a single Python expression.
///
/// This convenience function can be used to parse a single expression without having to
/// specify the Mode or the location.
///
/// # Example
///
/// For example, parsing a single expression denoting the addition of two numbers:
///
///  ```
/// use ruff_python_parser as parser;
/// let expr = parser::parse_expression("1 + 2", "<embedded>");
///
/// assert!(expr.is_ok());
///
/// ```
#[deprecated = "Use ruff_python_ast::Expr::parse from rustpython_parser::Parse trait."]
pub fn parse_expression(source: &str, path: &str) -> Result<ast::Expr, ParseError> {
    ast::Expr::parse(source, path)
}

/// Parses a Python expression from a given location.
///
/// This function allows to specify the location of the expression in the source code, other than
/// that, it behaves exactly like [`parse_expression`].
///
/// # Example
///
/// Parsing a single expression denoting the addition of two numbers, but this time specifying a different,
/// somewhat silly, location:
///
/// ```
/// use ruff_python_parser::{parse_expression_starts_at};
/// # use ruff_text_size::TextSize;
///
/// let expr = parse_expression_starts_at("1 + 2", "<embedded>", TextSize::from(400));
/// assert!(expr.is_ok());
/// ```
#[deprecated = "Use ruff_python_ast::Expr::parse_starts_at from rustpython_parser::Parse trait."]
pub fn parse_expression_starts_at(
    source: &str,
    path: &str,
    offset: TextSize,
) -> Result<ast::Expr, ParseError> {
    ast::Expr::parse_starts_at(source, path, offset)
}

/// Parse the given Python source code using the specified [`Mode`].
///
/// This function is the most general function to parse Python code. Based on the [`Mode`] supplied,
/// it can be used to parse a single expression, a full Python program, an interactive expression
/// or a Python program containing Jupyter magics.
///
/// # Example
///
/// If we want to parse a simple expression, we can use the [`Mode::Expression`] mode during
/// parsing:
///
/// ```
/// use ruff_python_parser::{Mode, parse};
///
/// let expr = parse("1 + 2", Mode::Expression, "<embedded>");
/// assert!(expr.is_ok());
/// ```
///
/// Alternatively, we can parse a full Python program consisting of multiple lines:
///
/// ```
/// use ruff_python_parser::{Mode, parse};
///
/// let source = r#"
/// class Greeter:
///
///   def greet(self):
///    print("Hello, world!")
/// "#;
/// let program = parse(source, Mode::Module, "<embedded>");
/// assert!(program.is_ok());
/// ```
///
/// Additionally, we can parse a Python program containing Jupyter magics:
///
/// ```
/// use ruff_python_parser::{Mode, parse};
///
/// let source = r#"
/// %timeit 1 + 2
/// ?str.replace
/// !ls
/// "#;
/// let program = parse(source, Mode::Jupyter, "<embedded>");
/// assert!(program.is_ok());
/// ```
pub fn parse(source: &str, mode: Mode, source_path: &str) -> Result<ast::Mod, ParseError> {
    parse_starts_at(source, mode, source_path, TextSize::default())
}

/// Parse the given Python source code using the specified [`Mode`] and [`Location`].
///
/// This function allows to specify the location of the the source code, other than
/// that, it behaves exactly like [`parse`].
///
/// # Example
///
/// ```
/// # use ruff_text_size::TextSize;
/// use ruff_python_parser::{Mode, parse_starts_at};
///
/// let source = r#"
/// def fib(i):
///    a, b = 0, 1
///    for _ in range(i):
///       a, b = b, a + b
///    return a
///
/// print(fib(42))
/// "#;
/// let program = parse_starts_at(source, Mode::Module, "<embedded>", TextSize::from(0));
/// assert!(program.is_ok());
/// ```
pub fn parse_starts_at(
    source: &str,
    mode: Mode,
    source_path: &str,
    offset: TextSize,
) -> Result<ast::Mod, ParseError> {
    let lxr = lexer::lex_starts_at(source, mode, offset);
    parse_tokens(lxr, mode, source_path)
}

/// Parse an iterator of [`LexResult`]s using the specified [`Mode`].
///
/// This could allow you to perform some preprocessing on the tokens before parsing them.
///
/// # Example
///
/// As an example, instead of parsing a string, we can parse a list of tokens after we generate
/// them using the [`lexer::lex`] function:
///
/// ```
/// use ruff_python_parser::{lexer::lex, Mode, parse_tokens};
///
/// let expr = parse_tokens(lex("1 + 2", Mode::Expression), Mode::Expression, "<embedded>");
/// assert!(expr.is_ok());
/// ```
pub fn parse_tokens(
    lxr: impl IntoIterator<Item = LexResult>,
    mode: Mode,
    source_path: &str,
) -> Result<ast::Mod, ParseError> {
    let lxr = lxr.into_iter();

    parse_filtered_tokens(
        lxr.filter_ok(|(tok, _)| !matches!(tok, Tok::Comment { .. } | Tok::NonLogicalNewline)),
        mode,
        source_path,
    )
}

fn parse_filtered_tokens(
    lxr: impl IntoIterator<Item = LexResult>,
    mode: Mode,
    source_path: &str,
) -> Result<ast::Mod, ParseError> {
    let marker_token = (Tok::start_marker(mode), Default::default());
    let lexer = iter::once(Ok(marker_token)).chain(lxr);
    python::TopParser::new()
        .parse(
            mode,
            lexer
                .into_iter()
                .map_ok(|(t, range)| (range.start(), t, range.end())),
        )
        .map_err(|e| parse_error_from_lalrpop(e, source_path))
}

/// Represents represent errors that occur during parsing and are
/// returned by the `parse_*` functions.

#[derive(Debug, PartialEq)]
pub struct ParseError {
    pub error: ParseErrorType,
    pub offset: TextSize,
    pub source_path: String,
}

impl std::ops::Deref for ParseError {
    type Target = ParseErrorType;

    fn deref(&self) -> &Self::Target {
        &self.error
    }
}

impl std::error::Error for ParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{} at byte offset {}",
            &self.error,
            u32::from(self.offset)
        )
    }
}

impl ParseError {
    pub fn error(self) -> ParseErrorType {
        self.error
    }
}

/// Represents the different types of errors that can occur during parsing.
#[derive(Debug, PartialEq)]
pub enum ParseErrorType {
    /// Parser encountered an unexpected end of input
    Eof,
    /// Parser encountered an extra token
    ExtraToken(Tok),
    /// Parser encountered an invalid token
    InvalidToken,
    /// Parser encountered an unexpected token
    UnrecognizedToken(Tok, Option<String>),
    // Maps to `User` type from `lalrpop-util`
    /// Parser encountered an error during lexing.
    Lexical(LexicalErrorType),
}

impl std::error::Error for ParseErrorType {}

// Convert `lalrpop_util::ParseError` to our internal type
fn parse_error_from_lalrpop(
    err: LalrpopError<TextSize, Tok, LexicalError>,
    source_path: &str,
) -> ParseError {
    let source_path = source_path.to_owned();

    match err {
        // TODO: Are there cases where this isn't an EOF?
        LalrpopError::InvalidToken { location } => ParseError {
            error: ParseErrorType::Eof,
            offset: location,
            source_path,
        },
        LalrpopError::ExtraToken { token } => ParseError {
            error: ParseErrorType::ExtraToken(token.1),
            offset: token.0,
            source_path,
        },
        LalrpopError::User { error } => ParseError {
            error: ParseErrorType::Lexical(error.error),
            offset: error.location,
            source_path,
        },
        LalrpopError::UnrecognizedToken { token, expected } => {
            // Hacky, but it's how CPython does it. See PyParser_AddToken,
            // in particular "Only one possible expected token" comment.
            let expected = (expected.len() == 1).then(|| expected[0].clone());
            ParseError {
                error: ParseErrorType::UnrecognizedToken(token.1, expected),
                offset: token.0,
                source_path,
            }
        }
        LalrpopError::UnrecognizedEof { location, expected } => {
            // This could be an initial indentation error that we should ignore
            let indent_error = expected == ["Indent"];
            if indent_error {
                ParseError {
                    error: ParseErrorType::Lexical(LexicalErrorType::IndentationError),
                    offset: location,
                    source_path,
                }
            } else {
                ParseError {
                    error: ParseErrorType::Eof,
                    offset: location,
                    source_path,
                }
            }
        }
    }
}

impl std::fmt::Display for ParseErrorType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            ParseErrorType::Eof => write!(f, "Got unexpected EOF"),
            ParseErrorType::ExtraToken(ref tok) => write!(f, "Got extraneous token: {tok:?}"),
            ParseErrorType::InvalidToken => write!(f, "Got invalid token"),
            ParseErrorType::UnrecognizedToken(ref tok, ref expected) => {
                if *tok == Tok::Indent {
                    write!(f, "unexpected indent")
                } else if expected.as_deref() == Some("Indent") {
                    write!(f, "expected an indented block")
                } else {
                    write!(f, "invalid syntax. Got unexpected token {tok}")
                }
            }
            ParseErrorType::Lexical(ref error) => write!(f, "{error}"),
        }
    }
}

impl ParseErrorType {
    /// Returns true if the error is an indentation error.
    pub fn is_indentation_error(&self) -> bool {
        match self {
            ParseErrorType::Lexical(LexicalErrorType::IndentationError) => true,
            ParseErrorType::UnrecognizedToken(token, expected) => {
                *token == Tok::Indent || expected.clone() == Some("Indent".to_owned())
            }
            _ => false,
        }
    }

    /// Returns true if the error is a tab error.
    pub fn is_tab_error(&self) -> bool {
        matches!(
            self,
            ParseErrorType::Lexical(LexicalErrorType::TabError)
                | ParseErrorType::Lexical(LexicalErrorType::TabsAfterSpaces)
        )
    }
}

include!("gen/parse.rs");

#[cfg(test)]
mod tests {
    use crate::Parse;
    use insta::assert_debug_snapshot;
    use ruff_python_ast as ast;

    use super::*;

    #[test]
    fn test_parse_empty() {
        let parse_ast = ast::Suite::parse("", "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_string() {
        let source = "'Hello world'";
        let parse_ast = ast::Suite::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_f_string() {
        let source = "f'Hello world'";
        let parse_ast = ast::Suite::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_print_hello() {
        let source = "print('Hello world')";
        let parse_ast = ast::Suite::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_print_2() {
        let source = "print('Hello world', 2)";
        let parse_ast = ast::Suite::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_kwargs() {
        let source = "my_func('positional', keyword=2)";
        let parse_ast = ast::Suite::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_if_elif_else() {
        let source = "if 1: 10\nelif 2: 20\nelse: 30";
        let parse_ast = ast::Suite::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_lambda() {
        let source = "lambda x, y: x * y"; // lambda(x, y): x * y";
        let parse_ast = ast::Suite::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_lambda_no_args() {
        let source = "lambda: 1";
        let parse_ast = ast::Suite::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_tuples() {
        let source = "a, b = 4, 5";

        insta::assert_debug_snapshot!(ast::Suite::parse(source, "<test>").unwrap());
    }

    #[test]
    fn test_parse_class() {
        let source = "\
class Foo(A, B):
 def __init__(self):
  pass
 def method_with_default(self, arg='default'):
  pass
";
        insta::assert_debug_snapshot!(ast::Suite::parse(source, "<test>").unwrap());
    }

    #[test]
    fn test_parse_class_generic_types() {
        let source = "\
# TypeVar
class Foo[T](): ...

# TypeVar with bound
class Foo[T: str](): ...

# TypeVar with tuple bound
class Foo[T: (str, bytes)](): ...

# Multiple TypeVar
class Foo[T, U](): ...

# Trailing comma
class Foo[T, U,](): ...

# TypeVarTuple
class Foo[*Ts](): ...

# ParamSpec
class Foo[**P](): ...

# Mixed types
class Foo[X, Y: str, *U, **P]():
  pass
";
        insta::assert_debug_snapshot!(ast::Suite::parse(source, "<test>").unwrap());
    }
    #[test]
    fn test_parse_function_definition() {
        let source = "\
def func(a):
    ...

def func[T](a: T) -> T:
    ...

def func[T: str](a: T) -> T:
    ...

def func[T: (str, bytes)](a: T) -> T:
    ...

def func[*Ts](*a: *Ts):
    ...

def func[**P](*args: P.args, **kwargs: P.kwargs):
    ...

def func[T, U: str, *Ts, **P]():
    pass
  ";
        insta::assert_debug_snapshot!(ast::Suite::parse(source, "<test>").unwrap());
    }

    #[test]
    fn test_parse_dict_comprehension() {
        let source = "{x1: x2 for y in z}";
        let parse_ast = ast::Expr::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_list_comprehension() {
        let source = "[x for y in z]";
        let parse_ast = ast::Expr::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_double_list_comprehension() {
        let source = "[x for y, y2 in z for a in b if a < 5 if a > 10]";
        let parse_ast = ast::Expr::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_generator_comprehension() {
        let source = "(x for y in z)";
        let parse_ast = ast::Expr::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_named_expression_generator_comprehension() {
        let source = "(x := y + 1 for y in z)";
        let parse_ast = ast::Expr::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_if_else_generator_comprehension() {
        let source = "(x if y else y for y in z)";
        let parse_ast = ast::Expr::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_bool_op_or() {
        let source = "x or y";
        let parse_ast = ast::Expr::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_bool_op_and() {
        let source = "x and y";
        let parse_ast = ast::Expr::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_slice() {
        let source = "x[1:2:3]";
        let parse_ast = ast::Expr::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_with_statement() {
        let source = "\
with 0: pass
with 0 as x: pass
with 0, 1: pass
with 0 as x, 1 as y: pass
with 0 if 1 else 2: pass
with 0 if 1 else 2 as x: pass
with (): pass
with () as x: pass
with (0): pass
with (0) as x: pass
with (0,): pass
with (0,) as x: pass
with (0, 1): pass
with (0, 1) as x: pass
with (*a,): pass
with (*a,) as x: pass
with (0, *a): pass
with (0, *a) as x: pass
with (a := 0): pass
with (a := 0) as x: pass
with (a := 0, b := 1): pass
with (a := 0, b := 1) as x: pass
with (0 as a): pass
with (0 as a,): pass
with (0 as a, 1 as b): pass
with (0 as a, 1 as b,): pass
";
        insta::assert_debug_snapshot!(ast::Suite::parse(source, "<test>").unwrap());
    }

    #[test]
    fn test_with_statement_invalid() {
        for source in [
            "with 0,: pass",
            "with 0 as x,: pass",
            "with 0 as *x: pass",
            "with *a: pass",
            "with *a as x: pass",
            "with (*a): pass",
            "with (*a) as x: pass",
            "with *a, 0 as x: pass",
            "with (*a, 0 as x): pass",
            "with 0 as x, *a: pass",
            "with (0 as x, *a): pass",
            "with (0 as x) as y: pass",
            "with (0 as x), 1: pass",
            "with ((0 as x)): pass",
            "with a := 0 as x: pass",
            "with (a := 0 as x): pass",
        ] {
            assert!(ast::Suite::parse(source, "<test>").is_err());
        }
    }

    #[test]
    fn test_star_index() {
        let source = "\
array_slice = array[0, *indexes, -1]
array[0, *indexes, -1] = array_slice
array[*indexes_to_select, *indexes_to_select]
array[3:5, *indexes_to_select]
";
        let parse_ast = ast::Suite::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_generator_expression_argument() {
        let source = r#"' '.join(
    sql
    for sql in (
        "LIMIT %d" % limit if limit else None,
        ("OFFSET %d" % offset) if offset else None,
    )
)"#;
        let parse_ast = ast::Expr::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_try() {
        let parse_ast = ast::Suite::parse(
            r#"try:
    raise ValueError(1)
except TypeError as e:
    print(f'caught {type(e)}')
except OSError as e:
    print(f'caught {type(e)}')"#,
            "<test>",
        )
        .unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_try_star() {
        let parse_ast = ast::Suite::parse(
            r#"try:
    raise ExceptionGroup("eg",
        [ValueError(1), TypeError(2), OSError(3), OSError(4)])
except* TypeError as e:
    print(f'caught {type(e)} with nested {e.exceptions}')
except* OSError as e:
    print(f'caught {type(e)} with nested {e.exceptions}')"#,
            "<test>",
        )
        .unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_dict_unpacking() {
        let parse_ast = ast::Expr::parse(r#"{"a": "b", **c, "d": "e"}"#, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_modes() {
        let source = "a[0][1][2][3][4]";

        assert!(parse(source, Mode::Expression, "<embedded>").is_ok());
        assert!(parse(source, Mode::Module, "<embedded>").is_ok());
        assert!(parse(source, Mode::Interactive, "<embedded>").is_ok());
    }

    #[test]
    fn test_parse_type_declaration() {
        let source = r#"
type X = int
type X = int | str
type X = int | "ForwardRefY"
type X[T] = T | list[X[T]]  # recursive
type X[T] = int
type X[T] = list[T] | set[T]
type X[T, *Ts, **P] = (T, Ts, P)
type X[T: int, *Ts, **P] = (T, Ts, P)
type X[T: (int, str), *Ts, **P] = (T, Ts, P)

# soft keyword as alias name
type type = int  
type match = int
type case = int

# soft keyword as value
type foo = type
type foo = match
type foo = case

# multine definitions
type \
	X = int
type X \
	= int
type X = \
	int
type X = (
    int
)
type \
    X[T] = T
type X \
    [T] = T
type X[T] \
    = T
"#;
        insta::assert_debug_snapshot!(ast::Suite::parse(source, "<test>").unwrap());
    }

    #[test]
    fn test_type_as_identifier() {
        let source = r#"\
type *a + b, c   # ((type * a) + b), c
type *(a + b), c   # (type * (a + b)), c
type (*a + b, c)   # type ((*(a + b)), c)
type -a * b + c   # (type - (a * b)) + c
type -(a * b) + c   # (type - (a * b)) + c
type (-a) * b + c   # (type (-(a * b))) + c
type ().a   # (type()).a
type (()).a   # (type(())).a
type ((),).a   # (type(())).a
type [a].b   # (type[a]).b
type [a,].b   # (type[(a,)]).b  (not (type[a]).b)
type [(a,)].b   # (type[(a,)]).b
type()[a:
    b]  # (type())[a: b]
if type := 1: pass
type = lambda query: query == event
print(type(12))
type(type)
a = (
	type in C
)
a = (
	type(b)
)
type (
	X = int
)
type = 1
type = x = 1
x = type = 1
"#;
        insta::assert_debug_snapshot!(ast::Suite::parse(source, "<test>").unwrap());
    }

    #[test]
    fn numeric_literals() {
        let source = r#"x = 123456789
x = 123456
x = .1
x = 1.
x = 1E+1
x = 1E-1
x = 1.000_000_01
x = 123456789.123456789
x = 123456789.123456789E123456789
x = 123456789E123456789
x = 123456789J
x = 123456789.123456789J
x = 0XB1ACC
x = 0B1011
x = 0O777
x = 0.000000006
x = 10000
x = 133333
"#;

        insta::assert_debug_snapshot!(ast::Suite::parse(source, "<test>").unwrap());
    }

    #[test]
    fn numeric_literals_attribute_access() {
        let source = r#"x = .1.is_integer()
x = 1. .imag
x = 1E+1.imag
x = 1E-1.real
x = 123456789.123456789.hex()
x = 123456789.123456789E123456789 .real
x = 123456789E123456789 .conjugate()
x = 123456789J.real
x = 123456789.123456789J.__add__(0b1011.bit_length())
x = 0XB1ACC.conjugate()
x = 0B1011 .conjugate()
x = 0O777 .real
x = 0.000000006  .hex()
x = -100.0000J

if 10 .real:
    ...

y = 100[no]
y = 100(no)
"#;
        assert_debug_snapshot!(ast::Suite::parse(source, "<test>").unwrap())
    }

    #[test]
    fn test_match_as_identifier() {
        let source = r#"\
match *a + b, c   # ((match * a) + b), c
match *(a + b), c   # (match * (a + b)), c
match (*a + b, c)   # match ((*(a + b)), c)
match -a * b + c   # (match - (a * b)) + c
match -(a * b) + c   # (match - (a * b)) + c
match (-a) * b + c   # (match (-(a * b))) + c
match ().a   # (match()).a
match (()).a   # (match(())).a
match ((),).a   # (match(())).a
match [a].b   # (match[a]).b
match [a,].b   # (match[(a,)]).b  (not (match[a]).b)
match [(a,)].b   # (match[(a,)]).b
match()[a:
    b]  # (match())[a: b]
if match := 1: pass
match match:
    case 1: pass
    case 2:
        pass
match = lambda query: query == event
print(match(12))
"#;
        insta::assert_debug_snapshot!(ast::Suite::parse(source, "<test>").unwrap());
    }

    #[test]
    fn test_patma() {
        let source = r#"# Cases sampled from Lib/test/test_patma.py

# case test_patma_098
match x:
    case -0j:
        y = 0
# case test_patma_142
match x:
    case bytes(z):
        y = 0
# case test_patma_073
match x:
    case 0 if 0:
        y = 0
    case 0 if 1:
        y = 1
# case test_patma_006
match 3:
    case 0 | 1 | 2 | 3:
        x = True
# case test_patma_049
match x:
    case [0, 1] | [1, 0]:
        y = 0
# case black_check_sequence_then_mapping
match x:
    case [*_]:
        return "seq"
    case {}:
        return "map"
# case test_patma_035
match x:
    case {0: [1, 2, {}]}:
        y = 0
    case {0: [1, 2, {}] | True} | {1: [[]]} | {0: [1, 2, {}]} | [] | "X" | {}:
        y = 1
    case []:
        y = 2
# case test_patma_107
match x:
    case 0.25 + 1.75j:
        y = 0
# case test_patma_097
match x:
    case -0j:
        y = 0
# case test_patma_007
match 4:
    case 0 | 1 | 2 | 3:
        x = True
# case test_patma_154
match x:
    case 0 if x:
        y = 0
# case test_patma_134
match x:
    case {1: 0}:
        y = 0
    case {0: 0}:
        y = 1
    case {**z}:
        y = 2
# case test_patma_185
match Seq():
    case [*_]:
        y = 0
# case test_patma_063
match x:
    case 1:
        y = 0
    case 1:
        y = 1
# case test_patma_248
match x:
    case {"foo": bar}:
        y = bar
# case test_patma_019
match (0, 1, 2):
    case [0, 1, *x, 2]:
        y = 0
# case test_patma_052
match x:
    case [0]:
        y = 0
    case [1, 0] if (x := x[:0]):
        y = 1
    case [1, 0]:
        y = 2
# case test_patma_191
match w:
    case [x, y, *_]:
        z = 0
# case test_patma_110
match x:
    case -0.25 - 1.75j:
        y = 0
# case test_patma_151
match (x,):
    case [y]:
        z = 0
# case test_patma_114
match x:
    case A.B.C.D:
        y = 0
# case test_patma_232
match x:
    case None:
        y = 0
# case test_patma_058
match x:
    case 0:
        y = 0
# case test_patma_233
match x:
    case False:
        y = 0
# case test_patma_078
match x:
    case []:
        y = 0
    case [""]:
        y = 1
    case "":
        y = 2
# case test_patma_156
match x:
    case z:
        y = 0
# case test_patma_189
match w:
    case [x, y, *rest]:
        z = 0
# case test_patma_042
match x:
    case (0 as z) | (1 as z) | (2 as z) if z == x % 2:
        y = 0
# case test_patma_034
match x:
    case {0: [1, 2, {}]}:
        y = 0
    case {0: [1, 2, {}] | False} | {1: [[]]} | {0: [1, 2, {}]} | [] | "X" | {}:
        y = 1
    case []:
        y = 2
# case test_patma_123
match (0, 1, 2):
    case 0, *x:
        y = 0
# case test_patma_126
match (0, 1, 2):
    case *x, 2,:
        y = 0
# case test_patma_151
match x,:
    case y,:
        z = 0
# case test_patma_152
match w, x:
    case y, z:
        v = 0
# case test_patma_153
match w := x,:
    case y as v,:
        z = 0
"#;
        let parse_ast = ast::Suite::parse(source, "<test>").unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_match() {
        let parse_ast = ast::Suite::parse(
            r#"
match {"test": 1}:
    case {
        **rest,
    }:
        print(rest)
match {"label": "test"}:
    case {
        "label": str() | None as label,
    }:
        print(label)
match x:
    case [0, 1,]:
        y = 0
match x:
    case (0, 1,):
        y = 0
match x:
    case (0,):
        y = 0
"#,
            "<test>",
        )
        .unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_variadic_generics() {
        let parse_ast = ast::Suite::parse(
            r#"
def args_to_tuple(*args: *Ts) -> Tuple[*Ts]: ...
"#,
            "<test>",
        )
        .unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_parse_constant() {
        use num_traits::ToPrimitive;

        let c = ast::Constant::parse_without_path("'string'").unwrap();
        assert_eq!(c.str().unwrap(), "string");

        let c = ast::Constant::parse_without_path("10").unwrap();
        assert_eq!(c.int().unwrap().to_i32().unwrap(), 10);
    }

    #[test]
    fn test_parse_identifier() {
        let i = ast::Identifier::parse_without_path("test").unwrap();
        assert_eq!(i.as_str(), "test");
    }

    #[test]
    fn decorator_ranges() {
        let parse_ast = ast::Suite::parse(
            r#"
@my_decorator
def test():
    pass

@class_decorator
class Abcd:
    pass
"#
            .trim(),
            "<test>",
        )
        .unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_jupyter_magic() {
        let parse_ast = parse(
            r#"
# Normal Python code
(
    a
    %
    b
)

# Dynamic object info
??a.foo
?a.foo
?a.foo?
??a.foo()??

# Line magic
%timeit a = b
%timeit foo(b) % 3
%alias showPath pwd && ls -a
%timeit a =\
  foo(b); b = 2
%matplotlib --inline
%matplotlib \
    --inline

# System shell access
!pwd && ls -a | sed 's/^/\    /'
!pwd \
  && ls -a | sed 's/^/\\    /'
!!cd /Users/foo/Library/Application\ Support/

# Let's add some Python code to make sure that earlier escapes were handled
# correctly and that we didn't consume any of the following code as a result
# of the escapes.
def foo():
    return (
        a
        !=
        b
    )

# Transforms into `foo(..)`
/foo 1 2
;foo 1 2
,foo 1 2

# Indented magic
for a in range(5):
    !ls

p1 = !pwd
p2: str = !pwd
foo = %foo \
    bar

% foo
foo = %foo  # comment
"#
            .trim(),
            Mode::Jupyter,
            "<test>",
        )
        .unwrap();
        insta::assert_debug_snapshot!(parse_ast);
    }

    #[test]
    fn test_jupyter_magic_parse_error() {
        let source = r#"
a = 1
%timeit a == 1
    "#
        .trim();
        let lxr = lexer::lex_starts_at(source, Mode::Jupyter, TextSize::default());
        let parse_err = parse_tokens(lxr, Mode::Module, "<test>").unwrap_err();
        assert_eq!(
            parse_err.to_string(),
            "line magics are only allowed in Jupyter mode at byte offset 6".to_string()
        );
    }
}
