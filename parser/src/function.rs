// Contains functions that perform validation and parsing of arguments and parameters.
// Checks apply both to functions and to lambdas.
use crate::text_size::TextRange;
use crate::{
    ast,
    lexer::{LexicalError, LexicalErrorType},
    text_size::TextSize,
};
use rustc_hash::FxHashSet;
use rustpython_ast::Ranged;

pub(crate) struct ArgumentList {
    pub args: Vec<ast::Expr>,
    pub keywords: Vec<ast::Keyword>,
}

// Perform validation of function/lambda arguments in a function definition.
pub(crate) fn validate_arguments(arguments: &ast::Arguments) -> Result<(), LexicalError> {
    let mut all_arg_names = FxHashSet::with_hasher(Default::default());

    let posonlyargs = arguments.posonlyargs.iter();
    let args = arguments.args.iter();
    let kwonlyargs = arguments.kwonlyargs.iter();

    let vararg: Option<&ast::Arg> = arguments.vararg.as_deref();
    let kwarg: Option<&ast::Arg> = arguments.kwarg.as_deref();

    for arg in posonlyargs
        .chain(args)
        .chain(kwonlyargs)
        .map(|arg| &arg.def)
        .chain(vararg)
        .chain(kwarg)
    {
        let range = arg.range;
        let arg_name = arg.arg.as_str();
        if !all_arg_names.insert(arg_name) {
            return Err(LexicalError {
                error: LexicalErrorType::DuplicateArgumentError(arg_name.to_string()),
                location: range.start(),
            });
        }
    }

    Ok(())
}

pub(crate) fn validate_pos_params(
    args: &(Vec<ast::ArgWithDefault>, Vec<ast::ArgWithDefault>),
) -> Result<(), LexicalError> {
    let (posonlyargs, args) = args;
    #[allow(clippy::skip_while_next)]
    let first_invalid = posonlyargs
        .iter()
        .chain(args.iter()) // for all args
        .skip_while(|arg| arg.default.is_none()) // starting with args without default
        .skip_while(|arg| arg.default.is_some()) // and then args with default
        .next(); // there must not be any more args without default
    if let Some(invalid) = first_invalid {
        return Err(LexicalError {
            error: LexicalErrorType::DefaultArgumentError,
            location: invalid.def.range.start(),
        });
    }
    Ok(())
}

type FunctionArgument = (
    Option<(TextSize, TextSize, Option<ast::Identifier>)>,
    ast::Expr,
);

// Parse arguments as supplied during a function/lambda *call*.
pub(crate) fn parse_args(func_args: Vec<FunctionArgument>) -> Result<ArgumentList, LexicalError> {
    let mut args = vec![];
    let mut keywords = vec![];

    let mut keyword_names =
        FxHashSet::with_capacity_and_hasher(func_args.len(), Default::default());
    let mut double_starred = false;
    for (name, value) in func_args {
        match name {
            Some((start, end, name)) => {
                // Check for duplicate keyword arguments in the call.
                if let Some(keyword_name) = &name {
                    if keyword_names.contains(keyword_name) {
                        return Err(LexicalError {
                            error: LexicalErrorType::DuplicateKeywordArgumentError(
                                keyword_name.to_string(),
                            ),
                            location: start,
                        });
                    }

                    keyword_names.insert(keyword_name.clone());
                } else {
                    double_starred = true;
                }

                keywords.push(ast::Keyword {
                    arg: name.map(ast::Identifier::new),
                    value,
                    range: TextRange::new(start, end),
                });
            }
            None => {
                // Positional arguments mustn't follow keyword arguments.
                if !keywords.is_empty() && !is_starred(&value) {
                    return Err(LexicalError {
                        error: LexicalErrorType::PositionalArgumentError,
                        location: value.start(),
                    });
                // Allow starred arguments after keyword arguments but
                // not after double-starred arguments.
                } else if double_starred {
                    return Err(LexicalError {
                        error: LexicalErrorType::UnpackedArgumentError,
                        location: value.start(),
                    });
                }

                args.push(value);
            }
        }
    }
    Ok(ArgumentList { args, keywords })
}

// Check if an expression is a starred expression.
const fn is_starred(exp: &ast::Expr) -> bool {
    exp.is_starred_expr()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast, parser::ParseErrorType, Parse};

    macro_rules! function_and_lambda {
        ($($name:ident: $code:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let parse_ast = ast::Suite::parse($code, "<test>");
                    insta::assert_debug_snapshot!(parse_ast);
                }
            )*
        }
    }

    #[cfg(feature = "all-nodes-with-ranges")]
    function_and_lambda! {
        test_function_no_args_with_ranges: "def f(): pass",
        test_function_pos_args_with_ranges: "def f(a, b, c): pass",
    }

    #[cfg(feature = "all-nodes-with-ranges")]
    function_and_lambda! {
        test_function_no_args: "def f(): pass",
        test_function_pos_args: "def f(a, b, c): pass",
        test_function_pos_args_with_defaults: "def f(a, b=20, c=30): pass",
        test_function_kw_only_args: "def f(*, a, b, c): pass",
        test_function_kw_only_args_with_defaults: "def f(*, a, b=20, c=30): pass",
        test_function_pos_and_kw_only_args: "def f(a, b, c, *, d, e, f): pass",
        test_function_pos_and_kw_only_args_with_defaults: "def f(a, b, c, *, d, e=20, f=30): pass",
        test_function_pos_and_kw_only_args_with_defaults_and_varargs: "def f(a, b, c, *args, d, e=20, f=30): pass",
        test_function_pos_and_kw_only_args_with_defaults_and_varargs_and_kwargs: "def f(a, b, c, *args, d, e=20, f=30, **kwargs): pass",
        test_lambda_no_args: "lambda: 1",
        test_lambda_pos_args: "lambda a, b, c: 1",
        test_lambda_pos_args_with_defaults: "lambda a, b=20, c=30: 1",
        test_lambda_kw_only_args: "lambda *, a, b, c: 1",
        test_lambda_kw_only_args_with_defaults: "lambda *, a, b=20, c=30: 1",
        test_lambda_pos_and_kw_only_args: "lambda a, b, c, *, d, e: 0",
    }

    fn function_parse_error(src: &str) -> LexicalErrorType {
        let parse_ast = ast::Suite::parse(src, "<test>");
        parse_ast
            .map_err(|e| match e.error {
                ParseErrorType::Lexical(e) => e,
                _ => panic!("Expected LexicalError"),
            })
            .expect_err("Expected error")
    }

    macro_rules! function_and_lambda_error {
        ($($name:ident: $code:expr, $error:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let error = function_parse_error($code);
                    assert_eq!(error, $error);
                }
            )*
        }
    }

    function_and_lambda_error! {
        // Check definitions
        test_duplicates_f1: "def f(a, a): pass", LexicalErrorType::DuplicateArgumentError("a".to_string()),
        test_duplicates_f2: "def f(a, *, a): pass", LexicalErrorType::DuplicateArgumentError("a".to_string()),
        test_duplicates_f3: "def f(a, a=20): pass", LexicalErrorType::DuplicateArgumentError("a".to_string()),
        test_duplicates_f4: "def f(a, *a): pass", LexicalErrorType::DuplicateArgumentError("a".to_string()),
        test_duplicates_f5: "def f(a, *, **a): pass", LexicalErrorType::DuplicateArgumentError("a".to_string()),
        test_duplicates_l1: "lambda a, a: 1", LexicalErrorType::DuplicateArgumentError("a".to_string()),
        test_duplicates_l2: "lambda a, *, a: 1", LexicalErrorType::DuplicateArgumentError("a".to_string()),
        test_duplicates_l3: "lambda a, a=20: 1", LexicalErrorType::DuplicateArgumentError("a".to_string()),
        test_duplicates_l4: "lambda a, *a: 1", LexicalErrorType::DuplicateArgumentError("a".to_string()),
        test_duplicates_l5: "lambda a, *, **a: 1", LexicalErrorType::DuplicateArgumentError("a".to_string()),
        test_default_arg_error_f: "def f(a, b=20, c): pass", LexicalErrorType::DefaultArgumentError,
        test_default_arg_error_l: "lambda a, b=20, c: 1", LexicalErrorType::DefaultArgumentError,

        // Check some calls.
        test_positional_arg_error_f: "f(b=20, c)", LexicalErrorType::PositionalArgumentError,
        test_unpacked_arg_error_f: "f(**b, *c)", LexicalErrorType::UnpackedArgumentError,
        test_duplicate_kw_f1: "f(a=20, a=30)", LexicalErrorType::DuplicateKeywordArgumentError("a".to_string()),
    }
}
