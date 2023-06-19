# spell-checker:words dfn dfns

# ! /usr/bin/env python
"""Generate Rust code from an ASDL description."""

import re
import sys
import textwrap
from argparse import ArgumentParser
from pathlib import Path
from typing import Any, Dict, Optional

import asdl

TABSIZE = 4
AUTO_GEN_MESSAGE = "// File automatically generated by {}.\n\n"

BUILTIN_TYPE_NAMES = {
    "identifier": "Identifier",
    "string": "String",
    "int": "Int",
    "constant": "Constant",
}
assert BUILTIN_TYPE_NAMES.keys() == asdl.builtin_types

BUILTIN_INT_NAMES = {
    "simple": "bool",
    "is_async": "bool",
    "conversion": "ConversionFlag",
}

RENAME_MAP = {
    "cmpop": "cmp_op",
    "unaryop": "unary_op",
    "boolop": "bool_op",
    "excepthandler": "except_handler",
    "withitem": "with_item",
}

RUST_KEYWORDS = {
    "if",
    "while",
    "for",
    "return",
    "match",
    "try",
    "await",
    "yield",
    "in",
    "mod",
    "type",
}

attributes = [
    asdl.Field("int", "lineno"),
    asdl.Field("int", "col_offset"),
    asdl.Field("int", "end_lineno"),
    asdl.Field("int", "end_col_offset"),
]

ORIGINAL_NODE_WARNING = "NOTE: This type is different from original Python AST."

arg_with_default = asdl.Type(
    "arg_with_default",
    asdl.Product(
        [
            asdl.Field("arg", "def"),
            asdl.Field(
                "expr", "default", opt=True
            ),  # order is important for cost-free borrow!
        ],
    ),
)
arg_with_default.doc = f"""
An alternative type of AST `arg`. This is used for each function argument that might have a default value.
Used by `Arguments` original type.

{ORIGINAL_NODE_WARNING}
""".strip()

alt_arguments = asdl.Type(
    "alt:arguments",
    asdl.Product(
        [
            asdl.Field("arg_with_default", "posonlyargs", seq=True),
            asdl.Field("arg_with_default", "args", seq=True),
            asdl.Field("arg", "vararg", opt=True),
            asdl.Field("arg_with_default", "kwonlyargs", seq=True),
            asdl.Field("arg", "kwarg", opt=True),
        ]
    ),
)
alt_arguments.doc = f"""
An alternative type of AST `arguments`. This is parser-friendly and human-friendly definition of function arguments.
This form also has advantage to implement pre-order traverse.
`defaults` and `kw_defaults` fields are removed and the default values are placed under each `arg_with_default` typed argument.
`vararg` and `kwarg` are still typed as `arg` because they never can have a default value.

The matching Python style AST type is [PythonArguments]. While [PythonArguments] has ordered `kwonlyargs` fields by
default existence, [Arguments] has location-ordered kwonlyargs fields.

{ORIGINAL_NODE_WARNING}
""".strip()

# Must be used only for rust types, not python types
CUSTOM_TYPES = [
    alt_arguments,
    arg_with_default,
]

CUSTOM_REPLACEMENTS = {
    "arguments": alt_arguments,
}
CUSTOM_ATTACHMENTS = [
    arg_with_default,
]


def maybe_custom(type):
    return CUSTOM_REPLACEMENTS.get(type.name, type)


def rust_field_name(name):
    name = rust_type_name(name)
    return re.sub(r"(?<!^)(?=[A-Z])", "_", name).lower()


def rust_type_name(name):
    """Return a string for the C name of the type.

    This function special cases the default types provided by asdl.
    """
    name = RENAME_MAP.get(name, name)
    if name in asdl.builtin_types:
        builtin = BUILTIN_TYPE_NAMES[name]
        return builtin
    elif name.islower():
        return "".join(part.capitalize() for part in name.split("_"))
    else:
        return name


def is_simple(sum):
    """Return True if a sum is a simple.

    A sum is simple if its types have no fields, e.g.
    unaryop = Invert | Not | UAdd | USub
    """
    for t in sum.types:
        if t.fields:
            return False
    return True


def asdl_of(name, obj):
    if isinstance(obj, asdl.Product) or isinstance(obj, asdl.Constructor):
        fields = ", ".join(map(str, obj.fields))
        if fields:
            fields = "({})".format(fields)
        return "{}{}".format(name, fields)
    else:
        if is_simple(obj):
            types = " | ".join(type.name for type in obj.types)
        else:
            sep = "\n{}| ".format(" " * (len(name) + 1))
            types = sep.join(asdl_of(type.name, type) for type in obj.types)
        return "{} = {}".format(name, types)


class TypeInfo:
    type: asdl.Type
    enum_name: Optional[str]
    has_user_data: Optional[bool]
    has_attributes: bool
    is_simple: bool
    children: set
    fields: Optional[Any]
    boxed: bool

    def __init__(self, type):
        self.type = type
        self.enum_name = None
        self.has_user_data = None
        self.has_attributes = False
        self.is_simple = False
        self.children = set()
        self.fields = None
        self.boxed = False

    def __repr__(self):
        return f"<TypeInfo: {self.name}>"

    @property
    def name(self):
        return self.type.name

    @property
    def is_type(self):
        return isinstance(self.type, asdl.Type)

    @property
    def is_product(self):
        return self.is_type and isinstance(self.type.value, asdl.Product)

    @property
    def is_sum(self):
        return self.is_type and isinstance(self.type.value, asdl.Sum)

    @property
    def has_expr(self):
        return self.is_product and any(
            f.type != "identifier" for f in self.type.value.fields
        )

    @property
    def is_custom(self):
        return self.type.name in [t.name for t in CUSTOM_TYPES]

    @property
    def is_custom_replaced(self):
        return self.type.name in CUSTOM_REPLACEMENTS

    @property
    def custom(self):
        if self.type.name in CUSTOM_REPLACEMENTS:
            return CUSTOM_REPLACEMENTS[self.type.name]
        return self.type

    def no_cfg(self, typeinfo):
        if self.is_product:
            return self.has_attributes
        elif self.enum_name:
            return typeinfo[self.enum_name].has_attributes
        else:
            return self.has_attributes

    @property
    def rust_name(self):
        return rust_type_name(self.name)

    @property
    def full_field_name(self):
        name = self.name
        if name.startswith("alt:"):
            name = name[4:]
        if self.enum_name is None:
            return name
        else:
            return f"{self.enum_name}_{rust_field_name(name)}"

    @property
    def full_type_name(self):
        name = self.name
        if name.startswith("alt:"):
            name = name[4:]
        rust_name = rust_type_name(name)
        if self.enum_name is not None:
            rust_name = rust_type_name(self.enum_name) + rust_name
        if self.is_custom_replaced:
            rust_name = "Python" + rust_name
        return rust_name

    def determine_user_data(self, type_info, stack):
        if self.name in stack:
            return None
        stack.add(self.name)
        for child, child_seq in self.children:
            if child in asdl.builtin_types:
                continue
            child_info = type_info[child]
            child_has_user_data = child_info.determine_user_data(type_info, stack)
            if self.has_user_data is None and child_has_user_data is True:
                self.has_user_data = True

        stack.remove(self.name)
        return self.has_user_data


class TypeInfoMixin:
    type_info: Dict[str, TypeInfo]

    def customized_type_info(self, type_name):
        info = self.type_info[type_name]
        return self.type_info[info.custom.name]

    def has_user_data(self, typ):
        return self.type_info[typ].has_user_data

    def apply_generics(self, typ, *generics):
        needs_generics = not self.type_info[typ].is_simple
        if needs_generics:
            return [f"<{g}>" for g in generics]
        else:
            return ["" for g in generics]


class EmitVisitor(asdl.VisitorBase, TypeInfoMixin):
    """Visit that emits lines"""

    def __init__(self, file, type_info):
        self.file = file
        self.type_info = type_info
        self.identifiers = set()
        super(EmitVisitor, self).__init__()

    def emit_identifier(self, name):
        name = str(name)
        if name in self.identifiers:
            return
        self.emit("_Py_IDENTIFIER(%s);" % name, 0)
        self.identifiers.add(name)

    def emit(self, line, depth):
        if line:
            line = (" " * TABSIZE * depth) + textwrap.dedent(line)
        self.file.write(line + "\n")


class FindUserDataTypesVisitor(asdl.VisitorBase):
    def __init__(self, type_info):
        self.type_info = type_info
        super().__init__()

    def visitModule(self, mod):
        for dfn in mod.dfns + CUSTOM_TYPES:
            self.visit(dfn)
        stack = set()
        for info in self.type_info.values():
            info.determine_user_data(self.type_info, stack)

    def visitType(self, type):
        key = type.name
        info = self.type_info[key] = TypeInfo(type)
        self.visit(type.value, info)

    def visitSum(self, sum, info):
        type = info.type
        info.is_simple = is_simple(sum)
        for cons in sum.types:
            self.visit(cons, type, info.is_simple)

        if info.is_simple:
            info.has_user_data = False
            return

        for t in sum.types:
            self.add_children(t.name, t.fields)

        if len(sum.types) > 1:
            info.boxed = True
        if sum.attributes:
            # attributes means located, which has the `range: R` field
            info.has_user_data = True
            info.has_attributes = True

        for variant in sum.types:
            self.add_children(type.name, variant.fields)

    def visitConstructor(self, cons, type, simple):
        info = self.type_info[cons.name] = TypeInfo(cons)
        info.enum_name = type.name
        info.is_simple = simple

    def visitProduct(self, product, info):
        type = info.type
        if product.attributes:
            # attributes means located, which has the `range: R` field
            info.has_user_data = True
            info.has_attributes = True
        if len(product.fields) > 2:
            info.boxed = True
        self.add_children(type.name, product.fields)

    def add_children(self, name, fields):
        self.type_info[name].children.update(
            (field.type, field.seq) for field in fields
        )


def rust_field(field_name):
    if field_name in RUST_KEYWORDS:
        field_name += "_"
    return field_name


class StructVisitor(EmitVisitor):
    """Visitor to generate type-defs for AST."""

    def __init__(self, *args, **kw):
        super().__init__(*args, **kw)

    def emit_attrs(self, depth):
        self.emit("#[derive(Clone, Debug, PartialEq)]", depth)

    def emit_range(self, has_attributes, depth):
        if has_attributes:
            self.emit("pub range: R,", depth + 1)
        else:
            self.emit("pub range: OptionalRange<R>,", depth + 1)

    def visitModule(self, mod):
        self.emit_attrs(0)
        self.emit(
            """
        #[derive(is_macro::Is)]
        pub enum Ast<R=TextRange> {
        """,
            0,
        )
        for dfn in mod.dfns:
            info = self.customized_type_info(dfn.name)
            dfn = info.custom
            rust_name = info.full_type_name
            generics = "" if self.type_info[dfn.name].is_simple else "<R>"
            if dfn.name == "mod":
                # This is exceptional rule to other enums.
                # Unlike other enums, this is justified because `Mod` is only used as
                # the top node of parsing result and never a child node of other nodes.
                # Because it will be very rarely used in very particular applications,
                # "ast_" prefix to everywhere seems less useful.
                self.emit('#[is(name = "module")]', 1)
            self.emit(f"{rust_name}({rust_name}{generics}),", 1)
        self.emit(
            """
            }
            impl<R> Node for Ast<R> {
                const NAME: &'static str = "AST";
                const FIELD_NAMES: &'static [&'static str] = &[];
            }
            """,
            0,
        )
        for dfn in mod.dfns:
            info = self.customized_type_info(dfn.name)
            rust_name = info.full_type_name
            generics = "" if self.type_info[dfn.name].is_simple else "<R>"
            self.emit(
                f"""
            impl<R> From<{rust_name}{generics}> for Ast<R> {{
                fn from(node: {rust_name}{generics}) -> Self {{
                    Ast::{rust_name}(node)
                }}
            }}
            """,
                0,
            )

        for dfn in mod.dfns + CUSTOM_TYPES:
            self.visit(dfn)

    def visitType(self, type, depth=0):
        if hasattr(type, "doc"):
            doc = "/// " + type.doc.replace("\n", "\n/// ") + "\n"
        else:
            doc = f"/// See also [{type.name}](https://docs.python.org/3/library/ast.html#ast.{type.name})"
        self.emit(doc, depth)
        self.visit(type.value, type, depth)

    def visitSum(self, sum, type, depth):
        if is_simple(sum):
            self.simple_sum(sum, type, depth)
        else:
            self.sum_with_constructors(sum, type, depth)

        (generics_applied,) = self.apply_generics(type.name, "R")
        self.emit(
            f"""
            impl{generics_applied} Node for {rust_type_name(type.name)}{generics_applied} {{
                const NAME: &'static str = "{type.name}";
                const FIELD_NAMES: &'static [&'static str] = &[];
            }}
            """,
            depth,
        )

    def simple_sum(self, sum, type, depth):
        rust_name = rust_type_name(type.name)
        self.emit_attrs(depth)
        self.emit("#[derive(is_macro::Is, Copy, Hash, Eq)]", depth)
        self.emit(f"pub enum {rust_name} {{", depth)
        for cons in sum.types:
            self.emit(f"{cons.name},", depth + 1)
        self.emit("}", depth)
        self.emit(f"impl {rust_name} {{", depth)
        needs_escape = any(rust_field_name(t.name) in RUST_KEYWORDS for t in sum.types)
        if needs_escape:
            prefix = rust_field_name(type.name) + "_"
        else:
            prefix = ""
        for cons in sum.types:
            self.emit(
                f"""
                #[inline]
                pub const fn {prefix}{rust_field_name(cons.name)}(&self) -> Option<{rust_name}{cons.name}> {{
                    match self {{
                        {rust_name}::{cons.name} => Some({rust_name}{cons.name}),
                        _ => None,
                    }}
                }}
                """,
                depth,
            )
        self.emit("}", depth)
        self.emit("", depth)

        for cons in sum.types:
            self.emit(
                f"""
                pub struct {rust_name}{cons.name};
                impl From<{rust_name}{cons.name}> for {rust_name} {{
                    fn from(_: {rust_name}{cons.name}) -> Self {{
                        {rust_name}::{cons.name}
                    }}
                }}
                impl<R> From<{rust_name}{cons.name}> for Ast<R> {{
                    fn from(_: {rust_name}{cons.name}) -> Self {{
                        {rust_name}::{cons.name}.into()
                    }}
                }}
                impl Node for {rust_name}{cons.name} {{
                    const NAME: &'static str = "{cons.name}";
                    const FIELD_NAMES: &'static [&'static str] = &[];
                }}
                impl std::cmp::PartialEq<{rust_name}> for {rust_name}{cons.name} {{
                    #[inline]
                    fn eq(&self, other: &{rust_name}) -> bool {{
                        matches!(other, {rust_name}::{cons.name})
                    }}
                }}
                """,
                0,
            )

    def sum_with_constructors(self, sum, type, depth):
        type_info = self.type_info[type.name]
        rust_name = rust_type_name(type.name)

        self.emit_attrs(depth)
        self.emit("#[derive(is_macro::Is)]", depth)
        self.emit(f"pub enum {rust_name}<R = TextRange> {{", depth)
        needs_escape = any(rust_field_name(t.name) in RUST_KEYWORDS for t in sum.types)
        for t in sum.types:
            if needs_escape:
                self.emit(
                    f'#[is(name = "{rust_field_name(t.name)}_{rust_name.lower()}")]',
                    depth + 1,
                )
            self.emit(f"{t.name}({rust_name}{t.name}<R>),", depth + 1)
        self.emit("}", depth)
        self.emit("", depth)

        for t in sum.types:
            self.sum_subtype_struct(type_info, t, rust_name, depth)

    def sum_subtype_struct(self, sum_type_info, t, rust_name, depth):
        self.emit(
            f"""/// See also [{t.name}](https://docs.python.org/3/library/ast.html#ast.{t.name})""",
            depth,
        )
        self.emit_attrs(depth)
        payload_name = f"{rust_name}{t.name}"
        self.emit(f"pub struct {payload_name}<R = TextRange> {{", depth)
        self.emit_range(sum_type_info.has_attributes, depth)
        for f in t.fields:
            self.visit(f, sum_type_info, "pub ", depth + 1, t.name)

        assert sum_type_info.has_attributes == self.type_info[t.name].no_cfg(
            self.type_info
        )

        self.emit("}", depth)
        field_names = [f'"{f.name}"' for f in t.fields]
        self.emit(
            f"""
            impl<R> Node for {payload_name}<R> {{
                const NAME: &'static str = "{t.name}";
                const FIELD_NAMES: &'static [&'static str] = &[{', '.join(field_names)}];
            }}
            impl<R> From<{payload_name}<R>> for {rust_name}<R> {{
                fn from(payload: {payload_name}<R>) -> Self {{
                    {rust_name}::{t.name}(payload)
                }}
            }}
            impl<R> From<{payload_name}<R>> for Ast<R> {{
                fn from(payload: {payload_name}<R>) -> Self {{
                    {rust_name}::from(payload).into()
                }}
            }}
            """,
            depth,
        )

        self.emit("", depth)

    def visitConstructor(self, cons, parent, depth):
        if cons.fields:
            self.emit(f"{cons.name} {{", depth)
            for f in cons.fields:
                self.visit(f, parent, "", depth + 1, cons.name)
            self.emit("},", depth)
        else:
            self.emit(f"{cons.name},", depth)

    def visitField(self, field, parent, vis, depth, constructor=None):
        try:
            field_type = self.customized_type_info(field.type)
            typ = field_type.full_type_name
        except KeyError:
            field_type = None
            typ = rust_type_name(field.type)
        if field_type and not field_type.is_simple:
            typ = f"{typ}<R>"
        # don't box if we're doing Vec<T>, but do box if we're doing Vec<Option<Box<T>>>
        if (
            field_type
            and field_type.boxed
            and (not (parent.is_product or field.seq) or field.opt)
        ):
            typ = f"Box<{typ}>"
        if field.opt or (
            # When a dictionary literal contains dictionary unpacking (e.g., `{**d}`),
            # the expression to be unpacked goes in `values` with a `None` at the corresponding
            # position in `keys`. To handle this, the type of `keys` needs to be `Option<Vec<T>>`.
            constructor == "Dict"
            and field.name == "keys"
        ):
            typ = f"Option<{typ}>"
        if field.seq:
            typ = f"Vec<{typ}>"
        if typ == "Int":
            typ = BUILTIN_INT_NAMES.get(field.name, typ)
        name = rust_field(field.name)
        self.emit(f"{vis}{name}: {typ},", depth)

    def visitProduct(self, product, type, depth):
        type_info = self.type_info[type.name]
        product_name = type_info.full_type_name
        self.emit_attrs(depth)
        self.emit(f"pub struct {product_name}<R = TextRange> {{", depth)
        self.emit_range(product.attributes, depth + 1)
        for f in product.fields:
            self.visit(f, type_info, "pub ", depth + 1)
        assert bool(product.attributes) == type_info.no_cfg(self.type_info)
        self.emit("}", depth)

        field_names = [f'"{f.name}"' for f in product.fields]
        self.emit(
            f"""
            impl<R> Node for {product_name}<R>  {{
                const NAME: &'static str = "{type.name}";
                const FIELD_NAMES: &'static [&'static str] = &[
                {', '.join(field_names)}
                ];
            }}
            """,
            depth,
        )


class RangedDefVisitor(EmitVisitor):
    def visitModule(self, mod):
        for dfn in mod.dfns + CUSTOM_TYPES:
            self.visit(dfn)

    def visitType(self, type, depth=0):
        self.visit(type.value, type.name, depth)

    def visitSum(self, sum, name, depth):
        info = self.type_info[name]

        self.emit_type_alias(info)

        if info.is_simple:
            for ty in sum.types:
                variant_info = self.type_info[ty.name]
                self.emit_type_alias(variant_info)
            return

        sum_match_arms = ""

        for ty in sum.types:
            variant_info = self.type_info[ty.name]
            sum_match_arms += (
                f"        Self::{variant_info.rust_name}(node) => node.range(),"
            )
            self.emit_type_alias(variant_info)
            self.emit_ranged_impl(variant_info)

        if not info.no_cfg(self.type_info):
            self.emit('#[cfg(feature = "all-nodes-with-ranges")]', 0)

        self.emit(
            f"""
            impl Ranged for crate::{info.full_type_name} {{
                fn range(&self) -> TextRange {{
                    match self {{
                        {sum_match_arms}
                    }}
                }}
            }}
            """.lstrip(),
            0,
        )

    def visitProduct(self, product, name, depth):
        info = self.type_info[name]

        self.emit_type_alias(info)
        self.emit_ranged_impl(info)

    def emit_type_alias(self, info):
        return  # disable
        generics = "" if info.is_simple else "::<TextRange>"

        self.emit(
            f"pub type {info.full_type_name} = crate::generic::{info.full_type_name}{generics};",
            0,
        )
        self.emit("", 0)

    def emit_ranged_impl(self, info):
        if not info.no_cfg(self.type_info):
            self.emit('#[cfg(feature = "all-nodes-with-ranges")]', 0)

        self.file.write(
            f"""
            impl Ranged for crate::generic::{info.full_type_name}::<TextRange> {{
                fn range(&self) -> TextRange {{
                    self.range
                }}
            }}
            """.strip()
        )


def write_ast_def(mod, type_info, f):
    f.write("use crate::text_size::TextRange;")
    StructVisitor(f, type_info).visit(mod)


def write_ranged_def(mod, type_info, f):
    RangedDefVisitor(f, type_info).visit(mod)


def write_parse_def(mod, type_info, f):
    for info in type_info.values():
        if info.enum_name not in ["expr", "stmt"]:
            continue

        type_name = rust_type_name(info.enum_name)
        cons_name = rust_type_name(info.name)

        f.write(
            f"""
        impl Parse for ast::{info.full_type_name} {{
            fn lex_starts_at(
                source: &str,
                offset: TextSize,
            ) -> SoftKeywordTransformer<Lexer<std::str::Chars>> {{
                ast::{type_name}::lex_starts_at(source, offset)
            }}
            fn parse_tokens(
                lxr: impl IntoIterator<Item = LexResult>,
                source_path: &str,
            ) -> Result<Self, ParseError> {{
                let node = ast::{type_name}::parse_tokens(lxr, source_path)?;
                match node {{
                    ast::{type_name}::{cons_name}(node) => Ok(node),
                    node => Err(ParseError {{
                        error: ParseErrorType::InvalidToken,
                        offset: node.range().start(),
                        source_path: source_path.to_owned(),
                    }}),
                }}
            }}
        }}
        """
        )


def main(
    input_filename,
    ast_dir,
    parser_dir,
    dump_module=False,
):
    auto_gen_msg = AUTO_GEN_MESSAGE.format("/".join(Path(__file__).parts[-2:]))
    mod = asdl.parse(input_filename)
    if dump_module:
        print("Parsed Module:")
        print(mod)
    if not asdl.check(mod):
        sys.exit(1)

    type_info = {}
    FindUserDataTypesVisitor(type_info).visit(mod)

    from functools import partial as p

    for filename, write in [
        ("generic", p(write_ast_def, mod, type_info)),
        ("ranged", p(write_ranged_def, mod, type_info)),
    ]:
        with (ast_dir / f"{filename}.rs").open("w") as f:
            f.write(auto_gen_msg)
            write(f)

    for filename, write in [
        ("parse", p(write_parse_def, mod, type_info)),
    ]:
        with (parser_dir / f"{filename}.rs").open("w") as f:
            f.write(auto_gen_msg)
            write(f)

    print(f"{ast_dir} regenerated.")


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("input_file", type=Path)
    parser.add_argument("-A", "--ast-dir", type=Path, required=True)
    parser.add_argument("-P", "--parser-dir", type=Path, required=True)
    parser.add_argument("-d", "--dump-module", action="store_true")

    args = parser.parse_args()
    main(
        args.input_file,
        args.ast_dir,
        args.parser_dir,
        args.dump_module,
    )
