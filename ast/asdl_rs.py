# spell-checker:words dfn dfns

#! /usr/bin/env python
"""Generate Rust code from an ASDL description."""

import sys
import json
import textwrap
import re

from argparse import ArgumentParser
from pathlib import Path
from typing import Optional, Dict

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
}

RUST_KEYWORDS = {"if", "while", "for", "return", "match", "try", "await", "yield"}


def rust_field_name(name):
    name = rust_type_name(name)
    return re.sub(r"(?<!^)(?=[A-Z])", "_", name).lower()


def rust_type_name(name):
    """Return a string for the C name of the type.

    This function special cases the default types provided by asdl.
    """
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
    name: str
    enum_name: Optional[str]
    has_user_data: Optional[bool]
    has_attributes: bool
    is_simple: bool
    empty_field: bool
    children: set
    boxed: bool
    product: bool
    has_expr: bool = False

    def __init__(self, name):
        self.name = name
        self.enum_name = None
        self.has_user_data = None
        self.has_attributes = False
        self.is_simple = False
        self.empty_field = False
        self.children = set()
        self.boxed = False
        self.product = False
        self.product_has_expr = False

    def __repr__(self):
        return f"<TypeInfo: {self.name}>"

    def no_cfg(self, typeinfo):
        if self.product:
            return self.has_attributes
        elif self.enum_name:
            return typeinfo[self.enum_name].has_attributes
        else:
            return self.has_attributes

    @property
    def rust_name(self):
        return rust_type_name(self.name)

    @property
    def sum_name(self):
        if self.enum_name is None:
            return self.name
        else:
            return f"{self.enum_name}_{self.name}"

    @property
    def rust_sum_name(self):
        rust_name = rust_type_name(self.name)
        if self.enum_name is None:
            return rust_name
        else:
            name = rust_type_name(self.enum_name) + rust_name
            return name

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
            line = (" " * TABSIZE * depth) + line
        self.file.write(line + "\n")


class FindUserDataTypesVisitor(asdl.VisitorBase):
    def __init__(self, type_info):
        self.type_info = type_info
        super().__init__()

    def visitModule(self, mod):
        for dfn in mod.dfns:
            self.visit(dfn)
        stack = set()
        for info in self.type_info.values():
            info.determine_user_data(self.type_info, stack)

    def visitType(self, type):
        self.type_info[type.name] = TypeInfo(type.name)
        self.visit(type.value, type.name)

    def visitSum(self, sum, name):
        info = self.type_info[name]
        if is_simple(sum):
            info.has_user_data = False
            info.is_simple = True
        else:
            for t in sum.types:
                t_info = TypeInfo(t.name)
                t_info.enum_name = name
                t_info.empty_field = not t.fields
                self.type_info[t.name] = t_info
                self.add_children(t.name, t.fields)
            if len(sum.types) > 1:
                info.boxed = True
            if sum.attributes:
                # attributes means located, which has the `custom: U` field
                info.has_user_data = True
                info.has_attributes = True

        for variant in sum.types:
            self.add_children(name, variant.fields)

    def visitProduct(self, product, name):
        info = self.type_info[name]
        if product.attributes:
            # attributes means located, which has the `custom: U` field
            info.has_user_data = True
            info.has_attributes = True
        info.has_expr = product_has_expr(product)
        if len(product.fields) > 2:
            info.boxed = True
        info.product = True
        self.add_children(name, product.fields)

    def add_children(self, name, fields):
        self.type_info[name].children.update(
            (field.type, field.seq) for field in fields
        )


def rust_field(field_name):
    if field_name == "type":
        return "type_"
    else:
        return field_name


def product_has_expr(product):
    return any(f.type != "identifier" for f in product.fields)


class StructVisitor(EmitVisitor):
    """Visitor to generate type-defs for AST."""

    def __init__(self, *args, **kw):
        super().__init__(*args, **kw)
        self.rust_type_defs = []

    def visitModule(self, mod):
        for dfn in mod.dfns:
            self.visit(dfn)

    def visitType(self, type, depth=0):
        self.visit(type.value, type.name, depth)

    def visitSum(self, sum, name, depth):
        if is_simple(sum):
            self.simple_sum(sum, name, depth)
        else:
            self.sum_with_constructors(sum, name, depth)

    def emit_attrs(self, depth):
        self.emit("#[derive(Clone, Debug, PartialEq)]", depth)

    def emit_custom(self, has_attributes, depth):
        if has_attributes:
            self.emit("pub custom: U,", depth + 1)
        else:
            self.emit('#[cfg(feature = "more-attributes")]', depth + 1)
            self.emit("pub custom: U,", depth + 1)
            self.emit('#[cfg(not(feature = "more-attributes"))]', depth + 1)
            self.emit("pub custom: std::marker::PhantomData<U>,", depth + 1)

    def simple_sum(self, sum, name, depth):
        rust_name = rust_type_name(name)
        self.emit_attrs(depth)
        self.emit("#[derive(is_macro::Is)]", depth)
        self.emit(f"pub enum {rust_name} {{", depth)
        for variant in sum.types:
            self.emit(f"{variant.name},", depth + 1)
        self.emit("}", depth)
        self.emit("", depth)

    def sum_with_constructors(self, sum, name, depth):
        type_info = self.type_info[name]
        rust_name = rust_type_name(name)
        # all the attributes right now are for location, so if it has attrs we
        # can just wrap it in Attributed<>

        for t in sum.types:
            self.sum_subtype_struct(type_info, t, rust_name, depth)

        self.emit_attrs(depth)
        self.emit("#[derive(is_macro::Is)]", depth)
        self.emit(f"pub enum {rust_name}<U> {{", depth)
        needs_escape = any(rust_field_name(t.name) in RUST_KEYWORDS for t in sum.types)
        for t in sum.types:
            if needs_escape:
                self.emit(
                    f'#[is(name = "{rust_field_name(t.name)}_{rust_name.lower()}")]',
                    depth + 1,
                )
            self.emit(f"{t.name}({rust_name}{t.name}<U>),", depth + 1)
        self.emit("}", depth)
        self.emit("", depth)

    def sum_subtype_struct(self, sum_type_info, t, rust_name, depth):
        self.emit_attrs(depth)
        payload_name = f"{rust_name}{t.name}"
        self.emit(f"pub struct {payload_name}<U> {{", depth)
        for f in t.fields:
            self.visit(f, sum_type_info, "pub ", depth + 1, t.name)

        assert sum_type_info.has_attributes == self.type_info[t.name].no_cfg(
            self.type_info
        )
        self.emit_custom(sum_type_info.has_attributes, depth)

        self.emit("}", depth)
        self.emit(
            textwrap.dedent(
                f"""
                impl<U> From<{payload_name}<U>> for {rust_name}<U> {{
                    fn from(payload: {payload_name}<U>) -> Self {{
                        {rust_name}::{t.name}(payload)
                    }}
                }}
                """
            ),
            depth,
        )

        if not sum_type_info.has_attributes:
            self.emit('#[cfg(feature = "more-attributes")]', depth)
        self.emit(f"impl<U> Custom<U> for {payload_name}<U> {{", depth)
        self.emit("#[inline]", depth + 1)
        self.emit("fn custom(self) -> U {", depth + 1)
        self.emit("self.custom", depth + 2)
        self.emit("}", depth + 1)
        self.emit("}", depth)
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
        typ = rust_type_name(field.type)
        field_type = self.type_info.get(field.type)
        if field_type and not field_type.is_simple:
            typ = f"{typ}<U>"
        # don't box if we're doing Vec<T>, but do box if we're doing Vec<Option<Box<T>>>
        if (
            field_type
            and field_type.boxed
            and (not (parent.product or field.seq) or field.opt)
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

    def visitProduct(self, product, name, depth):
        type_info = self.type_info[name]
        product_name = rust_type_name(name)
        self.emit_attrs(depth)

        self.emit(f"pub struct {product_name}<U> {{", depth)
        for f in product.fields:
            self.visit(f, type_info, "pub ", depth + 1)
        assert bool(product.attributes) == type_info.no_cfg(self.type_info)
        self.emit_custom(product.attributes, depth + 1)
        self.emit("}", depth)

        self.emit('#[cfg(feature = "more-attributes")]', depth)
        self.emit(f"impl<T> Custom<U> for {product_name}<U> {{", depth)
        self.emit("#[inline]", depth + 1)
        self.emit("fn custom(&self) -> U {", depth + 1)
        self.emit("self.custom", depth + 2)
        self.emit("}", depth + 1)
        self.emit("}", depth)
        self.emit("", depth)


class FoldTraitDefVisitor(EmitVisitor):
    def visitModule(self, mod, depth):
        self.emit("pub trait Fold<U> {", depth)
        self.emit("type TargetU;", depth + 1)
        self.emit("type Error;", depth + 1)
        self.emit(
            """
            fn map_user(&mut self, user: U) -> Result<Self::TargetU, Self::Error>;
            #[cfg(feature = "more-attributes")]
            fn map_user_cfg(&mut self, user: U) -> Result<Self::TargetU, Self::Error> {
                self.map_user(user)
            }
            #[cfg(not(feature = "more-attributes"))]
            fn map_user_cfg(&mut self, _user: U) -> Result<std::marker::PhantomData<Self::TargetU>, Self::Error> {
                Ok(std::marker::PhantomData)
            }
            """,
            depth + 1,
        )
        self.emit(
            """
            fn fold<X: Foldable<U, Self::TargetU>>(&mut self, node: X) -> Result<X::Mapped, Self::Error> {
                node.fold(self)
            }""",
            depth + 1,
        )
        for dfn in mod.dfns:
            self.visit(dfn, depth + 2)
        self.emit("}", depth)

    def visitType(self, type, depth):
        name = type.name
        apply_u, apply_target_u = self.apply_generics(name, "U", "Self::TargetU")
        enum_name = rust_type_name(name)
        self.emit(
            f"fn fold_{name}(&mut self, node: {enum_name}{apply_u}) -> Result<{enum_name}{apply_target_u}, Self::Error> {{",
            depth,
        )
        self.emit(f"fold_{name}(self, node)", depth + 1)
        self.emit("}", depth)


class FoldImplVisitor(EmitVisitor):
    def visitModule(self, mod, depth):
        for dfn in mod.dfns:
            self.visit(dfn, depth)

    def visitType(self, type, depth=0):
        self.visit(type.value, type.name, depth)

    def visitSum(self, sum, name, depth):
        type_info = self.type_info[name]
        apply_t, apply_u, apply_target_u = self.apply_generics(
            name, "T", "U", "F::TargetU"
        )
        enum_name = rust_type_name(name)
        simple = is_simple(sum)

        self.emit(f"impl<T, U> Foldable<T, U> for {enum_name}{apply_t} {{", depth)
        self.emit(f"type Mapped = {enum_name}{apply_u};", depth + 1)
        self.emit(
            "fn fold<F: Fold<T, TargetU = U> + ?Sized>(self, folder: &mut F) -> Result<Self::Mapped, F::Error> {",
            depth + 1,
        )
        self.emit(f"folder.fold_{name}(self)", depth + 2)
        self.emit("}", depth + 1)
        self.emit("}", depth)

        self.emit(
            f"pub fn fold_{name}<U, F: Fold<U> + ?Sized>(#[allow(unused)] folder: &mut F, node: {enum_name}{apply_u}) -> Result<{enum_name}{apply_target_u}, F::Error> {{",
            depth,
        )

        if simple:
            self.emit("Ok(node) }", depth + 1)
            return

        self.emit("match node {", depth + 1)
        for cons in sum.types:
            fields_pattern = self.make_pattern(enum_name, cons.name, cons.fields)
            self.emit(
                f"{fields_pattern[0]} {{ {fields_pattern[1]}}} {fields_pattern[2]} => {{",
                depth + 2,
            )
            if not type_info.has_attributes:
                self.emit('#[cfg(not(feature = "more-attributes"))]', depth + 3)
                self.emit("let custom = std::marker::PhantomData;", depth + 3)
                self.emit('#[cfg(feature = "more-attributes")]', depth + 3)
            self.emit("let custom = folder.map_user(custom)?;", depth + 3)
            self.gen_construction(
                fields_pattern[0], cons.fields, fields_pattern[2], depth + 3
            )
            self.emit("}", depth + 2)
        self.emit("}", depth + 1)
        self.emit("}", depth)

    def visitProduct(self, product, name, depth):
        apply_t, apply_u, apply_target_u = self.apply_generics(
            name, "T", "U", "F::TargetU"
        )
        struct_name = rust_type_name(name)
        has_attributes = bool(product.attributes)

        self.emit(f"impl<T, U> Foldable<T, U> for {struct_name}{apply_t} {{", depth)
        self.emit(f"type Mapped = {struct_name}{apply_u};", depth + 1)
        self.emit(
            "fn fold<F: Fold<T, TargetU = U> + ?Sized>(self, folder: &mut F) -> Result<Self::Mapped, F::Error> {",
            depth + 1,
        )
        self.emit(f"folder.fold_{name}(self)", depth + 2)
        self.emit("}", depth + 1)
        self.emit("}", depth)

        self.emit(
            f"pub fn fold_{name}<U, F: Fold<U> + ?Sized>(#[allow(unused)] folder: &mut F, node: {struct_name}{apply_u}) -> Result<{struct_name}{apply_target_u}, F::Error> {{",
            depth,
        )

        fields_pattern = self.make_pattern(struct_name, struct_name, product.fields)
        self.emit(f"let {struct_name} {{ {fields_pattern[1]} }} = node;", depth + 1)

        if not has_attributes:
            self.emit('#[cfg(not(feature = "more-attributes"))]', depth + 3)
            self.emit("let custom = std::marker::PhantomData;", depth + 3)
            self.emit('#[cfg(feature = "more-attributes")]', depth + 3)
        self.emit("let custom = folder.map_user(custom)?;", depth + 3)

        self.gen_construction(struct_name, product.fields, "", depth + 1)

        self.emit("}", depth)

    def make_pattern(self, rust_name, fieldname: str, fields):
        header = f"{rust_name}::{fieldname}({rust_name}{fieldname}"
        footer = ")"

        body = ",".join(rust_field(f.name) for f in fields)
        if body:
            body += ","
        body += "custom"

        return header, body, footer

    def gen_construction(self, header, fields, footer, depth):
        self.emit(f"Ok({header} {{", depth)
        for field in fields:
            name = rust_field(field.name)
            self.emit(f"{name}: Foldable::fold({name}, folder)?,", depth + 1)
        self.emit("custom,", depth + 1)

        self.emit(f"}}{footer})", depth)


class FoldModuleVisitor(EmitVisitor):
    def visitModule(self, mod):
        depth = 0
        self.emit("use crate::fold_helpers::Foldable;", depth)
        FoldTraitDefVisitor(self.file, self.type_info).visit(mod, depth)
        FoldImplVisitor(self.file, self.type_info).visit(mod, depth)


class VisitorTraitDefVisitor(StructVisitor):
    def full_name(self, name):
        type_info = self.type_info[name]
        if type_info.enum_name:
            return f"{type_info.enum_name}_{name}"
        else:
            return name

    def node_type_name(self, name):
        type_info = self.type_info[name]
        if type_info.enum_name:
            return f"{rust_type_name(type_info.enum_name)}{rust_type_name(name)}"
        else:
            return rust_type_name(name)

    def visitModule(self, mod, depth):
        self.emit("pub trait Visitor<U=()> {", depth)

        for dfn in mod.dfns:
            self.visit(dfn, depth + 1)
        self.emit("}", depth)

    def visitType(self, type, depth=0):
        self.visit(type.value, type.name, depth)

    def emit_visitor(self, nodename, depth, has_node=True):
        type_info = self.type_info[nodename]
        node_type = type_info.rust_sum_name
        self.emit(
            f"fn visit_{type_info.sum_name}(&mut self, node: {node_type}) {{", depth
        )
        if has_node:
            self.emit(f"self.generic_visit_{type_info.sum_name}(node)", depth + 1)

        self.emit("}", depth)

    def emit_generic_visitor_signature(self, nodename, depth, has_node=True):
        type_info = self.type_info[nodename]
        if has_node:
            node_type = type_info.rust_sum_name
        else:
            node_type = "()"
        self.emit(
            f"fn generic_visit_{type_info.sum_name}(&mut self, node: {node_type}) {{",
            depth,
        )

    def emit_empty_generic_visitor(self, nodename, depth):
        self.emit_generic_visitor_signature(nodename, depth)
        self.emit("}", depth)

    def simple_sum(self, sum, name, depth):
        self.emit_visitor(name, depth)
        self.emit_empty_generic_visitor(name, depth)

    def visit_match_for_type(self, nodename, rust_name, type_, depth):
        self.emit(f"{rust_name}::{type_.name}", depth)
        self.emit("(data)", depth)
        self.emit(f"=> self.visit_{nodename}_{type_.name}(data),", depth)

    def visit_sum_type(self, name, type_, depth):
        self.emit_visitor(type_.name, depth, has_node=type_.fields)
        if not type_.fields:
            return

        self.emit_generic_visitor_signature(type_.name, depth, has_node=True)
        for f in type_.fields:
            fieldname = rust_field(f.name)
            field_type = self.type_info.get(f.type)
            if not (field_type and field_type.has_user_data):
                continue

            if f.opt:
                self.emit(f"if let Some(value) = node.{fieldname} {{", depth + 1)
            elif f.seq:
                iterable = f"node.{fieldname}"
                if type_.name == "Dict" and f.name == "keys":
                    iterable = f"{iterable}.into_iter().flatten()"
                self.emit(f"for value in {iterable} {{", depth + 1)
            else:
                self.emit("{", depth + 1)
                self.emit(f"let value = node.{fieldname};", depth + 2)

            variable = "value"
            if field_type.boxed and (not f.seq or f.opt):
                variable = "*" + variable
            type_info = self.type_info[field_type.name]
            self.emit(f"self.visit_{type_info.sum_name}({variable});", depth + 2)

            self.emit("}", depth + 1)

        self.emit("}", depth)

    def sum_with_constructors(self, sum, name, depth):
        if not sum.attributes:
            return

        enum_name = rust_type_name(name)
        self.emit_visitor(name, depth)
        self.emit_generic_visitor_signature(name, depth)
        depth += 1
        self.emit("match node.node {", depth)
        for t in sum.types:
            self.visit_match_for_type(name, enum_name, t, depth + 1)
        self.emit("}", depth)
        depth -= 1
        self.emit("}", depth)

        # Now for the visitors for the types
        for t in sum.types:
            self.visit_sum_type(name, t, depth)

    def visitProduct(self, product, name, depth):
        self.emit_visitor(name, depth)
        self.emit_empty_generic_visitor(name, depth)


class VisitorModuleVisitor(EmitVisitor):
    def visitModule(self, mod):
        depth = 0
        self.emit("#[allow(unused_variables, non_snake_case)]", depth)
        VisitorTraitDefVisitor(self.file, self.type_info).visit(mod, depth)


class class_defVisitor(EmitVisitor):
    def visitModule(self, mod):
        for dfn in mod.dfns:
            self.visit(dfn)

    def visitType(self, type, depth=0):
        self.visit(type.value, type.name, depth)

    def visitSum(self, sum, name, depth):
        struct_name = "NodeKind" + rust_type_name(name)
        self.emit(
            f'#[pyclass(module = "_ast", name = {json.dumps(name)}, base = "AstNode")]',
            depth,
        )
        self.emit(f"struct {struct_name};", depth)
        self.emit("#[pyclass(flags(HAS_DICT, BASETYPE))]", depth)
        self.emit(f"impl {struct_name} {{}}", depth)
        for cons in sum.types:
            self.visit(cons, sum.attributes, struct_name, depth)

    def visitConstructor(self, cons, attrs, base, depth):
        self.gen_class_def(cons.name, cons.fields, attrs, depth, base)

    def visitProduct(self, product, name, depth):
        self.gen_class_def(name, product.fields, product.attributes, depth)

    def gen_class_def(self, name, fields, attrs, depth, base="AstNode"):
        struct_name = "Node" + rust_type_name(name)
        self.emit(
            f'#[pyclass(module = "_ast", name = {json.dumps(name)}, base = {json.dumps(base)})]',
            depth,
        )
        self.emit(f"struct {struct_name};", depth)
        self.emit("#[pyclass(flags(HAS_DICT, BASETYPE))]", depth)
        self.emit(f"impl {struct_name} {{", depth)
        self.emit("#[extend_class]", depth + 1)
        self.emit(
            "fn extend_class_with_fields(ctx: &Context, class: &'static Py<PyType>) {",
            depth + 1,
        )
        fields = ",".join(
            f"ctx.new_str(ascii!({json.dumps(f.name)})).into()" for f in fields
        )
        self.emit(
            f"class.set_attr(identifier!(ctx, _fields), ctx.new_tuple(vec![{fields}]).into());",
            depth + 2,
        )
        attrs = ",".join(
            f"ctx.new_str(ascii!({json.dumps(attr.name)})).into()" for attr in attrs
        )
        self.emit(
            f"class.set_attr(identifier!(ctx, _attributes), ctx.new_list(vec![{attrs}]).into());",
            depth + 2,
        )
        self.emit("}", depth + 1)
        self.emit("}", depth)


class ExtendModuleVisitor(EmitVisitor):
    def visitModule(self, mod):
        depth = 0
        self.emit(
            "pub fn extend_module_nodes(vm: &VirtualMachine, module: &Py<PyModule>) {",
            depth,
        )
        self.emit("extend_module!(vm, module, {", depth + 1)
        for dfn in mod.dfns:
            self.visit(dfn, depth + 2)
        self.emit("})", depth + 1)
        self.emit("}", depth)

    def visitType(self, type, depth):
        self.visit(type.value, type.name, depth)

    def visitSum(self, sum, name, depth):
        rust_name = rust_type_name(name)
        self.emit(
            f"{json.dumps(name)} => NodeKind{rust_name}::make_class(&vm.ctx),", depth
        )
        for cons in sum.types:
            self.visit(cons, depth)

    def visitConstructor(self, cons, depth):
        self.gen_extension(cons.name, depth)

    def visitProduct(self, product, name, depth):
        self.gen_extension(name, depth)

    def gen_extension(self, name, depth):
        rust_name = rust_type_name(name)
        self.emit(f"{json.dumps(name)} => Node{rust_name}::make_class(&vm.ctx),", depth)


class TraitImplVisitor(EmitVisitor):
    def visitModule(self, mod):
        for dfn in mod.dfns:
            self.visit(dfn)

    def visitType(self, type, depth=0):
        self.visit(type.value, type.name, depth)

    def visitSum(self, sum, name, depth):
        rust_name = enum_name = rust_type_name(name)
        if sum.attributes:
            rust_name = enum_name + "Kind"

        self.emit(f"impl NamedNode for ast::located::{rust_name} {{", depth)
        self.emit(f"const NAME: &'static str = {json.dumps(name)};", depth + 1)
        self.emit("}", depth)
        self.emit(f"impl Node for ast::located::{rust_name} {{", depth)
        self.emit(
            "fn ast_to_object(self, _vm: &VirtualMachine) -> PyObjectRef {", depth + 1
        )
        self.emit("match self {", depth + 2)
        for variant in sum.types:
            self.constructor_to_object(variant, enum_name, rust_name, depth + 3)
        self.emit("}", depth + 2)
        self.emit("}", depth + 1)
        self.emit(
            "fn ast_from_object(_vm: &VirtualMachine, _object: PyObjectRef) -> PyResult<Self> {",
            depth + 1,
        )
        self.gen_sum_from_object(sum, name, enum_name, rust_name, depth + 2)
        self.emit("}", depth + 1)
        self.emit("}", depth)

    def constructor_to_object(self, cons, enum_name, rust_name, depth):
        self.emit(f"ast::located::{rust_name}::{cons.name}", depth)
        if cons.fields:
            fields_pattern = self.make_pattern(cons.fields)
            self.emit(
                f"( ast::located::{enum_name}{cons.name} {{ {fields_pattern} }} )",
                depth,
            )
        self.emit(" => {", depth)
        self.make_node(cons.name, cons.fields, depth + 1)
        self.emit("}", depth)

    def visitProduct(self, product, name, depth):
        struct_name = rust_type_name(name)

        self.emit(f"impl NamedNode for ast::located::{struct_name} {{", depth)
        self.emit(f"const NAME: &'static str = {json.dumps(name)};", depth + 1)
        self.emit("}", depth)
        self.emit(f"impl Node for ast::located::{struct_name} {{", depth)
        self.emit(
            "fn ast_to_object(self, _vm: &VirtualMachine) -> PyObjectRef {", depth + 1
        )
        fields_pattern = self.make_pattern(product.fields)
        self.emit(
            f"let ast::located::{struct_name} {{ {fields_pattern} }} = self;", depth + 2
        )
        self.make_node(name, product.fields, depth + 2)
        self.emit("}", depth + 1)
        self.emit(
            "fn ast_from_object(_vm: &VirtualMachine, _object: PyObjectRef) -> PyResult<Self> {",
            depth + 1,
        )
        self.gen_product_from_object(product, name, struct_name, depth + 2)
        self.emit("}", depth + 1)
        self.emit("}", depth)

    def make_node(self, variant, fields, depth):
        rust_variant = rust_type_name(variant)
        self.emit(
            f"let _node = AstNode.into_ref_with_type(_vm, Node{rust_variant}::static_type().to_owned()).unwrap();",
            depth,
        )
        if fields:
            self.emit("let _dict = _node.as_object().dict().unwrap();", depth)
        for f in fields:
            self.emit(
                f"_dict.set_item({json.dumps(f.name)}, {rust_field(f.name)}.ast_to_object(_vm), _vm).unwrap();",
                depth,
            )
        self.emit("_node.into()", depth)

    def make_pattern(self, fields):
        return ",".join(rust_field(f.name) for f in fields)

    def gen_sum_from_object(self, sum, sum_name, enum_name, rust_name, depth):
        # if sum.attributes:
        #     self.extract_location(sum_name, depth)

        self.emit("let _cls = _object.class();", depth)
        self.emit("Ok(", depth)
        for cons in sum.types:
            self.emit(f"if _cls.is(Node{cons.name}::static_type()) {{", depth)
            if cons.fields:
                self.emit(
                    f"ast::located::{rust_name}::{cons.name} (ast::located::{enum_name}{cons.name} {{",
                    depth + 1,
                )
                self.gen_construction_fields(cons, sum_name, depth + 1)
                self.emit("})", depth + 1)
            else:
                self.emit(f"ast::located::{rust_name}::{cons.name}", depth + 1)
            self.emit("} else", depth)

        self.emit("{", depth)
        msg = f'format!("expected some sort of {sum_name}, but got {{}}",_object.repr(_vm)?)'
        self.emit(f"return Err(_vm.new_type_error({msg}));", depth + 1)
        self.emit("})", depth)

    def gen_product_from_object(self, product, product_name, struct_name, depth):
        # if product.attributes:
        #     self.extract_location(product_name, depth)

        self.emit("Ok(", depth)
        self.gen_construction(struct_name, product, product_name, depth + 1)
        self.emit(")", depth)

    def gen_construction_fields(self, cons, name, depth):
        for field in cons.fields:
            self.emit(
                f"{rust_field(field.name)}: {self.decode_field(field, name)},",
                depth + 1,
            )

    def gen_construction(self, cons_path, cons, name, depth):
        self.emit(f"ast::located::{cons_path} {{", depth)
        self.gen_construction_fields(cons, name, depth + 1)
        self.emit("}", depth)

    def extract_location(self, typename, depth):
        row = self.decode_field(asdl.Field("int", "lineno"), typename)
        column = self.decode_field(asdl.Field("int", "col_offset"), typename)
        self.emit(
            f"""
            let _location = {{
                let row = {row};
                let column = {column};
                try_location(row, column)
            }};""",
            depth,
        )

    def decode_field(self, field, typename):
        name = json.dumps(field.name)
        if field.opt and not field.seq:
            return f"get_node_field_opt(_vm, &_object, {name})?.map(|obj| Node::ast_from_object(_vm, obj)).transpose()?"
        else:
            return f"Node::ast_from_object(_vm, get_node_field(_vm, &_object, {name}, {json.dumps(typename)})?)?"


class ChainOfVisitors:
    def __init__(self, *visitors):
        self.visitors = visitors

    def visit(self, object):
        for v in self.visitors:
            v.visit(object)
            v.emit("", 0)


def write_ast_def(mod, type_info, f):
    StructVisitor(f, type_info).visit(mod)


def write_fold_def(mod, type_info, f):
    f.write(
        """
use crate::generic::Custom;
"""
    )
    FoldModuleVisitor(f, type_info).visit(mod)


def write_visitor_def(mod, type_info, f):
    VisitorModuleVisitor(f, type_info).visit(mod)


def write_ranged_def(mod, type_info, f):
    for info in type_info.values():
        if not info.is_simple:
            if info.no_cfg:
                f.write('#[cfg(feature = "more-attributes")]')
            f.write(
                f"""
            impl Ranged for {info.rust_sum_name} {{
                fn range(&self) -> TextRange {{
                    self.custom
                }}
            }}
            """
            )
            generics = "::<TextRange>"
        else:
            generics = ""
        f.write(
            f"pub type {info.rust_sum_name} = crate::generic::{info.rust_sum_name}{generics};\n"
        )


def write_located_def(mod, type_info, f):
    for info in type_info.values():
        if not info.is_simple:
            if info.no_cfg:
                f.write('#[cfg(feature = "more-attributes")]')
            f.write(
                f"""
            impl Located for {info.rust_sum_name} {{
                fn range(&self) -> SourceRange {{
                    self.custom
                }}
            }}
            """
            )
            generics = "::<SourceRange>"
        else:
            generics = ""
        f.write(
            f"pub type {info.rust_sum_name} = crate::generic::{info.rust_sum_name}{generics};\n"
        )


def write_ast_mod(mod, type_info, f):
    f.write(
        textwrap.dedent(
            """
            #![allow(clippy::all)]

            use super::*;
            use crate::common::ascii;
            """
        )
    )

    c = ChainOfVisitors(
        class_defVisitor(f, type_info),
        TraitImplVisitor(f, type_info),
        ExtendModuleVisitor(f, type_info),
    )
    c.visit(mod)


def main(
    input_filename,
    ast_dir,
    module_filename,
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

    for filename, write in [
        ("generic", write_ast_def),
        ("fold", write_fold_def),
        ("ranged", write_ranged_def),
        ("located", write_located_def),
        ("visitor", write_visitor_def),
    ]:
        with (ast_dir / f"{filename}.rs").open("w") as f:
            f.write(auto_gen_msg)
            write(mod, type_info, f)

    with module_filename.open("w") as module_file:
        module_file.write(auto_gen_msg)
        write_ast_mod(mod, type_info, module_file)

    print(f"{ast_dir}, {module_filename} regenerated.")


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("input_file", type=Path)
    parser.add_argument("-A", "--ast-dir", type=Path, required=True)
    parser.add_argument("-M", "--module-file", type=Path, required=True)
    parser.add_argument("-d", "--dump-module", action="store_true")

    args = parser.parse_args()
    main(
        args.input_file,
        args.ast_dir,
        args.module_file,
        args.dump_module,
    )
