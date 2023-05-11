// File automatically generated by ast/asdl_rs.py.

use crate::fold_helpers::Foldable;
use crate::generic::Custom;
pub trait Fold<U> {
    type TargetU;
    type Error;

    fn map_user(&mut self, user: U) -> Result<Self::TargetU, Self::Error>;
    #[cfg(feature = "more-attributes")]
    fn map_user_cfg(&mut self, user: U) -> Result<Self::TargetU, Self::Error> {
        self.map_user(user)
    }
    #[cfg(not(feature = "more-attributes"))]
    fn map_user_cfg(
        &mut self,
        _user: std::marker::PhantomData<U>,
    ) -> Result<std::marker::PhantomData<Self::TargetU>, Self::Error> {
        Ok(std::marker::PhantomData)
    }

    fn fold<X: Foldable<U, Self::TargetU>>(&mut self, node: X) -> Result<X::Mapped, Self::Error> {
        node.fold(self)
    }
    fn fold_mod(&mut self, node: Mod<U>) -> Result<Mod<Self::TargetU>, Self::Error> {
        fold_mod(self, node)
    }
    fn fold_stmt(&mut self, node: Stmt<U>) -> Result<Stmt<Self::TargetU>, Self::Error> {
        fold_stmt(self, node)
    }
    fn fold_expr(&mut self, node: Expr<U>) -> Result<Expr<Self::TargetU>, Self::Error> {
        fold_expr(self, node)
    }
    fn fold_expr_context(&mut self, node: ExprContext) -> Result<ExprContext, Self::Error> {
        fold_expr_context(self, node)
    }
    fn fold_boolop(&mut self, node: Boolop) -> Result<Boolop, Self::Error> {
        fold_boolop(self, node)
    }
    fn fold_operator(&mut self, node: Operator) -> Result<Operator, Self::Error> {
        fold_operator(self, node)
    }
    fn fold_unaryop(&mut self, node: Unaryop) -> Result<Unaryop, Self::Error> {
        fold_unaryop(self, node)
    }
    fn fold_cmpop(&mut self, node: Cmpop) -> Result<Cmpop, Self::Error> {
        fold_cmpop(self, node)
    }
    fn fold_comprehension(
        &mut self,
        node: Comprehension<U>,
    ) -> Result<Comprehension<Self::TargetU>, Self::Error> {
        fold_comprehension(self, node)
    }
    fn fold_excepthandler(
        &mut self,
        node: Excepthandler<U>,
    ) -> Result<Excepthandler<Self::TargetU>, Self::Error> {
        fold_excepthandler(self, node)
    }
    fn fold_arguments(
        &mut self,
        node: Arguments<U>,
    ) -> Result<Arguments<Self::TargetU>, Self::Error> {
        fold_arguments(self, node)
    }
    fn fold_arg(&mut self, node: Arg<U>) -> Result<Arg<Self::TargetU>, Self::Error> {
        fold_arg(self, node)
    }
    fn fold_keyword(&mut self, node: Keyword<U>) -> Result<Keyword<Self::TargetU>, Self::Error> {
        fold_keyword(self, node)
    }
    fn fold_alias(&mut self, node: Alias<U>) -> Result<Alias<Self::TargetU>, Self::Error> {
        fold_alias(self, node)
    }
    fn fold_withitem(&mut self, node: Withitem<U>) -> Result<Withitem<Self::TargetU>, Self::Error> {
        fold_withitem(self, node)
    }
    fn fold_match_case(
        &mut self,
        node: MatchCase<U>,
    ) -> Result<MatchCase<Self::TargetU>, Self::Error> {
        fold_match_case(self, node)
    }
    fn fold_pattern(&mut self, node: Pattern<U>) -> Result<Pattern<Self::TargetU>, Self::Error> {
        fold_pattern(self, node)
    }
    fn fold_type_ignore(
        &mut self,
        node: TypeIgnore<U>,
    ) -> Result<TypeIgnore<Self::TargetU>, Self::Error> {
        fold_type_ignore(self, node)
    }
}
impl<T, U> Foldable<T, U> for Mod<T> {
    type Mapped = Mod<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_mod(self)
    }
}
pub fn fold_mod<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Mod<U>,
) -> Result<Mod<F::TargetU>, F::Error> {
    match node {
        Mod::Module(ModModule {
            body,
            type_ignores,
            custom,
        }) => {
            let custom = folder.map_user_cfg(custom)?;
            Ok(Mod::Module(ModModule {
                body: Foldable::fold(body, folder)?,
                type_ignores: Foldable::fold(type_ignores, folder)?,
                custom,
            }))
        }
        Mod::Interactive(ModInteractive { body, custom }) => {
            let custom = folder.map_user_cfg(custom)?;
            Ok(Mod::Interactive(ModInteractive {
                body: Foldable::fold(body, folder)?,
                custom,
            }))
        }
        Mod::Expression(ModExpression { body, custom }) => {
            let custom = folder.map_user_cfg(custom)?;
            Ok(Mod::Expression(ModExpression {
                body: Foldable::fold(body, folder)?,
                custom,
            }))
        }
        Mod::FunctionType(ModFunctionType {
            argtypes,
            returns,
            custom,
        }) => {
            let custom = folder.map_user_cfg(custom)?;
            Ok(Mod::FunctionType(ModFunctionType {
                argtypes: Foldable::fold(argtypes, folder)?,
                returns: Foldable::fold(returns, folder)?,
                custom,
            }))
        }
    }
}
impl<T, U> Foldable<T, U> for Stmt<T> {
    type Mapped = Stmt<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_stmt(self)
    }
}
pub fn fold_stmt<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Stmt<U>,
) -> Result<Stmt<F::TargetU>, F::Error> {
    match node {
        Stmt::FunctionDef(StmtFunctionDef {
            name,
            args,
            body,
            decorator_list,
            returns,
            type_comment,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::FunctionDef(StmtFunctionDef {
                name: Foldable::fold(name, folder)?,
                args: Foldable::fold(args, folder)?,
                body: Foldable::fold(body, folder)?,
                decorator_list: Foldable::fold(decorator_list, folder)?,
                returns: Foldable::fold(returns, folder)?,
                type_comment: Foldable::fold(type_comment, folder)?,
                custom,
            }))
        }
        Stmt::AsyncFunctionDef(StmtAsyncFunctionDef {
            name,
            args,
            body,
            decorator_list,
            returns,
            type_comment,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::AsyncFunctionDef(StmtAsyncFunctionDef {
                name: Foldable::fold(name, folder)?,
                args: Foldable::fold(args, folder)?,
                body: Foldable::fold(body, folder)?,
                decorator_list: Foldable::fold(decorator_list, folder)?,
                returns: Foldable::fold(returns, folder)?,
                type_comment: Foldable::fold(type_comment, folder)?,
                custom,
            }))
        }
        Stmt::ClassDef(StmtClassDef {
            name,
            bases,
            keywords,
            body,
            decorator_list,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::ClassDef(StmtClassDef {
                name: Foldable::fold(name, folder)?,
                bases: Foldable::fold(bases, folder)?,
                keywords: Foldable::fold(keywords, folder)?,
                body: Foldable::fold(body, folder)?,
                decorator_list: Foldable::fold(decorator_list, folder)?,
                custom,
            }))
        }
        Stmt::Return(StmtReturn { value, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Return(StmtReturn {
                value: Foldable::fold(value, folder)?,
                custom,
            }))
        }
        Stmt::Delete(StmtDelete { targets, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Delete(StmtDelete {
                targets: Foldable::fold(targets, folder)?,
                custom,
            }))
        }
        Stmt::Assign(StmtAssign {
            targets,
            value,
            type_comment,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Assign(StmtAssign {
                targets: Foldable::fold(targets, folder)?,
                value: Foldable::fold(value, folder)?,
                type_comment: Foldable::fold(type_comment, folder)?,
                custom,
            }))
        }
        Stmt::AugAssign(StmtAugAssign {
            target,
            op,
            value,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::AugAssign(StmtAugAssign {
                target: Foldable::fold(target, folder)?,
                op: Foldable::fold(op, folder)?,
                value: Foldable::fold(value, folder)?,
                custom,
            }))
        }
        Stmt::AnnAssign(StmtAnnAssign {
            target,
            annotation,
            value,
            simple,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::AnnAssign(StmtAnnAssign {
                target: Foldable::fold(target, folder)?,
                annotation: Foldable::fold(annotation, folder)?,
                value: Foldable::fold(value, folder)?,
                simple: Foldable::fold(simple, folder)?,
                custom,
            }))
        }
        Stmt::For(StmtFor {
            target,
            iter,
            body,
            orelse,
            type_comment,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::For(StmtFor {
                target: Foldable::fold(target, folder)?,
                iter: Foldable::fold(iter, folder)?,
                body: Foldable::fold(body, folder)?,
                orelse: Foldable::fold(orelse, folder)?,
                type_comment: Foldable::fold(type_comment, folder)?,
                custom,
            }))
        }
        Stmt::AsyncFor(StmtAsyncFor {
            target,
            iter,
            body,
            orelse,
            type_comment,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::AsyncFor(StmtAsyncFor {
                target: Foldable::fold(target, folder)?,
                iter: Foldable::fold(iter, folder)?,
                body: Foldable::fold(body, folder)?,
                orelse: Foldable::fold(orelse, folder)?,
                type_comment: Foldable::fold(type_comment, folder)?,
                custom,
            }))
        }
        Stmt::While(StmtWhile {
            test,
            body,
            orelse,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::While(StmtWhile {
                test: Foldable::fold(test, folder)?,
                body: Foldable::fold(body, folder)?,
                orelse: Foldable::fold(orelse, folder)?,
                custom,
            }))
        }
        Stmt::If(StmtIf {
            test,
            body,
            orelse,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::If(StmtIf {
                test: Foldable::fold(test, folder)?,
                body: Foldable::fold(body, folder)?,
                orelse: Foldable::fold(orelse, folder)?,
                custom,
            }))
        }
        Stmt::With(StmtWith {
            items,
            body,
            type_comment,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::With(StmtWith {
                items: Foldable::fold(items, folder)?,
                body: Foldable::fold(body, folder)?,
                type_comment: Foldable::fold(type_comment, folder)?,
                custom,
            }))
        }
        Stmt::AsyncWith(StmtAsyncWith {
            items,
            body,
            type_comment,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::AsyncWith(StmtAsyncWith {
                items: Foldable::fold(items, folder)?,
                body: Foldable::fold(body, folder)?,
                type_comment: Foldable::fold(type_comment, folder)?,
                custom,
            }))
        }
        Stmt::Match(StmtMatch {
            subject,
            cases,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Match(StmtMatch {
                subject: Foldable::fold(subject, folder)?,
                cases: Foldable::fold(cases, folder)?,
                custom,
            }))
        }
        Stmt::Raise(StmtRaise { exc, cause, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Raise(StmtRaise {
                exc: Foldable::fold(exc, folder)?,
                cause: Foldable::fold(cause, folder)?,
                custom,
            }))
        }
        Stmt::Try(StmtTry {
            body,
            handlers,
            orelse,
            finalbody,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Try(StmtTry {
                body: Foldable::fold(body, folder)?,
                handlers: Foldable::fold(handlers, folder)?,
                orelse: Foldable::fold(orelse, folder)?,
                finalbody: Foldable::fold(finalbody, folder)?,
                custom,
            }))
        }
        Stmt::TryStar(StmtTryStar {
            body,
            handlers,
            orelse,
            finalbody,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::TryStar(StmtTryStar {
                body: Foldable::fold(body, folder)?,
                handlers: Foldable::fold(handlers, folder)?,
                orelse: Foldable::fold(orelse, folder)?,
                finalbody: Foldable::fold(finalbody, folder)?,
                custom,
            }))
        }
        Stmt::Assert(StmtAssert { test, msg, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Assert(StmtAssert {
                test: Foldable::fold(test, folder)?,
                msg: Foldable::fold(msg, folder)?,
                custom,
            }))
        }
        Stmt::Import(StmtImport { names, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Import(StmtImport {
                names: Foldable::fold(names, folder)?,
                custom,
            }))
        }
        Stmt::ImportFrom(StmtImportFrom {
            module,
            names,
            level,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::ImportFrom(StmtImportFrom {
                module: Foldable::fold(module, folder)?,
                names: Foldable::fold(names, folder)?,
                level: Foldable::fold(level, folder)?,
                custom,
            }))
        }
        Stmt::Global(StmtGlobal { names, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Global(StmtGlobal {
                names: Foldable::fold(names, folder)?,
                custom,
            }))
        }
        Stmt::Nonlocal(StmtNonlocal { names, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Nonlocal(StmtNonlocal {
                names: Foldable::fold(names, folder)?,
                custom,
            }))
        }
        Stmt::Expr(StmtExpr { value, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Expr(StmtExpr {
                value: Foldable::fold(value, folder)?,
                custom,
            }))
        }
        Stmt::Pass(StmtPass { custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Pass(StmtPass { custom }))
        }
        Stmt::Break(StmtBreak { custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Break(StmtBreak { custom }))
        }
        Stmt::Continue(StmtContinue { custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Stmt::Continue(StmtContinue { custom }))
        }
    }
}
impl<T, U> Foldable<T, U> for Expr<T> {
    type Mapped = Expr<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_expr(self)
    }
}
pub fn fold_expr<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Expr<U>,
) -> Result<Expr<F::TargetU>, F::Error> {
    match node {
        Expr::BoolOp(ExprBoolOp { op, values, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::BoolOp(ExprBoolOp {
                op: Foldable::fold(op, folder)?,
                values: Foldable::fold(values, folder)?,
                custom,
            }))
        }
        Expr::NamedExpr(ExprNamedExpr {
            target,
            value,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::NamedExpr(ExprNamedExpr {
                target: Foldable::fold(target, folder)?,
                value: Foldable::fold(value, folder)?,
                custom,
            }))
        }
        Expr::BinOp(ExprBinOp {
            left,
            op,
            right,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::BinOp(ExprBinOp {
                left: Foldable::fold(left, folder)?,
                op: Foldable::fold(op, folder)?,
                right: Foldable::fold(right, folder)?,
                custom,
            }))
        }
        Expr::UnaryOp(ExprUnaryOp {
            op,
            operand,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::UnaryOp(ExprUnaryOp {
                op: Foldable::fold(op, folder)?,
                operand: Foldable::fold(operand, folder)?,
                custom,
            }))
        }
        Expr::Lambda(ExprLambda { args, body, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Lambda(ExprLambda {
                args: Foldable::fold(args, folder)?,
                body: Foldable::fold(body, folder)?,
                custom,
            }))
        }
        Expr::IfExp(ExprIfExp {
            test,
            body,
            orelse,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::IfExp(ExprIfExp {
                test: Foldable::fold(test, folder)?,
                body: Foldable::fold(body, folder)?,
                orelse: Foldable::fold(orelse, folder)?,
                custom,
            }))
        }
        Expr::Dict(ExprDict {
            keys,
            values,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Dict(ExprDict {
                keys: Foldable::fold(keys, folder)?,
                values: Foldable::fold(values, folder)?,
                custom,
            }))
        }
        Expr::Set(ExprSet { elts, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Set(ExprSet {
                elts: Foldable::fold(elts, folder)?,
                custom,
            }))
        }
        Expr::ListComp(ExprListComp {
            elt,
            generators,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::ListComp(ExprListComp {
                elt: Foldable::fold(elt, folder)?,
                generators: Foldable::fold(generators, folder)?,
                custom,
            }))
        }
        Expr::SetComp(ExprSetComp {
            elt,
            generators,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::SetComp(ExprSetComp {
                elt: Foldable::fold(elt, folder)?,
                generators: Foldable::fold(generators, folder)?,
                custom,
            }))
        }
        Expr::DictComp(ExprDictComp {
            key,
            value,
            generators,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::DictComp(ExprDictComp {
                key: Foldable::fold(key, folder)?,
                value: Foldable::fold(value, folder)?,
                generators: Foldable::fold(generators, folder)?,
                custom,
            }))
        }
        Expr::GeneratorExp(ExprGeneratorExp {
            elt,
            generators,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::GeneratorExp(ExprGeneratorExp {
                elt: Foldable::fold(elt, folder)?,
                generators: Foldable::fold(generators, folder)?,
                custom,
            }))
        }
        Expr::Await(ExprAwait { value, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Await(ExprAwait {
                value: Foldable::fold(value, folder)?,
                custom,
            }))
        }
        Expr::Yield(ExprYield { value, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Yield(ExprYield {
                value: Foldable::fold(value, folder)?,
                custom,
            }))
        }
        Expr::YieldFrom(ExprYieldFrom { value, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::YieldFrom(ExprYieldFrom {
                value: Foldable::fold(value, folder)?,
                custom,
            }))
        }
        Expr::Compare(ExprCompare {
            left,
            ops,
            comparators,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Compare(ExprCompare {
                left: Foldable::fold(left, folder)?,
                ops: Foldable::fold(ops, folder)?,
                comparators: Foldable::fold(comparators, folder)?,
                custom,
            }))
        }
        Expr::Call(ExprCall {
            func,
            args,
            keywords,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Call(ExprCall {
                func: Foldable::fold(func, folder)?,
                args: Foldable::fold(args, folder)?,
                keywords: Foldable::fold(keywords, folder)?,
                custom,
            }))
        }
        Expr::FormattedValue(ExprFormattedValue {
            value,
            conversion,
            format_spec,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::FormattedValue(ExprFormattedValue {
                value: Foldable::fold(value, folder)?,
                conversion: Foldable::fold(conversion, folder)?,
                format_spec: Foldable::fold(format_spec, folder)?,
                custom,
            }))
        }
        Expr::JoinedStr(ExprJoinedStr { values, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::JoinedStr(ExprJoinedStr {
                values: Foldable::fold(values, folder)?,
                custom,
            }))
        }
        Expr::Constant(ExprConstant {
            value,
            kind,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Constant(ExprConstant {
                value: Foldable::fold(value, folder)?,
                kind: Foldable::fold(kind, folder)?,
                custom,
            }))
        }
        Expr::Attribute(ExprAttribute {
            value,
            attr,
            ctx,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Attribute(ExprAttribute {
                value: Foldable::fold(value, folder)?,
                attr: Foldable::fold(attr, folder)?,
                ctx: Foldable::fold(ctx, folder)?,
                custom,
            }))
        }
        Expr::Subscript(ExprSubscript {
            value,
            slice,
            ctx,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Subscript(ExprSubscript {
                value: Foldable::fold(value, folder)?,
                slice: Foldable::fold(slice, folder)?,
                ctx: Foldable::fold(ctx, folder)?,
                custom,
            }))
        }
        Expr::Starred(ExprStarred { value, ctx, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Starred(ExprStarred {
                value: Foldable::fold(value, folder)?,
                ctx: Foldable::fold(ctx, folder)?,
                custom,
            }))
        }
        Expr::Name(ExprName { id, ctx, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Name(ExprName {
                id: Foldable::fold(id, folder)?,
                ctx: Foldable::fold(ctx, folder)?,
                custom,
            }))
        }
        Expr::List(ExprList { elts, ctx, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::List(ExprList {
                elts: Foldable::fold(elts, folder)?,
                ctx: Foldable::fold(ctx, folder)?,
                custom,
            }))
        }
        Expr::Tuple(ExprTuple { elts, ctx, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Tuple(ExprTuple {
                elts: Foldable::fold(elts, folder)?,
                ctx: Foldable::fold(ctx, folder)?,
                custom,
            }))
        }
        Expr::Slice(ExprSlice {
            lower,
            upper,
            step,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Expr::Slice(ExprSlice {
                lower: Foldable::fold(lower, folder)?,
                upper: Foldable::fold(upper, folder)?,
                step: Foldable::fold(step, folder)?,
                custom,
            }))
        }
    }
}
impl<T, U> Foldable<T, U> for ExprContext {
    type Mapped = ExprContext;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_expr_context(self)
    }
}
pub fn fold_expr_context<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: ExprContext,
) -> Result<ExprContext, F::Error> {
    Ok(node)
}
impl<T, U> Foldable<T, U> for Boolop {
    type Mapped = Boolop;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_boolop(self)
    }
}
pub fn fold_boolop<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Boolop,
) -> Result<Boolop, F::Error> {
    Ok(node)
}
impl<T, U> Foldable<T, U> for Operator {
    type Mapped = Operator;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_operator(self)
    }
}
pub fn fold_operator<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Operator,
) -> Result<Operator, F::Error> {
    Ok(node)
}
impl<T, U> Foldable<T, U> for Unaryop {
    type Mapped = Unaryop;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_unaryop(self)
    }
}
pub fn fold_unaryop<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Unaryop,
) -> Result<Unaryop, F::Error> {
    Ok(node)
}
impl<T, U> Foldable<T, U> for Cmpop {
    type Mapped = Cmpop;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_cmpop(self)
    }
}
pub fn fold_cmpop<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Cmpop,
) -> Result<Cmpop, F::Error> {
    Ok(node)
}
impl<T, U> Foldable<T, U> for Comprehension<T> {
    type Mapped = Comprehension<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_comprehension(self)
    }
}
pub fn fold_comprehension<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Comprehension<U>,
) -> Result<Comprehension<F::TargetU>, F::Error> {
    let Comprehension {
        target,
        iter,
        ifs,
        is_async,
        custom,
    } = node;
    let custom = folder.map_user_cfg(custom)?;
    Ok(Comprehension {
        target: Foldable::fold(target, folder)?,
        iter: Foldable::fold(iter, folder)?,
        ifs: Foldable::fold(ifs, folder)?,
        is_async: Foldable::fold(is_async, folder)?,
        custom,
    })
}
impl<T, U> Foldable<T, U> for Excepthandler<T> {
    type Mapped = Excepthandler<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_excepthandler(self)
    }
}
pub fn fold_excepthandler<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Excepthandler<U>,
) -> Result<Excepthandler<F::TargetU>, F::Error> {
    match node {
        Excepthandler::ExceptHandler(ExcepthandlerExceptHandler {
            type_,
            name,
            body,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Excepthandler::ExceptHandler(ExcepthandlerExceptHandler {
                type_: Foldable::fold(type_, folder)?,
                name: Foldable::fold(name, folder)?,
                body: Foldable::fold(body, folder)?,
                custom,
            }))
        }
    }
}
impl<T, U> Foldable<T, U> for Arguments<T> {
    type Mapped = Arguments<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_arguments(self)
    }
}
pub fn fold_arguments<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Arguments<U>,
) -> Result<Arguments<F::TargetU>, F::Error> {
    let Arguments {
        posonlyargs,
        args,
        vararg,
        kwonlyargs,
        kw_defaults,
        kwarg,
        defaults,
        custom,
    } = node;
    let custom = folder.map_user_cfg(custom)?;
    Ok(Arguments {
        posonlyargs: Foldable::fold(posonlyargs, folder)?,
        args: Foldable::fold(args, folder)?,
        vararg: Foldable::fold(vararg, folder)?,
        kwonlyargs: Foldable::fold(kwonlyargs, folder)?,
        kw_defaults: Foldable::fold(kw_defaults, folder)?,
        kwarg: Foldable::fold(kwarg, folder)?,
        defaults: Foldable::fold(defaults, folder)?,
        custom,
    })
}
impl<T, U> Foldable<T, U> for Arg<T> {
    type Mapped = Arg<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_arg(self)
    }
}
pub fn fold_arg<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Arg<U>,
) -> Result<Arg<F::TargetU>, F::Error> {
    let Arg {
        arg,
        annotation,
        type_comment,
        custom,
    } = node;
    let custom = folder.map_user(custom)?;
    Ok(Arg {
        arg: Foldable::fold(arg, folder)?,
        annotation: Foldable::fold(annotation, folder)?,
        type_comment: Foldable::fold(type_comment, folder)?,
        custom,
    })
}
impl<T, U> Foldable<T, U> for Keyword<T> {
    type Mapped = Keyword<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_keyword(self)
    }
}
pub fn fold_keyword<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Keyword<U>,
) -> Result<Keyword<F::TargetU>, F::Error> {
    let Keyword { arg, value, custom } = node;
    let custom = folder.map_user(custom)?;
    Ok(Keyword {
        arg: Foldable::fold(arg, folder)?,
        value: Foldable::fold(value, folder)?,
        custom,
    })
}
impl<T, U> Foldable<T, U> for Alias<T> {
    type Mapped = Alias<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_alias(self)
    }
}
pub fn fold_alias<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Alias<U>,
) -> Result<Alias<F::TargetU>, F::Error> {
    let Alias {
        name,
        asname,
        custom,
    } = node;
    let custom = folder.map_user(custom)?;
    Ok(Alias {
        name: Foldable::fold(name, folder)?,
        asname: Foldable::fold(asname, folder)?,
        custom,
    })
}
impl<T, U> Foldable<T, U> for Withitem<T> {
    type Mapped = Withitem<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_withitem(self)
    }
}
pub fn fold_withitem<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Withitem<U>,
) -> Result<Withitem<F::TargetU>, F::Error> {
    let Withitem {
        context_expr,
        optional_vars,
        custom,
    } = node;
    let custom = folder.map_user_cfg(custom)?;
    Ok(Withitem {
        context_expr: Foldable::fold(context_expr, folder)?,
        optional_vars: Foldable::fold(optional_vars, folder)?,
        custom,
    })
}
impl<T, U> Foldable<T, U> for MatchCase<T> {
    type Mapped = MatchCase<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_match_case(self)
    }
}
pub fn fold_match_case<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: MatchCase<U>,
) -> Result<MatchCase<F::TargetU>, F::Error> {
    let MatchCase {
        pattern,
        guard,
        body,
        custom,
    } = node;
    let custom = folder.map_user_cfg(custom)?;
    Ok(MatchCase {
        pattern: Foldable::fold(pattern, folder)?,
        guard: Foldable::fold(guard, folder)?,
        body: Foldable::fold(body, folder)?,
        custom,
    })
}
impl<T, U> Foldable<T, U> for Pattern<T> {
    type Mapped = Pattern<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_pattern(self)
    }
}
pub fn fold_pattern<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: Pattern<U>,
) -> Result<Pattern<F::TargetU>, F::Error> {
    match node {
        Pattern::MatchValue(PatternMatchValue { value, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Pattern::MatchValue(PatternMatchValue {
                value: Foldable::fold(value, folder)?,
                custom,
            }))
        }
        Pattern::MatchSingleton(PatternMatchSingleton { value, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Pattern::MatchSingleton(PatternMatchSingleton {
                value: Foldable::fold(value, folder)?,
                custom,
            }))
        }
        Pattern::MatchSequence(PatternMatchSequence { patterns, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Pattern::MatchSequence(PatternMatchSequence {
                patterns: Foldable::fold(patterns, folder)?,
                custom,
            }))
        }
        Pattern::MatchMapping(PatternMatchMapping {
            keys,
            patterns,
            rest,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Pattern::MatchMapping(PatternMatchMapping {
                keys: Foldable::fold(keys, folder)?,
                patterns: Foldable::fold(patterns, folder)?,
                rest: Foldable::fold(rest, folder)?,
                custom,
            }))
        }
        Pattern::MatchClass(PatternMatchClass {
            cls,
            patterns,
            kwd_attrs,
            kwd_patterns,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Pattern::MatchClass(PatternMatchClass {
                cls: Foldable::fold(cls, folder)?,
                patterns: Foldable::fold(patterns, folder)?,
                kwd_attrs: Foldable::fold(kwd_attrs, folder)?,
                kwd_patterns: Foldable::fold(kwd_patterns, folder)?,
                custom,
            }))
        }
        Pattern::MatchStar(PatternMatchStar { name, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Pattern::MatchStar(PatternMatchStar {
                name: Foldable::fold(name, folder)?,
                custom,
            }))
        }
        Pattern::MatchAs(PatternMatchAs {
            pattern,
            name,
            custom,
        }) => {
            let custom = folder.map_user(custom)?;
            Ok(Pattern::MatchAs(PatternMatchAs {
                pattern: Foldable::fold(pattern, folder)?,
                name: Foldable::fold(name, folder)?,
                custom,
            }))
        }
        Pattern::MatchOr(PatternMatchOr { patterns, custom }) => {
            let custom = folder.map_user(custom)?;
            Ok(Pattern::MatchOr(PatternMatchOr {
                patterns: Foldable::fold(patterns, folder)?,
                custom,
            }))
        }
    }
}
impl<T, U> Foldable<T, U> for TypeIgnore<T> {
    type Mapped = TypeIgnore<U>;
    fn fold<F: Fold<T, TargetU = U> + ?Sized>(
        self,
        folder: &mut F,
    ) -> Result<Self::Mapped, F::Error> {
        folder.fold_type_ignore(self)
    }
}
pub fn fold_type_ignore<U, F: Fold<U> + ?Sized>(
    #[allow(unused)] folder: &mut F,
    node: TypeIgnore<U>,
) -> Result<TypeIgnore<F::TargetU>, F::Error> {
    match node {
        TypeIgnore::TypeIgnore(TypeIgnoreTypeIgnore {
            lineno,
            tag,
            custom,
        }) => {
            let custom = folder.map_user_cfg(custom)?;
            Ok(TypeIgnore::TypeIgnore(TypeIgnoreTypeIgnore {
                lineno: Foldable::fold(lineno, folder)?,
                tag: Foldable::fold(tag, folder)?,
                custom,
            }))
        }
    }
}
