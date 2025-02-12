//! This module compiles parsed `Expr`s into an optimized Ast node called an `OP`.
//! The compiled form is much faster, especially for constants.
//!
//! # Compile-time Optimizations
//!
//! ## Constant Folding
//! Operations with constants can be calculated at compile time so
//! they don't need to be calculated during `eval()`.
//!
//! For example, `1 + x + 1` will be compiled into `x + 2`, saving some time during `eval()`.
//!
//! If the entire expression only consists of constants (no variables),
//! then the expression can be reduced to a final result at compile time,
//! resulting in near-native speed during `eval()`.
//!
//! ## Algebraic Simplification
//! * Subtraction is converted to Addition.
//! * Division is converted to Multiplication.
//! * Built-in functions with constant arguments are evaluated.
//! * Constant terms are combined.
//! * Logical operator short-circuits are applied and no-op branches are discarded.
//!
//! ## Optimized Memory Layout and Execution
//! * Variable-length `Expr`/`Value` Ast nodes are converted into constant-sized `OP` nodes.
//! * The `F` enumeration helps to eliminate expensive function calls.

use indexmap::{map::Entry, IndexMap};

use crate::builtins;
use crate::context::*;
use crate::debug_indexed_list;
use crate::error::Error;
use crate::float::*;
use crate::op::{self, *};
use crate::parser::*;
use crate::tokens::{self, *};
use crate::{compile_op, map2, map3, signature};
use std::fmt::{self, Debug};
use std::ops::Add;
use std::usize;

impl Ast {
    pub fn compile<M: Module>(&self, ex: &mut Expression<M>) -> Result<(), Error> {
        ex.compile(self)
    }
}

pub fn compile<M: Module>(ast: &Ast, ex: &mut Expression<M>) -> Result<(), Error> {
    Expression::compile(ex, ast)
}

/// You must `use` the `Compiler` trait before you can call `.compile()` on parsed `Expr`s.
pub trait Compiler<M: Module> {
    /// Turns a parsed `Expr` into a compiled `OP`.
    ///
    /// Cannot fail, unless you run out of memory.
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP, Error>;
}

pub struct Resolver<'e, 'm, M: Module, CTX: Context> {
    expr: &'e Expression<'m, M>,
    start: usize,
    locals_buf: Buffer<CTX::T>,
    ctx: CTX,
}
/// `Expression` is where `compile()` results are stored.
pub struct Expression<'m, M: Module> {
    module: &'m M,
    locals: IndexMap<String, ARG>,
    pub(crate) ops: Vec<OP>,
}

impl<'m, M: Module> Expression<'m, M> {
    pub fn new(module: &'m M) -> Self {
        Self {
            module,
            locals: IndexMap::with_capacity(2),
            ops: Vec::new(),
        }
    }

    #[inline]
    pub fn compile(&mut self, ast: &Ast) -> Result<(), Error> {
        self.ops.clear();

        let mut offset = 0;
        let mut stores = Vec::with_capacity(2);
        if let Some(Statement::Return(last_ex)) = ast.stmts.last() {
            for stmt in &ast.stmts {
                match stmt {
                    Statement::OpAssign(name, aop, ex) => match aop {
                        Assign => {
                            let op = ex.compile(ast, self)?;
                            let arg = op.into_arg(self);
                            match arg {
                                F(F::I(i)) => match self.locals.entry(name.into()) {
                                    Entry::Vacant(e) => {
                                        e.insert(F(F::VAR(LOCAL(offset))));
                                        stores.push(FOP(FOP::STORE(offset, i)));
                                        offset += 1;
                                    }
                                    Entry::Occupied(mut e) => {
                                        if let F(F::VAR(LOCAL(offset))) = e.get() {
                                            stores.push(FOP(FOP::STORE(*offset, i)));
                                        } else {
                                            *e.get_mut() = F(F::VAR(LOCAL(offset)));
                                            stores.push(FOP(FOP::STORE(offset, i)));
                                            offset += 1;
                                        }
                                    }
                                },
                                F2(F2::I(i)) => match self.locals.entry(name.into()) {
                                    Entry::Vacant(e) => {
                                        e.insert(F2(F2::VAR(LOCAL(offset))));
                                        stores.push(FOP2(FOP2::STORE(offset, i)));
                                        offset += 2;
                                    }
                                    Entry::Occupied(mut e) => {
                                        if let F2(F2::VAR(LOCAL(offset))) = e.get() {
                                            stores.push(FOP2(FOP2::STORE(*offset, i)));
                                        } else {
                                            *e.get_mut() = F2(F2::VAR(LOCAL(offset)));
                                            stores.push(FOP2(FOP2::STORE(offset, i)));
                                            offset += 2;
                                        }
                                    }
                                },
                                F3(F3::I(i)) => match self.locals.entry(name.into()) {
                                    Entry::Vacant(e) => {
                                        e.insert(F3(F3::VAR(LOCAL(offset))));
                                        stores.push(FOP3(FOP3::STORE(offset, i)));
                                        offset += 3;
                                    }
                                    Entry::Occupied(mut e) => {
                                        if let F3(F3::VAR(LOCAL(offset))) = e.get() {
                                            stores.push(FOP3(FOP3::STORE(*offset, i)));
                                        } else {
                                            *e.get_mut() = F3(F3::VAR(LOCAL(offset)));
                                            stores.push(FOP3(FOP3::STORE(offset, i)));
                                            offset += 3;
                                        }
                                    }
                                },
                                B(B::I(i)) => match self.locals.entry(name.into()) {
                                    Entry::Vacant(e) => {
                                        e.insert(B(B::VAR(LOCAL(offset))));
                                        stores.push(BOP(BOP::STORE(offset, i)));
                                        offset += 1;
                                    }
                                    Entry::Occupied(mut e) => {
                                        if let B(B::VAR(LOCAL(offset))) = e.get() {
                                            stores.push(BOP(BOP::STORE(*offset, i)));
                                        } else {
                                            *e.get_mut() = B(B::VAR(LOCAL(offset)));
                                            stores.push(BOP(BOP::STORE(offset, i)));
                                            offset += 1;
                                        }
                                    }
                                },
                                _ => {
                                    self.locals.insert(name.into(), arg);
                                }
                            }
                        }
                        _ => unimplemented!(),
                    },
                    _ => {} // Statement::Return(e) => e.compile(ast, self),
                }
            }

            let op = last_ex.compile(ast, self)?;
            self.ops.push(op);
            self.ops.append(&mut stores);
            Ok(())
        } else {
            Err(Error::InvalidType("Nothing returned".into()))
        }
    }

    #[inline]
    pub fn last(&self) -> Option<&OP> {
        self.ops.last()
    }

    /// Returns a reference to the [`OP`](../compiler/enum.OP.html)
    /// located at `i` within the `Expression.ops'.
    ///
    /// If `i` is out-of-bounds, a reference to a default `OP` is returned.
    ///
    #[inline]
    pub fn get(&self, i: usize) -> &OP {
        // unsafe{self.ops.get_unchecked(i)}
        self.ops.get(i).unwrap()
    }

    /// Appends an `OP` to `Expression.ops`.
    #[inline]
    pub fn push(&mut self, op: OP) -> usize {
        let i = self.ops.len();
        self.ops.push(op);
        i
    }

    /// Removes an `OP` from `Expression.ops` as efficiently as possible.
    #[inline]
    pub fn pop(&mut self) -> OP {
        self.ops.pop().unwrap()
    }

    /// Clears all data from `Expression.ops`.
    #[inline]
    pub fn clear(&mut self) {
        self.ops.clear();
        self.locals.clear();
    }
}

pub trait IntoArg<M: Module, T>: Sized {
    fn into_arg(self, ex: &mut Expression<M>) -> T;
}

impl<M: Module> IntoArg<M, ARG> for OP {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> ARG {
        match self {
            FOP(f) => F(f.into_arg(ex)),
            FOP2(f2) => F2(f2.into_arg(ex)),
            FOP3(f3) => F3(f3.into_arg(ex)),
            BOP(b) => B(b.into_arg(ex)),
        }
    }
}

impl<M: Module> IntoArg<M, B> for BOP {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> B {
        match self {
            BOP::CONST(c) => B::CONST(c),
            _ => B::I(ex.push(BOP(self))),
        }
    }
}

impl<M: Module> IntoArg<M, F> for BOP {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> F {
        match self {
            BOP::CONST(c) => F::CONST(c.into()),
            _ => F::I(ex.push(BOP(self))),
        }
    }
}

impl<M: Module> IntoArg<M, F2> for BOP {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> F2 {
        match self {
            BOP::CONST(c) => F2::CONST([c.into(); 2]),
            _ => F2::F(F::I(ex.push(BOP(self)))),
        }
    }
}

impl<M: Module> IntoArg<M, F3> for BOP {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> F3 {
        match self {
            BOP::CONST(c) => F3::CONST([c.into(); 3]),
            _ => F3::F(F::I(ex.push(BOP(self)))),
        }
    }
}

impl<M: Module> IntoArg<M, F> for FOP {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> F {
        match self {
            FOP::CONST(c) => F::CONST(c),
            FOP::VAR(v) => F::VAR(v),
            _ => F::I(ex.push(FOP(self))),
        }
    }
}

impl<M: Module> IntoArg<M, B> for FOP {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> B {
        match self {
            FOP::CONST(c) => B::CONST((c != 0.0).into()),
            FOP::VAR(v) => B::VAR(v),
            _ => B::I(ex.push(FOP(self))),
        }
    }
}

impl<M: Module> IntoArg<M, F2> for FOP {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> F2 {
        match self {
            FOP::CONST(c) => F2::CONST([c; 2]),
            _ => F2::F(F::I(ex.push(FOP(self)))),
        }
    }
}

impl<M: Module> IntoArg<M, F3> for FOP {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> F3 {
        match self {
            FOP::CONST(c) => F3::CONST([c; 3]),
            _ => F3::F(F::I(ex.push(FOP(self)))),
        }
    }
}

impl<M: Module> IntoArg<M, F2> for FOP2 {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> F2 {
        match self {
            FOP2::CONST(c) => F2::CONST(c),
            FOP2::VAR(v) => F2::VAR(v),
            _ => F2::I(ex.push(FOP2(self))),
        }
    }
}

impl<M: Module> IntoArg<M, F3> for FOP3 {
    #[inline]
    fn into_arg(self, ex: &mut Expression<M>) -> F3 {
        match self {
            FOP3::CONST(c) => F3::CONST(c),
            FOP3::VAR(v) => F3::VAR(v),
            _ => F3::I(ex.push(FOP3(self))),
        }
    }
}

impl<M: Module> Debug for Expression<'_, M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        writeln!(f, "{:?}", self.locals)?;
        debug_indexed_list(f, &self.ops)?;
        Ok(())
    }
}

impl<M: Module> Expression<'_, M> {
    #[inline]
    fn neg_wrap(&mut self, op: OP) -> OP {
        match op {
            FOP(FOP::NEG(_)) | FOP2(FOP2::NEG(_)) | FOP3(FOP3::NEG(_)) => self.pop(),
            FOP(FOP::CONST(c)) => FOP(FOP::CONST(-c)),
            FOP(op) => FOP(FOP::NEG(op.into_arg(self))),

            FOP2(FOP2::CONST([x, y])) => FOP2(FOP2::CONST([-x, -y])),
            FOP2(op) => FOP2(FOP2::NEG(op.into_arg(self))),

            FOP3(FOP3::CONST([x, y, z])) => FOP3(FOP3::CONST([-x, -y, -z])),
            FOP3(op) => FOP3(FOP3::NEG(op.into_arg(self))),

            BOP(BOP::CONST(c)) => FOP(FOP::CONST(-f64::from(c))),
            BOP(op) => FOP(FOP::NEG(op.into_arg(self))),
        }
    }

    #[inline]
    fn not_wrap(&mut self, op: OP) -> Result<OP, Error> {
        match op {
            BOP(BOP::NOT(_)) => Ok(self.pop()),
            BOP(BOP::CONST(c)) => Ok(BOP(BOP::CONST(!c))),
            BOP(op) => Ok(BOP(BOP::NOT(op.into_arg(self)))),

            FOP(FOP::CONST(c)) => Ok(BOP(BOP::CONST((c == 0.0).into()))),
            FOP(op) => Ok(BOP(BOP::NOT(op.into_arg(self)))),
            _ => Err(Error::InvalidType(
                "invalid operand type for ! operator".into(),
            )),
        }
    }

    #[inline]
    fn inv_wrap(&mut self, op: OP) -> OP {
        match op {
            FOP(FOP::INV(_)) | FOP2(FOP2::INV(_)) => self.pop(),
            FOP(FOP::CONST(c)) => FOP(FOP::CONST(c.recip())),
            FOP(op) => FOP(FOP::INV(op.into_arg(self))),

            FOP2(FOP2::CONST([x, y])) => FOP2(FOP2::CONST([x.recip(), y.recip()])),
            FOP2(op) => FOP2(FOP2::INV(op.into_arg(self))),

            FOP3(FOP3::CONST([x, y, z])) => FOP3(FOP3::CONST([x.recip(), y.recip(), z.recip()])),
            FOP3(op) => FOP3(FOP3::INV(op.into_arg(self))),

            BOP(BOP::CONST(c)) => FOP(FOP::CONST(f64::from(c).recip())),
            BOP(op) => FOP(FOP::INV(op.into_arg(self))),
        }
    }

    #[inline]
    fn compile_mul(&mut self, sorted_ops: Vec<OP>) -> Result<OP, Error> {
        let mut const_out = FOP(FOP::CONST(1.0));
        let mut out = FOP(FOP::CONST(1.0));

        for op in sorted_ops {
            match (out, op) {
                (FOP(FOP::CONST(c0)), FOP(FOP::CONST(c1))) => {
                    out = FOP(FOP::CONST(c0 * c1));
                }
                (FOP(FOP::CONST(c0)), FOP2(FOP2::CONST([cx1, cy1]))) => {
                    out = FOP2(FOP2::CONST([c0 * cx1, c0 * cy1]));
                }
                (FOP2(FOP2::CONST(c0)), FOP2(FOP2::CONST(c1))) => {
                    out = FOP2(FOP2::CONST(map2!(std::ops::Mul::mul, c0, c1)));
                }
                (FOP(FOP::CONST(c0)), FOP3(FOP3::CONST([cx1, cy1, cz1]))) => {
                    out = FOP3(FOP3::CONST([c0 * cx1, c0 * cy1, c0 * cz1]));
                }
                (FOP3(FOP3::CONST(c0)), FOP3(FOP3::CONST(c1))) => {
                    out = FOP3(FOP3::CONST(map3!(std::ops::Mul::mul, c0, c1)));
                }
                (op1 @ (FOP(FOP::CONST(_)) | FOP2(FOP2::CONST(_)) | FOP3(FOP3::CONST(_))), op2) => {
                    const_out = op1;
                    out = op2;
                }

                (FOP(fop0), FOP(fop1)) => {
                    out = FOP(FOP::MUL(fop0.into_arg(self), fop1.into_arg(self)));
                }
                (FOP(fop0), FOP2(uop1)) => {
                    out = FOP2(FOP2::MUL(fop0.into_arg(self), uop1.into_arg(self)));
                }
                (FOP2(uop0), FOP2(uop1)) => {
                    out = FOP2(FOP2::MUL(uop0.into_arg(self), uop1.into_arg(self)));
                }
                (FOP(fop0), FOP3(uop1)) => {
                    out = FOP3(FOP3::MUL(fop0.into_arg(self), uop1.into_arg(self)));
                }
                (FOP3(uop0), FOP3(uop1)) => {
                    out = FOP3(FOP3::MUL(uop0.into_arg(self), uop1.into_arg(self)));
                }
                (l, r) => {
                    return Err(Error::InvalidType(
                        "invalid operands type for '*' operator".into(),
                    ))
                }
            }
        }

        match (const_out, out) {
            (FOP(FOP::CONST(1.0)), op1 @ FOP(_)) => Ok(op1),
            (FOP(fop0), FOP(fop1)) => Ok(FOP(FOP::MUL(fop0.into_arg(self), fop1.into_arg(self)))),
            (FOP2(FOP2::CONST([1.0, 1.0])), op1 @ FOP2(_)) => Ok(op1),
            (op0 @ (FOP(_) | FOP2(_)), op1 @ (FOP(_) | FOP2(_))) => {
                let l = op0.into_arg(self).try_into().unwrap();
                let r = op1.into_arg(self).try_into().unwrap();
                Ok(FOP2(FOP2::MUL(l, r)))
            }
            (FOP3(FOP3::CONST([1.0, 1.0, 1.0])), op1 @ FOP3(_)) => Ok(op1),
            (op0 @ (FOP(_) | FOP3(_)), op1 @ (FOP(_) | FOP3(_))) => {
                let l = op0.into_arg(self).try_into().unwrap();
                let r = op1.into_arg(self).try_into().unwrap();
                Ok(FOP3(FOP3::MUL(l, r)))
            }
            _ => Err(Error::Unreachable),
        }
    }

    #[inline]
    fn compile_add(&mut self, sorted_ops: Vec<OP>) -> Result<OP, Error> {
        let mut const_out = FOP(FOP::CONST(0.0));
        let mut out = FOP(FOP::CONST(0.0));

        for op in sorted_ops {
            match (out, op) {
                (FOP(FOP::CONST(c0)), FOP(FOP::CONST(c1))) => {
                    out = FOP(FOP::CONST(c0 + c1));
                }
                (FOP(FOP::CONST(c0)), FOP2(FOP2::CONST([cx1, cy1]))) => {
                    out = FOP2(FOP2::CONST([c0 + cx1, c0 + cy1]));
                }
                (FOP2(FOP2::CONST(c0)), FOP2(FOP2::CONST(c1))) => {
                    out = FOP2(FOP2::CONST(map2!(std::ops::Add::add, c0, c1)));
                }
                (FOP(FOP::CONST(c0)), FOP3(FOP3::CONST([cx1, cy1, cz1]))) => {
                    out = FOP3(FOP3::CONST([c0 + cx1, c0 + cy1, c0 + cz1]));
                }
                (FOP3(FOP3::CONST(c0)), FOP3(FOP3::CONST(c1))) => {
                    out = FOP3(FOP3::CONST(map3!(std::ops::Add::add, c0, c1)));
                }
                (op1 @ (FOP(FOP::CONST(_)) | FOP2(FOP2::CONST(_)) | FOP3(FOP3::CONST(_))), op2) => {
                    const_out = op1;
                    out = op2;
                }

                (FOP(fop0), FOP(fop1)) => {
                    out = FOP(FOP::ADD(fop0.into_arg(self), fop1.into_arg(self)));
                }
                (FOP(fop0), FOP2(uop1)) => {
                    out = FOP2(FOP2::ADD(fop0.into_arg(self), uop1.into_arg(self)));
                }
                (FOP2(uop0), FOP2(uop1)) => {
                    out = FOP2(FOP2::ADD(uop0.into_arg(self), uop1.into_arg(self)));
                }
                (FOP(fop0), FOP3(uop1)) => {
                    out = FOP3(FOP3::ADD(fop0.into_arg(self), uop1.into_arg(self)));
                }
                (FOP3(uop0), FOP3(uop1)) => {
                    out = FOP3(FOP3::ADD(uop0.into_arg(self), uop1.into_arg(self)));
                }
                (l, r) => {
                    return Err(Error::InvalidType(
                        "invalid operands type for '+' operator".into(),
                    ))
                }
            }
        }

        match (const_out, out) {
            (FOP(FOP::CONST(0.0)), op1 @ FOP(_)) => Ok(op1),
            (FOP(fop0), FOP(fop1)) => Ok(FOP(FOP::ADD(fop0.into_arg(self), fop1.into_arg(self)))),
            (FOP2(FOP2::CONST([0.0, 0.0])), op1 @ FOP2(_)) => Ok(op1),
            (op0 @ (FOP(_) | FOP2(_)), op1 @ (FOP(_) | FOP2(_))) => {
                let l = op0.into_arg(self).try_into().unwrap();
                let r = op1.into_arg(self).try_into().unwrap();
                Ok(FOP2(FOP2::ADD(l, r)))
            }
            (FOP3(FOP3::CONST([0.0, 0.0, 0.0])), op1 @ FOP3(_)) => Ok(op1),
            (op0 @ (FOP(_) | FOP3(_)), op1 @ (FOP(_) | FOP3(_))) => {
                let l = op0.into_arg(self).try_into().unwrap();
                let r = op1.into_arg(self).try_into().unwrap();
                Ok(FOP3(FOP3::ADD(l, r)))
            }
            _ => Err(Error::Unreachable),
        }
    }

    #[inline]
    fn push_add_leafs(&mut self, ops: &mut Vec<OP>, op: OP) {
        match op {
            FOP(FOP::ADD(l, r)) => {
                self.push_f_add_leaf(ops, r);
                self.push_f_add_leaf(ops, l);
            }
            FOP2(FOP2::ADD(l, r)) => {
                self.push_f2_add_leaf(ops, r);
                self.push_f2_add_leaf(ops, l);
            }
            FOP3(FOP3::ADD(l, r)) => {
                self.push_f3_add_leaf(ops, r);
                self.push_f3_add_leaf(ops, l);
            }
            _ => {
                ops.push(op);
            }
        }
    }
    fn push_f_add_leaf(&mut self, ops: &mut Vec<OP>, f: F) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match f {
            F::I(_) => {
                let op = self.pop();
                self.push_add_leafs(ops, op);
            }
            F::CONST(c) => ops.push(FOP(FOP::CONST(c))),
            F::VAR(i) => ops.push(FOP(FOP::VAR(i))),
        };
    }
    fn push_f2_add_leaf(&mut self, ops: &mut Vec<OP>, f2: F2) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match f2 {
            F2::I(_) => {
                let op = self.pop();
                self.push_add_leafs(ops, op);
            }

            F2::CONST(c) => ops.push(FOP2(FOP2::CONST(c))),
            F2::VAR(i) => ops.push(FOP2(FOP2::VAR(i))),
            F2::F(f) => match f {
                F::I(_) => {
                    let op = self.pop();
                    self.push_add_leafs(ops, op);
                }
                F::CONST(c) => ops.push(FOP(FOP::CONST(c))),
                F::VAR(i) => ops.push(FOP(FOP::VAR(i))),
            },
        };
    }

    fn push_f3_add_leaf(&mut self, ops: &mut Vec<OP>, f3: F3) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match f3 {
            F3::I(_) => {
                let op = self.pop();
                self.push_add_leafs(ops, op);
            }

            F3::CONST(c) => ops.push(FOP3(FOP3::CONST(c))),
            F3::VAR(i) => ops.push(FOP3(FOP3::VAR(i))),
            F3::F(f) => match f {
                F::I(_) => {
                    let op = self.pop();
                    self.push_add_leafs(ops, op);
                }
                F::CONST(c) => ops.push(FOP(FOP::CONST(c))),
                F::VAR(i) => ops.push(FOP(FOP::VAR(i))),
            },
        };
    }

    #[inline]
    fn push_mul_leafs(&mut self, ops: &mut Vec<OP>, op: OP) {
        match op {
            FOP(FOP::MUL(l, r)) => {
                self.push_f_mul_leaf(ops, r);
                self.push_f_mul_leaf(ops, l);
            }
            FOP2(FOP2::MUL(l, r)) => {
                self.push_f2_mul_leaf(ops, r);
                self.push_f2_mul_leaf(ops, l);
            }
            FOP3(FOP3::MUL(l, r)) => {
                self.push_f3_mul_leaf(ops, r);
                self.push_f3_mul_leaf(ops, l);
            }
            _ => {
                ops.push(op);
            }
        }
    }
    fn push_f_mul_leaf(&mut self, ops: &mut Vec<OP>, f: F) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match f {
            F::I(_) => {
                let op = self.pop();
                self.push_mul_leafs(ops, op);
            }
            F::CONST(c) => ops.push(FOP(FOP::CONST(c))),
            F::VAR(i) => ops.push(FOP(FOP::VAR(i))),
        };
    }

    fn push_f2_mul_leaf(&mut self, ops: &mut Vec<OP>, f2: F2) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match f2 {
            F2::I(_) => {
                let op = self.pop();
                self.push_mul_leafs(ops, op);
            }

            F2::CONST(c) => ops.push(FOP2(FOP2::CONST(c))),
            F2::VAR(i) => ops.push(FOP2(FOP2::VAR(i))),
            F2::F(f) => match f {
                F::I(_) => {
                    let op = self.pop();
                    self.push_mul_leafs(ops, op);
                }
                F::CONST(c) => ops.push(FOP(FOP::CONST(c))),
                F::VAR(i) => ops.push(FOP(FOP::VAR(i))),
            },
        };
    }

    fn push_f3_mul_leaf(&mut self, ops: &mut Vec<OP>, f3: F3) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match f3 {
            F3::I(_) => {
                let op = self.pop();
                self.push_mul_leafs(ops, op);
            }

            F3::CONST(c) => ops.push(FOP3(FOP3::CONST(c))),
            F3::VAR(i) => ops.push(FOP3(FOP3::VAR(i))),
            F3::F(f) => match f {
                F::I(_) => {
                    let op = self.pop();
                    self.push_mul_leafs(ops, op);
                }
                F::CONST(c) => ops.push(FOP(FOP::CONST(c))),
                F::VAR(i) => ops.push(FOP(FOP::VAR(i))),
            },
        }
    }
}

#[derive(Debug)]
struct ExprSlice<'s>(&'s Value, Vec<&'s ExprPair>);

impl<'s> ExprSlice<'s> {
    fn new(first: &Value) -> ExprSlice<'_> {
        ExprSlice(first, Vec::with_capacity(8))
    }

    #[inline]
    fn from_expr(ex: &Expr) -> ExprSlice<'_> {
        let mut sl = ExprSlice::new(&ex.0);
        for exprpairref in ex.1.iter() {
            sl.1.push(exprpairref)
        }
        sl
    }

    #[inline]
    fn split(&self, bop: BinaryOp, dst: &mut Vec<ExprSlice<'s>>) {
        dst.push(ExprSlice::new(&self.0));
        for exprpair in self.1.iter() {
            if exprpair.0 == bop {
                dst.push(ExprSlice::new(&exprpair.1));
            } else if let Some(cur) = dst.last_mut() {
                cur.1.push(exprpair);
            }
        }
    }

    #[inline]
    fn split_multi(
        &self,
        search: &[BinaryOp],
        xsdst: &mut Vec<ExprSlice<'s>>,
        opdst: &mut Vec<&'s BinaryOp>,
    ) {
        xsdst.push(ExprSlice::new(&self.0));
        for exprpair in self.1.iter() {
            if search.contains(&exprpair.0) {
                xsdst.push(ExprSlice::new(&exprpair.1));
                opdst.push(&exprpair.0);
            } else if let Some(cur) = xsdst.last_mut() {
                cur.1.push(exprpair);
            }
        }
    }
}

impl<M: Module> Compiler<M> for ExprSlice<'_> {
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP, Error> {
        // Associative:  (2+3)+4 = 2+(3+4)
        // Commutative:  1+2 = 2+1
        //
        //          Only         Only
        // Neither  Associative  Commutative  Both
        // -------  -----------  -----------  ----
        // FGTE      (none)       (none)       OR
        // FLTE                                AND
        // FGT                                 FNE
        // FLT                                 FEQ
        // Minus (opt with neg & add)         Plus
        // Div (opt with inv & mul)           FMUL
        // FMOD
        // FEXP

        // Find the lowest-priority BinaryOp:
        let mut lowest_op = match self.1.first() {
            Some(p0) => p0.0,
            None => return self.0.compile(ast, ex),
        };
        for exprpair in self.1.iter() {
            if exprpair.0 < lowest_op {
                lowest_op = exprpair.0
            }
        }

        // All comparisons have equal precedence:
        if lowest_op == EQ
            || lowest_op == NE
            || lowest_op == LT
            || lowest_op == GT
            || lowest_op == LE
            || lowest_op == GE
        {
            let mut ops = Vec::<&BinaryOp>::with_capacity(4);
            let mut xss = Vec::<ExprSlice>::with_capacity(ops.len() + 1);
            self.split_multi(&[EQ, NE, LT, GT, LE, GE], &mut xss, &mut ops);
            let mut out = xss.first().unwrap().compile(ast, ex)?;

            for (i, _op) in ops.into_iter().enumerate() {
                let op = xss.get(i + 1).unwrap().compile(ast, ex)?;
                let l = out.into_arg(ex).convert_bool();
                let r = op.into_arg(ex).convert_bool();

                out = match (_op, l, r) {
                    (EQ, F(F::CONST(l)), F(F::CONST(r))) => BOP(BOP::CONST(l == r)),
                    (EQ, F(l), F(r)) => BOP(BOP::EQ(l, r)),
                    (EQ, l @ (F(_) | F2(_)), r @ (F(_) | F2(_))) => {
                        let l = l.try_into().unwrap();
                        let r = r.try_into().unwrap();
                        match (l, r) {
                            (F2::CONST(l), F2::CONST(r)) => BOP(BOP::CONST(l == r)),
                            _ => BOP(BOP::EQ2(l, r)),
                        }
                    }
                    (EQ, l @ (F(_) | F3(_)), r @ (F(_) | F3(_))) => {
                        let l = l.try_into().unwrap();
                        let r = r.try_into().unwrap();
                        match (l, r) {
                            (F3::CONST(l), F3::CONST(r)) => BOP(BOP::CONST(l == r)),
                            _ => BOP(BOP::EQ3(l, r)),
                        }
                    }

                    (NE, F(F::CONST(l)), F(F::CONST(r))) => BOP(BOP::CONST(l != r)),
                    (NE, F(l), F(r)) => BOP(BOP::NE(l, r)),
                    (NE, l @ (F(_) | F2(_)), r @ (F(_) | F2(_))) => {
                        let l = l.try_into().unwrap();
                        let r = r.try_into().unwrap();
                        match (l, r) {
                            (F2::CONST(l), F2::CONST(r)) => BOP(BOP::CONST(l != r)),
                            _ => BOP(BOP::NE2(l, r)),
                        }
                    }
                    (NE, l @ (F(_) | F3(_)), r @ (F(_) | F3(_))) => {
                        let l = l.try_into().unwrap();
                        let r = r.try_into().unwrap();
                        match (l, r) {
                            (F3::CONST(l), F3::CONST(r)) => BOP(BOP::CONST(l != r)),
                            _ => BOP(BOP::NE3(l, r)),
                        }
                    }

                    (LT, F(F::CONST(l)), F(F::CONST(r))) => BOP(BOP::CONST(l < r)),
                    (LT, F(l), F(r)) => BOP(BOP::LT(l, r)),

                    (GT, F(F::CONST(l)), F(F::CONST(r))) => BOP(BOP::CONST(l > r)),
                    (GT, F(l), F(r)) => BOP(BOP::GT(l, r)),

                    (LE, F(F::CONST(l)), F(F::CONST(r))) => BOP(BOP::CONST(l <= r)),
                    (LE, F(l), F(r)) => BOP(BOP::LE(l, r)),

                    (GE, F(F::CONST(l)), F(F::CONST(r))) => BOP(BOP::CONST(l >= r)),
                    (GE, F(l), F(r)) => BOP(BOP::GE(l, r)),

                    (_op, l, r) => {
                        return Err(Error::InvalidType(format!(
                            "invalid operands type for '{}' operator",
                            _op
                        )))
                    }
                };
            }
            return Ok(out);
        }

        match lowest_op {
            Or => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Or, &mut xss);
                let mut out = BOP(BOP::CONST(false));
                let mut out_set = false;
                for xs in xss.iter() {
                    let op = xs.compile(ast, ex)?;
                    out = if out_set {
                        let l = out.into_arg(ex).try_into().map_err(|_| {
                            Error::InvalidType("Invalid operands type for '||' operator".into())
                        })?;
                        let r = op.into_arg(ex).try_into().map_err(|_| {
                            Error::InvalidType("Invalid operands type for '||' operator".into())
                        })?;
                        match (l, r) {
                            (B::CONST(l), B::CONST(r)) => BOP(BOP::CONST(l || r)),
                            _ => BOP(BOP::OR(l, r)),
                        }
                    } else {
                        out_set = true;
                        op
                    };
                }
                Ok(out)
            }
            And => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(And, &mut xss);
                let mut out = BOP(BOP::CONST(true));
                let mut out_set = false;
                for xs in xss.iter() {
                    let op = xs.compile(ast, ex)?;
                    out = if out_set {
                        let l = out.into_arg(ex).try_into().map_err(|_| {
                            Error::InvalidType("invalid operands type for '&&' operator".into())
                        })?;
                        let r = op.into_arg(ex).try_into().map_err(|_| {
                            Error::InvalidType("invalid operands type for '&&' operator".into())
                        })?;
                        match (l, r) {
                            (B::CONST(l), B::CONST(r)) => BOP(BOP::CONST(l && r)),
                            _ => BOP(BOP::AND(l, r)),
                        }
                    } else {
                        out_set = true;
                        op
                    };
                }
                Ok(out)
            }

            Add => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Add, &mut xss);
                println!("ADD SPLITTED: {:?}", xss);
                let mut ops = Vec::<OP>::with_capacity(xss.len());
                for xs in xss {
                    let op = xs.compile(ast, ex)?;
                    ex.push_add_leafs(&mut ops, op);
                }
                sort(&mut ops);
                // println!("sorted: {:?}", ops);
                ex.compile_add(ops)
            }

            Sub => {
                // Note: We don't need to push_add_leaves from here because Sub has a higher precedence than ADD.
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Sub, &mut xss);
                let mut ops = Vec::<OP>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let op = xs.compile(ast, ex)?;
                    ops.push(if i == 0 { op } else { ex.neg_wrap(op) });
                }
                sort(&mut ops);

                ex.compile_add(ops)
            }
            Mul => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Mul, &mut xss);
                println!("MUL SPLITTED: {:?}", xss);
                let mut ops = Vec::<OP>::with_capacity(xss.len());
                for xs in xss {
                    let op = xs.compile(ast, ex)?;
                    ex.push_mul_leafs(&mut ops, op);
                }
                sort(&mut ops);
                ex.compile_mul(ops)
            }
            Div => {
                // Note: We don't need to push_mul_leaves from here because Div has a higher precedence than MUL.
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Div, &mut xss);
                let mut ops = Vec::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let op = xs.compile(ast, ex)?;
                    ops.push(if i == 0 { op } else { ex.inv_wrap(op) });
                }
                sort(&mut ops);
                ex.compile_mul(ops)
            }

            Rem => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Rem, &mut xss);
                let mut out = FOP(FOP::CONST(0.0));
                let mut out_set = false;
                for xs in xss.iter() {
                    let op = xs.compile(ast, ex)?;
                    out = if out_set {
                        let l = out.into_arg(ex);
                        let r = op.into_arg(ex);
                        compile_op!(REM, rem, (l, r))
                    } else {
                        out_set = true;
                        op
                    };
                }
                Ok(out)
            }
            Pow => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Pow, &mut xss);
                let mut out = FOP(FOP::CONST(0.0));
                let mut out_set = false;
                // Right-to-Left Associativity
                for xs in xss.into_iter().rev() {
                    let op = xs.compile(ast, ex)?;
                    out = if out_set {
                        let l = op.into_arg(ex);
                        let r = out.into_arg(ex);
                        compile_op!(POW, pow, (l, r))
                    } else {
                        out_set = true;
                        op
                    };
                }
                Ok(out)
            }

            _ => Err(Error::Unreachable),
        }
    }
}

impl<M: Module> Compiler<M> for Expr {
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP, Error> {
        let top = ExprSlice::from_expr(&self);
        top.compile(ast, ex)
    }
}

impl<M: Module> Compiler<M> for UnaryOp {
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP, Error> {
        match self {
            Neg(fcv) => {
                let op = fcv.compile(ast, ex)?;
                Ok(ex.neg_wrap(op))
            }
            Not(fcv) => {
                let op = fcv.compile(ast, ex)?;
                ex.not_wrap(op)
            }
        }
    }
}

impl<M: Module> Compiler<M> for ECV {
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP, Error> {
        match self {
            Const(c) => Ok(FOP(FOP::CONST(*c))),
            Var(name) => {
                if let Some(arg) = ex.locals.get(name) {
                    Ok(arg.clone().into())
                } else if let Some(op) = ex.module.dispatch_ident(name) {
                    Ok(op)
                } else {
                    builtins::dispatch_const(name).ok_or(Error::Undefined(name.to_owned()))
                }
            }
            E(i) => ast.get_expr(*i).compile(ast, ex),
        }
    }
}

impl<M: Module> Compiler<M> for Value {
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP, Error> {
        match self {
            ECV(ecv) => ecv.compile(ast, ex),
            UnaryOp(u) => u.compile(ast, ex),
            Func(name, string, eargs) => {
                if let ("if", None, [cond, then, els]) = (name.as_str(), string, eargs.as_slice()) {
                    let cond = cond.compile(ast, ex)?;
                    let cond: B = cond.into_arg(ex).try_into()?;
                    let then = then.compile(ast, ex)?;
                    let els = els.compile(ast, ex)?;

                    match (cond, then, els) {
                        (B::CONST(false), _, els) => Ok(els),
                        (B::CONST(_), then, _) => Ok(then),
                        (cond, then, els) => match then.optype().max(els.optype()) {
                            Type::B => Ok(BOP(BOP::IF(
                                cond,
                                then.into_arg(ex).try_into().unwrap(),
                                els.into_arg(ex).try_into().unwrap(),
                            ))),
                            Type::F => Ok(FOP(FOP::IF(
                                cond,
                                then.into_arg(ex).try_into().unwrap(),
                                els.into_arg(ex).try_into().unwrap(),
                            ))),
                            Type::F2 => Ok(FOP2(FOP2::IF(
                                cond,
                                then.into_arg(ex).try_into().unwrap(),
                                els.into_arg(ex).try_into().unwrap(),
                            ))),
                            Type::F3 => Ok(FOP3(FOP3::IF(
                                cond,
                                then.into_arg(ex).try_into()?,
                                els.into_arg(ex).try_into()?,
                            ))),
                        },
                    }
                } else {
                    let mut args = Vec::with_capacity(eargs.len());
                    for earg in eargs {
                        let op = earg.compile(ast, ex)?;
                        let arg = op.into_arg(ex);
                        args.push(arg);
                    }
                    let string = string.as_deref();
                    if let Some(op) = ex.module.dispatch_func(&name, string, &args) {
                        Ok(op)
                    } else {
                        builtins::dispatch_func(&name, string, &args).ok_or(Error::Undefined(
                            format!("cannot find function '{}'", signature(name, &args)),
                        ))
                    }
                }
            }
            List(vals) => match &vals.as_slice() {
                &[ECV::Const(cx), ECV::Const(cy)] => Ok(FOP2(FOP2::CONST([*cx, *cy]))),
                &[ECV::Const(cx), ECV::Const(cy), ECV::Const(cz)] => {
                    Ok(FOP3(FOP3::CONST([*cx, *cy, *cz])))
                }
                &[x, y] => {
                    let x = x.compile(ast, ex)?.into_arg(ex).try_into()?;
                    let y = y.compile(ast, ex)?.into_arg(ex).try_into()?;
                    Ok(FOP2(FOP2::NEW([x, y])))
                }
                &[x, y, z] => {
                    let x = x.compile(ast, ex)?.into_arg(ex).try_into()?;
                    let y = y.compile(ast, ex)?.into_arg(ex).try_into()?;
                    let z = z.compile(ast, ex)?.into_arg(ex).try_into()?;
                    Ok(FOP3(FOP3::NEW([x, y, z])))
                }
                _ => Err(Error::InvalidSyntax(
                    "The vector must be 2 to 3 elements long".into(),
                )),
            },

            _ => Err(Error::Unreachable),
        }
    }
}
