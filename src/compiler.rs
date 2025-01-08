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

use crate::context::*;
use crate::error::Error;
// pub use crate::parser::FOP;
// use crate::context::{self, Module};
use crate::debug_indexed_list;
use crate::float::*;
use crate::ops::{self, *};
use crate::parser::*;
use crate::tokens::*;
use crate::{map2, map3};
use indexmap::{IndexMap, IndexSet};

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

// macro_rules! map2 {
//     ($f:expr, $($a:expr),+) => {
//         [
//             $f($($a[0]),+),
//             $f($($a[1]),+),
//         ]
//     };
// }

// macro_rules! map3 {
//     ($f:expr, $($a:expr),+) => {
//         [
//             $f($($a[0]),+),
//             $f($($a[1]),+),
//             $f($($a[2]),+),
//         ]
//     };
// }

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
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP<M::FFN, M::UFN>, Error>;
}

/// `Expression` is where `compile()` results are stored.
pub struct Expression<'m, M: Module = ()> {
    module: &'m M,
    pub(crate) ops: Vec<OP<M::FFN, M::UFN>>,
}

impl<'m, M: Module> Expression<'m, M> {
    pub fn new(module: &'m M) -> Self {
        Self {
            module,
            ops: Vec::new(),
        }
    }

    // fn get_var(&self, name: &str) -> Option<*const f32> {
    //     self.module.get_var(name)
    // }

    #[inline]
    pub fn compile(&mut self, ast: &Ast) -> Result<(), Error> {
        self.ops.clear();

        let expr = ast.exprs.last().unwrap();
        let op = expr.compile(ast, self)?;

        self.ops.push(op);
        if self.ops.len() <= 2 {
            Ok(())
        } else {
            // *********************************************
            // **********   optimization pass   ************
            // *********************************************
            // let index_set = IndexSet::with_capacity(self.ops.len());
            // let mut cache: IndexSet<OP<M::FFN, M::UFN>> = index_set;
            // let mut index_remap: Vec<usize> = Vec::with_capacity(self.ops.len());

            // let mut iter_instr = self.ops.iter();
            // cache.insert(iter_instr.next().unwrap().clone());
            // index_remap.push(0);

            // for op in iter_instr {
            //     let mut op = op.clone();
            //     op.update_i(|i| *index_remap.get(i).unwrap());

            //     if let Some(i) = cache.get_index_of(&op) {
            //         index_remap.push(i);
            //     } else {
            //         cache.insert(op);
            //         index_remap.push(cache.len() - 1);
            //     }
            // }
            // let new_len = cache.len();
            // for (old, new) in self.ops.iter_mut().zip(cache.into_iter()) {
            //     *old = new;
            // }
            // self.ops.truncate(new_len);
            Ok(())
        }
    }

    #[inline]
    pub fn last(&self) -> Option<&OP<M::FFN, M::UFN>> {
        self.ops.last()
    }

    /// Returns a reference to the [`OP`](../compiler/enum.OP.html)
    /// located at `instr_i` within the `Expression.ops'.
    ///
    /// If `instr_i` is out-of-bounds, a reference to a default `OP` is returned.
    ///
    #[inline]
    pub fn get(&self, instr_i: usize) -> &OP<M::FFN, M::UFN> {
        // unsafe{self.ops.get_unchecked(instr_i)}
        self.ops.get(instr_i).unwrap()
    }

    /// Appends an `OP` to `Expression.ops`.
    #[inline]
    pub fn push(&mut self, op: OP<M::FFN, M::UFN>) -> usize {
        let i = self.ops.len();
        self.ops.push(op);
        i
    }

    /// Removes an `OP` from `Expression.ops` as efficiently as possible.
    #[inline]
    pub fn pop(&mut self) -> OP<M::FFN, M::UFN> {
        self.ops.pop().unwrap()
    }

    /// Clears all data from `Expression.ops`.
    #[inline]
    pub fn clear(&mut self) {
        self.ops.clear();
    }

    // #[inline]
    // pub fn instr_to_arg(&mut self, op: OP<M::FFN, M::UFN>) -> ARG {
    //     match op {
    //         FOP(F(a)) => ARG::F(a),
    //         UOP(U(a)) => ARG::U(a),
    //         FOP(_) => ARG::F(FOP(self.push(op))),
    //         UOP(_) => ARG::U(UOP(self.push(op))),
    //     }
    // }
}

// impl OP<M::FFN, M::UFN> {
//     #[inline]
//     fn to_uicv<M>(self, expr: &mut Expression<M>) -> F {
//         match self {
//             FOP(op) => F::F(op.to_icv(expr)),
//             UOP(op) => U::U(op.to_icv(expr)),
//         }
//     }
// }

impl ARG {
    #[inline]
    fn to_ficv<M: Module>(self, expr: &mut Expression<M>) -> F {
        match self {
            F(f) => f,

            U(U::CONST(c)) => F::CONST(c[0]),
            U(U::I(i)) => F::I(i),
            U(U::VAR(u)) => F::I(expr.push(UOP(UOP::VAR(u)))),

            // B(B::CONST(c)) => F::CONST(c.into()),
            // B(B::I(i)) => F::I(i),
            // B(B::VAR(u)) => F::I(expr.push(BOP(BOP::VAR(u)))),
            _ => unreachable!(),
        }
    }

    #[inline]
    fn to_uicv<M: Module>(self, expr: &mut Expression<M>) -> U {
        match self {
            U(u) => u,

            F(F::CONST(c)) => U::CONST([c; 2]),
            F(F::I(i)) => U::I(i),
            F(F::VAR(u)) => U::I(expr.push(FOP(FOP::VAR(u)))),

            // B(B::CONST(c)) => U::CONST([c.into(); 2]),
            // B(B::I(i)) => U::I(i),
            // B(B::VAR(u)) => U::I(expr.push(BOP(BOP::VAR(u)))),
            _ => unreachable!(),
        }
    }
}

impl<FFN, UFN> ops::OP<FFN, UFN> {
    #[inline]
    fn to_icv<M: Module<FFN = FFN, UFN = UFN>>(self, expr: &mut Expression<M>) -> ARG {
        match self {
            FOP(FOP::CONST(c)) => F(F::CONST(c)),
            FOP(FOP::VAR(v)) => F(F::VAR(v)),
            FOP(_) => F(F::I(expr.push(self))),

            BOP(BOP::CONST(c)) => F(F::CONST(c.into())),
            BOP(_) => F(F::I(expr.push(self))),

            UOP(UOP::CONST(c)) => U(U::CONST(c)),
            UOP(UOP::VAR(v)) => U(U::VAR(v)),
            UOP(_) => U(U::I(expr.push(self))),
        }
    }

    #[inline]
    fn to_bicv<M: Module<FFN = FFN, UFN = UFN>>(self, expr: &mut Expression<M>) -> B {
        match self {
            FOP(fop) => fop.to_bicv(expr),
            UOP(uop) => uop.to_bicv(expr),
            BOP(bop) => bop.to_bicv(expr),
        }
    }

    #[inline]
    fn to_ficv<M: Module<FFN = FFN, UFN = UFN>>(self, expr: &mut Expression<M>) -> F {
        match self {
            FOP(fop) => fop.to_ficv(expr),
            UOP(uop) => uop.to_ficv(expr),
            BOP(bop) => bop.to_ficv(expr),
        }
    }

    #[inline]
    fn to_uicv<M: Module<FFN = FFN, UFN = UFN>>(self, expr: &mut Expression<M>) -> U {
        match self {
            UOP(uop) => uop.to_uicv(expr),
            FOP(fop) => fop.to_uicv(expr),
            BOP(bop) => bop.to_uicv(expr),
        }
    }
}

impl BOP {
    #[inline]
    fn to_bicv<M: Module>(self, expr: &mut Expression<M>) -> B {
        match self {
            BOP::CONST(c) => B::CONST(c),
            _ => B::I(expr.push(BOP(self))),
        }
    }

    #[inline]
    fn to_ficv<M: Module>(self, expr: &mut Expression<M>) -> F {
        match self {
            BOP::CONST(c) => F::CONST(c.into()),
            _ => F::I(expr.push(BOP(self))),
        }
    }

    #[inline]
    fn to_uicv<M: Module>(self, expr: &mut Expression<M>) -> U {
        match self {
            BOP::CONST(c) => U::CONST([c.into(); 2]),
            _ => U::I(expr.push(BOP(self))),
        }
    }
}

impl<FFN> FOP<FFN> {
    #[inline]
    fn to_bicv<M: Module<FFN = FFN>>(self, expr: &mut Expression<M>) -> B {
        match self {
            FOP::CONST(c) => B::CONST(c != 0.0),
            FOP::VAR(v) => B::VAR(v),
            _ => B::I(expr.push(FOP(self))),
        }
    }

    #[inline]
    fn to_ficv<M: Module<FFN = FFN>>(self, expr: &mut Expression<M>) -> F {
        match self {
            FOP::CONST(c) => F::CONST(c),
            FOP::VAR(v) => F::VAR(v),
            _ => F::I(expr.push(FOP(self))),
        }
    }

    #[inline]
    fn to_uicv<M: Module<FFN = FFN>>(self, expr: &mut Expression<M>) -> U {
        match self {
            FOP::CONST(c) => U::CONST([c; 2]),
            _ => U::I(expr.push(FOP(self))),
        }
    }
}

impl<UFN> UOP<UFN> {
    #[inline]
    fn to_bicv<M: Module<UFN = UFN>>(self, expr: &mut Expression<M>) -> B {
        match self {
            UOP::CONST(c) => B::CONST(c[0] != 0.0),
            UOP::VAR(v) => B::VAR(v),
            _ => B::I(expr.push(UOP(self))),
        }
    }

    #[inline]
    fn to_ficv<M: Module<UFN = UFN>>(self, expr: &mut Expression<M>) -> F {
        match self {
            UOP::CONST(c) => F::CONST(c[0]),
            _ => F::I(expr.push(UOP(self))),
        }
    }

    #[inline]
    fn to_uicv<M: Module<UFN = UFN>>(self, expr: &mut Expression<M>) -> U {
        match self {
            UOP::CONST(c) => U::CONST(c),
            UOP::VAR(v) => U::VAR(v),
            _ => U::I(expr.push(UOP(self))),
        }
    }
}

impl<M: Module> Debug for Expression<'_, M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        debug_indexed_list(f, &self.ops)?;
        Ok(())
    }
}

impl<M: Module> Expression<'_, M> {
    #[inline]
    fn neg_wrap(&mut self, op: OP<M::FFN, M::UFN>) -> OP<M::FFN, M::UFN> {
        match op {
            FOP(FOP::NEG(_)) | UOP(UOP::NEG(_)) => self.pop(),
            FOP(FOP::CONST(c)) => FOP(FOP::CONST(-c)),
            FOP(op) => FOP(FOP::NEG(op.to_ficv(self))),

            BOP(BOP::CONST(c)) => FOP(FOP::CONST(-f64::from(c))),
            BOP(op) => FOP(FOP::NEG(op.to_ficv(self))),

            UOP(UOP::CONST([x, y])) => UOP(UOP::CONST([-x, -y])),
            UOP(op) => UOP(UOP::NEG(op.to_uicv(self))),
            // _ => unreachable!(),
        }
    }

    #[inline]
    fn not_wrap(&mut self, op: OP<M::FFN, M::UFN>) -> OP<M::FFN, M::UFN> {
        match op {
            BOP(BOP::NOT(_)) => self.pop(),
            BOP(BOP::CONST(c)) => BOP(BOP::CONST(!c)),
            BOP(op) => BOP(BOP::NOT(op.to_bicv(self))),

            FOP(FOP::CONST(c)) => BOP(BOP::CONST((c == 0.0).into())),
            FOP(op) => BOP(BOP::NOT(op.to_bicv(self))),

            UOP(UOP::CONST(c)) => BOP(BOP::CONST((c[0] == 0.0).into())),
            UOP(op) => BOP(BOP::NOT(op.to_bicv(self))),
            // _ => unreachable!(),
        }
    }

    #[inline]
    fn inv_wrap(&mut self, op: OP<M::FFN, M::UFN>) -> OP<M::FFN, M::UFN> {
        match op {
            FOP(FOP::INV(_)) | UOP(UOP::INV(_)) => self.pop(),
            FOP(FOP::CONST(c)) => FOP(FOP::CONST(c.recip())),
            FOP(op) => FOP(FOP::INV(op.to_ficv(self))),

            BOP(BOP::CONST(c)) => FOP(FOP::CONST(f64::from(c).recip())),
            BOP(op) => FOP(FOP::INV(op.to_ficv(self))),

            UOP(UOP::CONST([x, y])) => UOP(UOP::CONST([x.recip(), y.recip()])),
            UOP(op) => UOP(UOP::INV(op.to_uicv(self))),

            _ => unreachable!(),
        }
    }

    #[inline]
    fn compile_mul(&mut self, sorted_ops: Vec<OP<M::FFN, M::UFN>>) -> OP<M::FFN, M::UFN> {
        let mut const_out = FOP(FOP::CONST(1.0));
        let mut out = FOP(FOP::CONST(1.0));

        for op in sorted_ops {
            match (out, op) {
                (FOP(FOP::CONST(c0)), BOP(BOP::CONST(c1))) => {
                    out = FOP(FOP::CONST(c0 * f64::from(c1)));
                }
                (FOP(FOP::CONST(c0)), FOP(FOP::CONST(c1))) => {
                    out = FOP(FOP::CONST(c0 * c1));
                }
                (FOP(FOP::CONST(c0)), UOP(UOP::CONST([cx1, cy1]))) => {
                    out = UOP(UOP::CONST([c0 * cx1, c0 * cy1]));
                }
                (UOP(UOP::CONST([cx0, cy0])), UOP(UOP::CONST([cx1, cy1]))) => {
                    out = UOP(UOP::CONST([cx0 * cx1, cy0 * cy1]));
                }
                (op1 @ (FOP(FOP::CONST(_)) | UOP(UOP::CONST(_))), op2) => {
                    const_out = op1;
                    out = op2;
                }
                (fop0 @ (FOP(_) | BOP(_)), fop1 @ (FOP(_) | BOP(_))) => {
                    out = FOP(FOP::MUL(fop0.to_ficv(self), fop1.to_ficv(self)));
                }
                (fop0 @ (FOP(_) | BOP(_)), UOP(uop1)) => {
                    out = UOP(UOP::MUL(fop0.to_uicv(self), uop1.to_uicv(self)));
                }
                (UOP(uop0), UOP(uop1)) => {
                    out = UOP(UOP::MUL(uop0.to_uicv(self), uop1.to_uicv(self)));
                }
                _ => unreachable!(), //because of sorting
            }
        }
        match (const_out, out) {
            (FOP(FOP::CONST(1.0)), op1 @ FOP(_)) => op1,
            (FOP(fop0), fop1 @ (FOP(_) | BOP(_))) => {
                FOP(FOP::MUL(fop0.to_ficv(self), fop1.to_ficv(self)))
            }
            (UOP(UOP::CONST([1.0, 1.0])), op1 @ UOP(_)) => op1,
            (op0 @ (FOP(_) | UOP(_)), op1 @ (FOP(_) | UOP(_) | BOP(_))) => {
                let l = op0.to_uicv(self);
                let r = op1.to_uicv(self);
                UOP(UOP::MUL(l, r))
            }
            _ => unreachable!(),
        }
    }

    #[inline]
    fn compile_add(&mut self, sorted_ops: Vec<OP<M::FFN, M::UFN>>) -> OP<M::FFN, M::UFN> {
        let mut const_out = FOP(FOP::CONST(0.0));
        let mut out = FOP(FOP::CONST(0.0));

        for op in sorted_ops {
            match (out, op) {
                (FOP(FOP::CONST(c0)), BOP(BOP::CONST(c1))) => {
                    out = FOP(FOP::CONST(c0 + f64::from(c1)));
                }
                (FOP(FOP::CONST(c0)), FOP(FOP::CONST(c1))) => {
                    out = FOP(FOP::CONST(c0 + c1));
                }
                (FOP(FOP::CONST(c0)), UOP(UOP::CONST([cx1, cy1]))) => {
                    out = UOP(UOP::CONST([c0 + cx1, c0 + cy1]));
                }
                (UOP(UOP::CONST([cx0, cy0])), UOP(UOP::CONST([cx1, cy1]))) => {
                    out = UOP(UOP::CONST([cx0 + cx1, cy0 + cy1]));
                }
                (op1 @ (FOP(FOP::CONST(_)) | UOP(UOP::CONST(_))), op2) => {
                    const_out = op1;
                    out = op2;
                }

                (fop0 @ (FOP(_) | BOP(_)), fop1 @ (FOP(_) | BOP(_))) => {
                    out = FOP(FOP::ADD(fop0.to_ficv(self), fop1.to_ficv(self)));
                }
                (fop0 @ (FOP(_) | BOP(_)), UOP(uop1)) => {
                    out = UOP(UOP::ADD(fop0.to_uicv(self), uop1.to_uicv(self)));
                }
                (UOP(uop0), UOP(uop1)) => {
                    out = UOP(UOP::ADD(uop0.to_uicv(self), uop1.to_uicv(self)));
                }
                _ => unreachable!(), //because of sorting
            }
        }

        match (const_out, out) {
            (FOP(FOP::CONST(0.0)), op1 @ FOP(_)) => op1,
            (FOP(fop0), fop1 @ (FOP(_) | BOP(_))) => {
                FOP(FOP::ADD(fop0.to_ficv(self), fop1.to_ficv(self)))
            }
            (UOP(UOP::CONST([0.0, 0.0])), op1 @ UOP(_)) => op1,
            (op0 @ (FOP(_) | UOP(_)), op1 @ (FOP(_) | UOP(_) | BOP(_))) => {
                let l = op0.to_uicv(self);
                let r = op1.to_uicv(self);
                UOP(UOP::ADD(l, r))
            }
            _ => unreachable!(),
        }
    }

    fn push_fadd_leaf(&mut self, ops: &mut Vec<OP<M::FFN, M::UFN>>, icv: F) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match icv {
            F::I(_) => {
                let op = self.pop();
                match op {
                    FOP(FOP::ADD(l, r)) => {
                        self.push_fadd_leaf(ops, r);
                        self.push_fadd_leaf(ops, l);
                    }
                    UOP(UOP::ADD(l, r)) => {
                        self.push_uadd_leaf(ops, r);
                        self.push_uadd_leaf(ops, l);
                    }
                    _ => {
                        ops.push(op);
                    }
                }
            }
            F::CONST(c) => ops.push(FOP(FOP::CONST(c))),
            F::VAR(v) => ops.push(FOP(FOP::VAR(v))),
        };
    }
    fn push_uadd_leaf(&mut self, ops: &mut Vec<OP<M::FFN, M::UFN>>, icv: U) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match icv {
            U::I(_) => {
                let op = self.pop();
                match op {
                    UOP(UOP::ADD(l, r)) => {
                        self.push_uadd_leaf(ops, r);
                        self.push_uadd_leaf(ops, l);
                    }
                    FOP(FOP::ADD(l, r)) => {
                        self.push_fadd_leaf(ops, r);
                        self.push_fadd_leaf(ops, l);
                    }
                    _ => {
                        ops.push(op);
                    }
                }
            }

            U::CONST(c) => ops.push(UOP(UOP::CONST(c))),
            U::VAR(v) => ops.push(UOP(UOP::VAR(v))),
        };
    }

    fn push_fmul_leaf(&mut self, ops: &mut Vec<OP<M::FFN, M::UFN>>, ficv: F) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match ficv {
            F::I(_) => {
                let op = self.pop();
                match op {
                    FOP(FOP::MUL(l, r)) => {
                        self.push_fmul_leaf(ops, r);
                        self.push_fmul_leaf(ops, l);
                    }
                    UOP(UOP::MUL(l, r)) => {
                        self.push_umul_leaf(ops, r);
                        self.push_umul_leaf(ops, l);
                    }
                    _ => {
                        ops.push(op);
                    }
                }
            }
            F::CONST(c) => ops.push(FOP(FOP::CONST(c))),
            F::VAR(v) => ops.push(FOP(FOP::VAR(v))),
        };
    }

    fn push_umul_leaf(&mut self, ops: &mut Vec<OP<M::FFN, M::UFN>>, uicv: U) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match uicv {
            U::I(_) => {
                let op = self.pop();
                match op {
                    UOP(UOP::MUL(l, r)) => {
                        self.push_umul_leaf(ops, r);
                        self.push_umul_leaf(ops, l);
                    }
                    FOP(FOP::MUL(l, r)) => {
                        self.push_fmul_leaf(ops, r);
                        self.push_fmul_leaf(ops, l);
                    }
                    _ => {
                        ops.push(op);
                    }
                }
            }

            U::CONST(c) => ops.push(UOP(UOP::CONST(c))),
            U::VAR(v) => ops.push(UOP(UOP::VAR(v))),
        };
    }
}

#[derive(Debug)]
struct ExprSlice<'s>(&'s Value, Vec<&'s ExprPair>);

impl<'s> ExprSlice<'s> {
    fn new(first: &Value) -> ExprSlice<'_> {
        ExprSlice(first, Vec::with_capacity(8))
    }

    #[inline]
    fn from_expr(expr: &Expr) -> ExprSlice<'_> {
        let mut sl = ExprSlice::new(&expr.0);
        for exprpairref in expr.1.iter() {
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
// y = 1.0;
// x = cos(y)
// vec3 v = sin(x)
impl<M: Module> Compiler<M> for ExprSlice<'_> {
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP<M::FFN, M::UFN>, Error> {
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

                out = match _op {
                    EQ => match (out, op) {
                        (BOP(BOP::CONST(l)), BOP(BOP::CONST(r))) => BOP(BOP::CONST(l == r)),
                        (l @ (FOP(_) | BOP(_)), r @ (FOP(_) | BOP(_))) => {
                            let l = l.to_ficv(ex);
                            let r = r.to_ficv(ex);
                            match (l, r) {
                                (F::CONST(l), F::CONST(r)) => BOP(BOP::CONST(l == r)),
                                _ => BOP(BOP::EQ(l, r)),
                            }
                        }
                        (l @ (FOP(_) | UOP(_) | BOP(_)), r @ (FOP(_) | UOP(_) | BOP(_))) => {
                            let l = l.to_uicv(ex);
                            let r = r.to_uicv(ex);
                            match (l, r) {
                                (U::CONST(l), U::CONST(r)) => BOP(BOP::CONST(l == r)),
                                _ => BOP(BOP::EQU(l, r)),
                            }
                        }
                    },
                    NE => match (out, op) {
                        (BOP(BOP::CONST(l)), BOP(BOP::CONST(r))) => BOP(BOP::CONST(l != r)),
                        (l @ (FOP(_) | BOP(_)), r @ (FOP(_) | BOP(_))) => {
                            let l = l.to_ficv(ex);
                            let r = r.to_ficv(ex);
                            match (l, r) {
                                (F::CONST(l), F::CONST(r)) => BOP(BOP::CONST(l != r)),
                                _ => BOP(BOP::NE(l, r)),
                            }
                        }
                        (l @ (FOP(_) | UOP(_) | BOP(_)), r @ (FOP(_) | UOP(_) | BOP(_))) => {
                            let l = l.to_uicv(ex);
                            let r = r.to_uicv(ex);
                            match (l, r) {
                                (U::CONST(l), U::CONST(r)) => BOP(BOP::CONST(l != r)),
                                _ => BOP(BOP::NEU(l, r)),
                            }
                        }
                    },
                    LT => match (out, op) {
                        (BOP(BOP::CONST(l)), BOP(BOP::CONST(r))) => BOP(BOP::CONST(l < r)),
                        (l, r) => {
                            let l = l.to_ficv(ex);
                            let r = r.to_ficv(ex);
                            match (l, r) {
                                (F::CONST(l), F::CONST(r)) => BOP(BOP::CONST(l < r)),
                                _ => BOP(BOP::LT(l, r)),
                            }
                        }
                    },
                    GT => match (out, op) {
                        (BOP(BOP::CONST(l)), BOP(BOP::CONST(r))) => BOP(BOP::CONST(l > r)),
                        (l, r) => {
                            let l = l.to_ficv(ex);
                            let r = r.to_ficv(ex);
                            match (l, r) {
                                (F::CONST(l), F::CONST(r)) => BOP(BOP::CONST(l > r)),
                                _ => BOP(BOP::GT(l, r)),
                            }
                        }
                    },
                    LE => match (out, op) {
                        (BOP(BOP::CONST(l)), BOP(BOP::CONST(r))) => BOP(BOP::CONST(l <= r)),
                        (l, r) => {
                            let l = l.to_ficv(ex);
                            let r = r.to_ficv(ex);
                            match (l, r) {
                                (F::CONST(l), F::CONST(r)) => BOP(BOP::CONST(l <= r)),
                                _ => BOP(BOP::LE(l, r)),
                            }
                        }
                    },
                    GE => match (out, op) {
                        (BOP(BOP::CONST(l)), BOP(BOP::CONST(r))) => BOP(BOP::CONST(l >= r)),
                        (l, r) => {
                            let l = l.to_ficv(ex);
                            let r = r.to_ficv(ex);
                            match (l, r) {
                                (F::CONST(l), F::CONST(r)) => BOP(BOP::CONST(l >= r)),
                                _ => BOP(BOP::GE(l, r)),
                            }
                        }
                    },
                    _ => unreachable!(),
                };
            }
            return Ok(out);
        }

        match lowest_op {
            Or => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(And, &mut xss);
                let mut out = BOP(BOP::CONST(false));
                let mut out_set = false;
                for xs in xss.iter() {
                    let op = xs.compile(ast, ex)?;
                    out = if out_set {
                        let l = out.to_bicv(ex);
                        let r = op.to_bicv(ex);
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
                        let l = out.to_bicv(ex);
                        let r = op.to_bicv(ex);
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
                let mut ops = Vec::<OP<M::FFN, M::UFN>>::with_capacity(xss.len());
                for xs in xss {
                    let op = xs.compile(ast, ex)?;
                    match op {
                        FOP(FOP::ADD(licv, ricv)) => {
                            ex.push_fadd_leaf(&mut ops, ricv);
                            ex.push_fadd_leaf(&mut ops, licv);
                        }
                        UOP(UOP::ADD(licv, ricv)) => {
                            ex.push_uadd_leaf(&mut ops, ricv);
                            ex.push_uadd_leaf(&mut ops, licv);
                        }
                        _ => {
                            ops.push(op);
                        }
                    }
                }
                sort(&mut ops);
                // println!("sorted: {:?}", ops);
                Ok(ex.compile_add(ops))
            }

            Sub => {
                // Note: We don't need to push_add_leaves from here because Sub has a higher precedence than FADD.
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Sub, &mut xss);
                let mut ops = Vec::<OP<M::FFN, M::UFN>>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let op = xs.compile(ast, ex)?;
                    ops.push(if i == 0 { op } else { ex.neg_wrap(op) });
                }
                sort(&mut ops);

                Ok(ex.compile_add(ops))
            }
            Mul => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Mul, &mut xss);
                let mut ops = Vec::<OP<M::FFN, M::UFN>>::with_capacity(xss.len());
                for xs in xss {
                    let op = xs.compile(ast, ex)?;
                    match op {
                        FOP(FOP::MUL(licv, ricv)) => {
                            ex.push_fmul_leaf(&mut ops, ricv);
                            ex.push_fmul_leaf(&mut ops, licv);
                        }
                        UOP(UOP::MUL(licv, ricv)) => {
                            ex.push_umul_leaf(&mut ops, ricv);
                            ex.push_umul_leaf(&mut ops, licv);
                        }
                        _ => {
                            ops.push(op);
                        }
                    }
                }
                sort(&mut ops);
                Ok(ex.compile_mul(ops))
            }
            Div => {
                // Note: We don't need to push_mul_leaves from here because Div has a higher precedence than FMUL.

                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Div, &mut xss);
                let mut ops = Vec::<OP<M::FFN, M::UFN>>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let op = xs.compile(ast, ex)?;
                    ops.push(if i == 0 { op } else { ex.inv_wrap(op) });
                }
                sort(&mut ops);
                Ok(ex.compile_mul(ops))
            }

            Rem => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Rem, &mut xss);
                let mut out = FOP(FOP::CONST(0.0));
                let mut out_set = false;
                for xs in xss.iter() {
                    let op = xs.compile(ast, ex)?;
                    out = if out_set {
                        let l = out.to_icv(ex);
                        let r = op.to_icv(ex);
                        match (l, r) {
                            (F(F::CONST(l)), F(F::CONST(r))) => FOP(FOP::CONST(f64::rem(l, r))),
                            (F(l), F(r)) => FOP(FOP::REM(l, r)),
                            (l @ (F(_) | U(_)), r @ (F(_) | U(_))) => {
                                let l = l.to_uicv(ex);
                                let r = r.to_uicv(ex);
                                match (l, r) {
                                    (U::CONST(l), U::CONST(r)) => {
                                        UOP(UOP::CONST(map2!(f64::rem, l, r)))
                                    }
                                    _ => UOP(UOP::REM(l, r)),
                                }
                            }
                        }
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
                        let l = op.to_icv(ex);
                        let r = out.to_icv(ex);
                        match (l, r) {
                            (F(F::CONST(l)), F(F::CONST(r))) => FOP(FOP::CONST(f64::pow(l, r))),
                            (F(l), F(r)) => FOP(FOP::POW(l, r)),
                            (l @ (F(_) | U(_)), r @ (F(_) | U(_))) => {
                                let l = l.to_uicv(ex);
                                let r = r.to_uicv(ex);
                                match (l, r) {
                                    (U::CONST(l), U::CONST(r)) => {
                                        UOP(UOP::CONST(map2!(f64::pow, l, r)))
                                    }
                                    _ => UOP(UOP::POW(l, r)),
                                }
                            }
                        }
                    } else {
                        out_set = true;
                        op
                    };
                }
                Ok(out)
            }

            _ => unreachable!(),
        }
    }
}

impl<M: Module> Compiler<M> for Expr {
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP<M::FFN, M::UFN>, Error> {
        let top = ExprSlice::from_expr(&self);
        top.compile(ast, ex)
    }
}

impl<M: Module> Compiler<M> for UnaryOp {
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP<M::FFN, M::UFN>, Error> {
        match self {
            Neg(fcv) => {
                let op = fcv.compile(ast, ex)?;
                Ok(ex.neg_wrap(op))
            }

            Not(fcv) => {
                let op = fcv.compile(ast, ex)?;
                Ok(ex.not_wrap(op))
            }
        }
    }
}

impl<M: Module> Compiler<M> for ECV {
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP<M::FFN, M::UFN>, Error> {
        match self {
            Const(c) => Ok(FOP(FOP::CONST(*c))),
            Var(name) => {
                if let Some(op) = ex.module.dispatch_var(name) {
                    match op {
                        F(F::CONST(c)) => Ok(FOP(FOP::CONST(*c))),
                        F(F::VAR(v)) => Ok(FOP(FOP::VAR(*v))),
                        U(U::CONST(c)) => Ok(UOP(UOP::CONST(*c))),
                        U(U::VAR(v)) => Ok(UOP(UOP::VAR(*v))),
                        _ => Err(Error::Undefined(name.to_owned())),
                    }
                } else {
                    match name.as_str() {
                        // builtins constants
                        "PI" => Ok(FOP(FOP::CONST(f64::PI))),
                        "E" => Ok(FOP(FOP::CONST(f64::E))),
                        "EPS" => Ok(FOP(FOP::CONST(f64::EPSILON))),
                        _ => Err(Error::Undefined(name.to_owned())),
                    }
                }
            }
            E(i) => ast.get_expr(*i).compile(ast, ex),
        }
    }
}

impl<M: Module> Compiler<M> for Value {
    fn compile(&self, ast: &Ast, ex: &mut Expression<M>) -> Result<OP<M::FFN, M::UFN>, Error> {
        match self {
            ECV(ecv) => ecv.compile(ast, ex),
            UnaryOp(u) => u.compile(ast, ex),
            Func(name, sarg, eargs) => {
                let mut args = if let Some(s) = sarg {
                    // let mut args = Vec::with_capacity(eargs.len() + 1);
                    // args.push(s.clone().into());
                    // args
                    Vec::with_capacity(eargs.len())
                } else {
                    Vec::with_capacity(eargs.len())
                };

                for earg in eargs {
                    let op = earg.compile(ast, ex)?;
                    let arg = op.to_icv(ex);
                    args.push(arg);
                }
                match ex.module.dispatch_func(&name, &args) {
                    Some(op) => Ok(op),
                    _ => Err(Error::Undefined(name.to_owned())),
                }
                // ("if", None, [cond, then, else_]) => {
                //     let cond = cond.compile(ast, ex)?;
                //     let then = then.compile(ast, ex)?;
                //     let else_ = else_.compile(ast, ex)?;
                //     match (cond, then, else_) {
                //         (FOP(FOP::CONST(0.0)), _, a2) => Ok(a2),
                //         (FOP(FOP::CONST(_)), a1, _) => Ok(a1),
                //         (FOP(cond), FOP(a1), FOP(a2)) => Ok(FOP(FIF(
                //             cond.to_icv(ex),
                //             a1.to_icv(ex),
                //             a2.to_icv(ex),
                //         ))),
                //         (FOP(cond), UOP(a1), UOP(a2)) => Ok(UOP(UIF(
                //             cond.to_icv(ex),
                //             a1.to_icv(ex),
                //             a2.to_icv(ex),
                //         ))),

                //         _ => Err(Error::Undefined("if".into())),
                //     }
                // }
                // _ => {
                //     let mut args = Vec::with_capacity(2);
                //     for earg in eargs {
                //         let op = earg.compile(ast, ex)?;
                //         let arg = op.to_icv(ex);
                //         args.push(arg);
                //     }

                //     if let Some(op) = ex.module.func(name, sarg, &args) {
                //         Ok(op)
                //     } else {
                //         Err(Error::Undefined(name.to_owned()))
                //     }
                //}
            }
            List(vals) => match &vals.as_slice() {
                &[ECV::Const(cx), ECV::Const(cy)] => Ok(UOP(UOP::CONST([*cx, *cy]))),
                &[x, y] => {
                    let x: F = x.compile(ast, ex)?.to_ficv(ex);
                    let y: F = y.compile(ast, ex)?.to_ficv(ex);
                    Ok(UOP(UOP::SET(x, y)))
                }
                _ => Err(Error::InvalidSyntax(
                    "The vector must be 2 to 3 elements long".into(),
                )),
            },

            _ => unreachable!(),
        }
    }
}
