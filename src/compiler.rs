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
// use crate::{map2, map3};
use indexmap::{IndexMap, IndexSet};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

type OP<M> = ops::OP<<M as Module>::FFN, <M as Module>::UFN>;

impl Ast {
    pub fn compile<M: Module>(&self, cexpr: &mut Engine<M>, module: &M) -> Result<(), Error> {
        cexpr.compile(self, module)
    }
}

pub fn compile<M: Module>(ast: &Ast, cexpr: &mut Engine<M>, module: &M) -> Result<(), Error> {
    Engine::compile(cexpr, ast, module)
}

/// You must `use` the `Compiler` trait before you can call `.compile()` on parsed `Expr`s.
pub trait Compiler<M: Module> {
    /// Turns a parsed `Expr` into a compiled `OP`.
    ///
    /// Cannot fail, unless you run out of memory.
    fn compile(&self, ast: &Ast, cexpr: &mut Engine<M>, module: &M) -> Result<OP<M>, Error>;
}

/// `Engine` is where `compile()` results are stored.
pub struct Engine<M: Module> {
    pub(crate) ops: Vec<OP<M>>,
}

impl<M: Module> Engine<M> {
    pub fn new() -> Self {
        Self { ops: Vec::new() }
    }

    // fn get_var(&self, name: &str) -> Option<*const f32> {
    //     self.module.get_var(name)
    // }

    #[inline]
    pub fn compile(&mut self, ast: &Ast, module: &M) -> Result<(), Error> {
        self.ops.clear();

        let expr = ast.exprs.last().unwrap();
        let instr = expr.compile(ast, self, module)?;

        self.ops.push(instr);
        if self.ops.len() <= 2 {
            Ok(())
        } else {
            // *********************************************
            // **********   optimization pass   ************
            // *********************************************
            // let index_set = IndexSet::with_capacity(self.ops.len());
            // let mut cache: IndexSet<OP<M>> = index_set;
            // let mut index_remap: Vec<usize> = Vec::with_capacity(self.ops.len());

            // let mut iter_instr = self.ops.iter();
            // cache.insert(iter_instr.next().unwrap().clone());
            // index_remap.push(0);

            // for instr in iter_instr {
            //     let mut instr = instr.clone();
            //     instr.update_i(|i| *index_remap.get(i).unwrap());

            //     if let Some(i) = cache.get_index_of(&instr) {
            //         index_remap.push(i);
            //     } else {
            //         cache.insert(instr);
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
    pub fn last(&self) -> Option<&OP<M>> {
        self.ops.last()
    }

    /// Returns a reference to the [`OP`](../compiler/enum.OP.html)
    /// located at `instr_i` within the `Engine.ops'.
    ///
    /// If `instr_i` is out-of-bounds, a reference to a default `OP` is returned.
    ///
    #[inline]
    pub fn get(&self, instr_i: usize) -> &OP<M> {
        // unsafe{self.ops.get_unchecked(instr_i)}
        self.ops.get(instr_i).unwrap()
    }

    /// Appends an `OP` to `Engine.ops`.
    #[inline]
    pub fn push(&mut self, instr: OP<M>) -> usize {
        let i = self.ops.len();
        self.ops.push(instr);
        i
    }

    /// Removes an `OP` from `Engine.ops` as efficiently as possible.
    #[inline]
    pub fn pop(&mut self) -> OP<M> {
        self.ops.pop().unwrap()
    }

    /// Clears all data from `Engine.ops`.
    #[inline]
    pub fn clear(&mut self) {
        self.ops.clear();
    }

    // #[inline]
    // pub fn instr_to_arg(&mut self, op: OP<M>) -> ICV {
    //     match op {
    //         FOP(F(a)) => ICV::F(a),
    //         UOP(U(a)) => ICV::U(a),
    //         FOP(_) => ICV::F(FOP(self.push(op))),
    //         UOP(_) => ICV::U(UOP(self.push(op))),
    //     }
    // }
}

// impl OP<M> {
//     #[inline]
//     fn to_uicv<M>(self, expr: &mut Engine<M>) -> F {
//         match self {
//             FOP(op) => F::F(op.to_icv(expr)),
//             UOP(op) => U::U(op.to_icv(expr)),
//         }
//     }
// }

impl<FFN, UFN> ops::OP<FFN, UFN> {
    #[inline]
    fn to_icv<M: Module<FFN = FFN, UFN = UFN>>(self, expr: &mut Engine<M>) -> ICV {
        match self {
            FOP(FOP::CONST(c)) => F(F::CONST(c)),
            FOP(FOP::VAR(v)) => F(F::VAR(v)),
            FOP(_) => F(F::I(expr.push(self))),

            UOP(UOP::CONST(c)) => U(U::CONST(c)),
            UOP(UOP::VAR(v)) => U(U::VAR(v)),
            UOP(_) => U(U::I(expr.push(self))),
        }
    }

    // #[inline]
    // fn to_ficv<M: Module<FFN = FFN, UFN = UFN>>(self, expr: &mut Engine<M>) -> F {
    //     match self {
    //         FOP(FOP::CONST(c)) => F::CONST(c),
    //         FOP(FOP::VAR(v)) => F::VAR(v),
    //         FOP(_) => F::I(expr.push(self)),

    //         UOP(UOP::CONST(c)) => F::CONST(c[0]),
    //         UOP(UOP::VAR(v)) => F::VAR(v),
    //         UOP(_) => F::I(expr.push(self)),
    //     }
    // }

    // #[inline]
    // fn to_uicv<M: Module<FFN = FFN, UFN = UFN>>(self, expr: &mut Engine<M>) -> U {
    //     match self {
    //         UOP(UOP::CONST(c)) => U::CONST(c),
    //         UOP(UOP::VAR(v)) => U::VAR(v),
    //         UOP(_) => U::I(expr.push(self)),

    //         FOP(FOP::CONST(c)) => U::CONST([c; 2]),
    //         // FOP(FOP::VAR(c)) => U::FROM(F::VAR(c)),
    //         FOP(_) => U::I(expr.push(self)),
    //     }
    // }
}

impl<FFN> FOP<FFN> {
    #[inline]
    fn to_ficv<M: Module<FFN = FFN>>(self, expr: &mut Engine<M>) -> F {
        match self {
            FOP::CONST(c) => F::CONST(c),
            FOP::VAR(v) => F::VAR(v),
            _ => F::I(expr.push(FOP(self))),
        }
    }

    // #[inline]
    // fn to_uicv<M: Module<FFN = FFN>>(self, expr: &mut Engine<M>) -> U {
    //     match self {
    //         FOP::CONST(c) => U::CONST([c; 2]),
    //         _ => U::I(expr.push(FOP(self))),
    //     }
    // }
}

impl<UFN> UOP<UFN> {
    // #[inline]
    // fn to_ficv<M: Module<UFN = UFN>>(self, expr: &mut Engine<M>) -> F {
    //     match self {
    //         UOP::CONST(c) => F::CONST(c[0]),
    //         UOP::VAR(v) => F::VAR(v),
    //         _ => F::I(expr.push(UOP(self))),
    //     }
    // }

    #[inline]
    fn to_uicv<M: Module<UFN = UFN>>(self, expr: &mut Engine<M>) -> U {
        match self {
            UOP::CONST(c) => U::CONST(c),
            UOP::VAR(v) => U::VAR(v),
            _ => U::I(expr.push(UOP(self))),
        }
    }
}

impl<M: Module> Debug for Engine<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        debug_indexed_list(f, &self.ops)?;
        Ok(())
    }
}

impl<M: Module> Engine<M> {
    #[inline]
    fn neg_wrap(&mut self, op: OP<M>) -> OP<M> {
        match op {
            FOP(FOP::NEG(_)) | UOP(UOP::NEG(_)) => self.pop(),
            FOP(FOP::CONST(c)) => FOP(FOP::CONST(-c)),
            FOP(op) => FOP(FOP::NEG(op.to_ficv(self))),
            UOP(UOP::CONST([x, y])) => UOP(UOP::CONST([-x, -y])),
            UOP(op) => UOP(UOP::NEG(op.to_uicv(self))),
        }
    }

    #[inline]
    fn not_wrap(&mut self, op: OP<M>) -> OP<M> {
        match op {
            FOP(FOP::NOT(_)) | UOP(UOP::NOT(_)) => self.pop(),
            FOP(FOP::CONST(c)) => FOP(FOP::CONST((c == 0.0).into())),
            FOP(op) => FOP(FOP::NOT(op.to_ficv(self))),
            UOP(UOP::CONST([x, y])) => UOP(UOP::CONST([(x == 0.0).into(), (y == 0.0).into()])),
            UOP(op) => UOP(UOP::NOT(op.to_uicv(self))),
        }
    }

    #[inline]
    fn inv_wrap(&mut self, op: OP<M>) -> OP<M> {
        match op {
            FOP(FOP::INV(_)) | UOP(UOP::INV(_)) => self.pop(),
            FOP(FOP::CONST(c)) => FOP(FOP::CONST(c.recip())),
            FOP(op) => FOP(FOP::INV(op.to_ficv(self))),
            UOP(UOP::CONST([x, y])) => UOP(UOP::CONST([x.recip(), y.recip()])),
            UOP(op) => UOP(UOP::INV(op.to_uicv(self))),
        }
    }

    #[inline]
    fn compile_mul(&mut self, sorted_ops: Vec<OP<M>>) -> OP<M> {
        let mut const_out = FOP(FOP::CONST(1.0));
        let mut out = FOP(FOP::CONST(1.0));

        for op in sorted_ops {
            match (out, op) {
                (FOP(FOP::CONST(c0)), FOP(FOP::CONST(c1))) => {
                    out = FOP(FOP::CONST(c0 * c1));
                }
                (FOP(FOP::CONST(c0)), UOP(UOP::CONST([cx1, cy1]))) => {
                    out = UOP(UOP::CONST([c0 * cx1, c0 * cy1]));
                }
                (UOP(UOP::CONST([cx0, cy0])), UOP(UOP::CONST([cx1, cy1]))) => {
                    out = UOP(UOP::CONST([cx0 * cx1, cy0 * cy1]));
                }
                (op1 @ (FOP(FOP::CONST(_)) | UOP(UOP::CONST(_))), op2 @ _) => {
                    const_out = op1;
                    out = op2;
                }
                (FOP(fop0), FOP(fop1)) => {
                    out = FOP(FOP::MUL(fop0.to_ficv(self), fop1.to_ficv(self)));
                }
                (FOP(fop0), UOP(uop1)) => {
                    out = UOP(UOP::MUL(fop0.to_ficv(self).into(), uop1.to_uicv(self)));
                }
                (UOP(uop0), UOP(uop1)) => {
                    out = UOP(UOP::MUL(uop0.to_uicv(self), uop1.to_uicv(self)));
                }
                _ => unreachable!(), //because of sorting
            }
        }
        match (const_out, out) {
            (FOP(FOP::CONST(1.0)) | UOP(UOP::CONST([1.0, 1.0])), op1 @ _) => op1,
            (FOP(fop0), FOP(fop1)) => FOP(FOP::MUL(fop0.to_ficv(self), fop1.to_ficv(self))),
            (op0 @ (FOP(_) | UOP(_)), op1 @ (FOP(_) | UOP(_))) => UOP(UOP::MUL(
                op0.to_icv(self).try_into().unwrap(),
                op1.to_icv(self).try_into().unwrap(),
            )), // (UOP(fop0), FOP(uop1)) => UOP(UOP::MUL(fop0.to_uicv(self), uop1.to_uicv(self))),
                // (UOP(uop0), UOP(uop1)) => UOP(UOP::MUL(uop0.to_uicv(self), uop1.to_uicv(self))),
        }
    }

    #[inline]
    fn compile_add(&mut self, sorted_ops: Vec<OP<M>>) -> OP<M> {
        let mut const_out = FOP(FOP::CONST(0.0));
        let mut out = FOP(FOP::CONST(0.0));
        // println!("SORTED {:?}", &sorted_ops);
        for op in sorted_ops {
            // println!("!!!!!!!! {:?} {:?}", &out, &op);
            match (out, op) {
                (FOP(FOP::CONST(c0)), FOP(FOP::CONST(c1))) => {
                    out = FOP(FOP::CONST(c0 + c1));
                }
                (FOP(FOP::CONST(c0)), UOP(UOP::CONST([cx1, cy1]))) => {
                    out = UOP(UOP::CONST([c0 + cx1, c0 + cy1]));
                }
                (UOP(UOP::CONST([cx0, cy0])), UOP(UOP::CONST([cx1, cy1]))) => {
                    out = UOP(UOP::CONST([cx0 + cx1, cy0 + cy1]));
                }
                (op1 @ (FOP(FOP::CONST(_)) | UOP(UOP::CONST(_))), op2 @ _) => {
                    const_out = op1;
                    out = op2;
                }
                (FOP(fop0), FOP(fop1)) => {
                    out = FOP(FOP::ADD(fop0.to_ficv(self), fop1.to_ficv(self)));
                }
                (FOP(fop0), UOP(uop1)) => {
                    out = UOP(UOP::ADD(fop0.to_ficv(self).into(), uop1.to_uicv(self)));
                }
                (UOP(uop0), UOP(uop1)) => {
                    out = UOP(UOP::ADD(uop0.to_uicv(self), uop1.to_uicv(self)));
                }
                _ => unreachable!(), //because of sorting
            }
        }
        match (const_out, out) {
            (FOP(FOP::CONST(0.0)) | UOP(UOP::CONST([0.0, 0.0])), op1 @ _) => op1,
            (FOP(fop0), FOP(fop1)) => FOP(FOP::ADD(fop0.to_ficv(self), fop1.to_ficv(self))),
            (op0 @ (FOP(_) | UOP(_)), op1 @ (FOP(_) | UOP(_))) => UOP(UOP::ADD(
                op0.to_icv(self).try_into().unwrap(),
                op1.to_icv(self).try_into().unwrap(),
            )), // (FOP(fop0), UOP(uop1)) => UOP(UOP::ADD(fop0.to_uicv(self), uop1.to_uicv(self))),
                // (UOP(fop0), FOP(uop1)) => UOP(UOP::ADD(fop0.to_uicv(self), uop1.to_uicv(self))),
                // (UOP(uop0), UOP(uop1)) => UOP(UOP::ADD(uop0.to_uicv(self), uop1.to_uicv(self))),
        }
    }

    fn push_fadd_leaf(&mut self, ops: &mut Vec<OP<M>>, icv: F) {
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
    fn push_uadd_leaf(&mut self, ops: &mut Vec<OP<M>>, icv: U) {
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
            U::F(ficv) => self.push_fadd_leaf(ops, ficv),
            U::CONST(c) => ops.push(UOP(UOP::CONST(c))),
            U::VAR(v) => ops.push(UOP(UOP::VAR(v))),
        };
    }

    fn push_fmul_leaf(&mut self, ops: &mut Vec<OP<M>>, icv: F) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match icv {
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

    fn push_umul_leaf(&mut self, ops: &mut Vec<OP<M>>, icv: U) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match icv {
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
            U::F(ficv) => self.push_fmul_leaf(ops, ficv),
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
    fn compile(&self, ast: &Ast, cexpr: &mut Engine<M>, module: &M) -> Result<OP<M>, Error> {
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
            None => return self.0.compile(ast, cexpr, module),
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
            || lowest_op == LTE
            || lowest_op == GTE
        {
            unimplemented!();
            // let mut ops = Vec::<&BinaryOp>::with_capacity(4);
            // let mut xss = Vec::<ExprSlice>::with_capacity(ops.len() + 1);
            // self.split_multi(&[EQ, NE, LT, GT, LTE, GTE], &mut xss, &mut ops);
            // let mut out = xss.first().unwrap().compile(ast, cexpr)?;

            // for (i, op) in ops.into_iter().enumerate() {
            //     let instr = xss.get(i + 1).unwrap().compile(ast, cexpr)?;

            //     if let F(FCONST(l)) = out {
            //         if let F(FCONST(r)) = instr {
            //             out = match op {
            //                 EQ => F(FCONST((l == r).into())),
            //                 NE => F(FCONST((l != r).into())),
            //                 LT => F(FCONST((l < r).into())),
            //                 GT => F(FCONST((l > r).into())),
            //                 LTE => F(FCONST((l <= r).into())),
            //                 GTE => F(FCONST((l >= r).into())),
            //                 _ => unreachable!(),
            //             };
            //             continue;
            //         }
            //     }

            //     out = match op {
            //         EQ => FEQ(cexpr.instr_to_arg(out), cexpr.instr_to_arg(instr)),
            //         NE => FNE(cexpr.instr_to_arg(out), cexpr.instr_to_arg(instr)),
            //         LT => FLT(cexpr.instr_to_arg(out), cexpr.instr_to_arg(instr)),
            //         GT => FGT(cexpr.instr_to_arg(out), cexpr.instr_to_arg(instr)),
            //         LTE => FLTE(cexpr.instr_to_arg(out), cexpr.instr_to_arg(instr)),
            //         GTE => FGTE(cexpr.instr_to_arg(out), cexpr.instr_to_arg(instr)),
            //         _ => unreachable!(),
            //     };
            // }
            // return Ok(out);
        }

        match lowest_op {
            Or => {
                unimplemented!();
                // let mut xss = Vec::<ExprSlice>::with_capacity(4);
                // self.split(Or, &mut xss);
                // let mut out = F(FCONST(0.0));
                // let mut out_set = false;
                // for xs in xss.iter() {
                //     let instr = xs.compile(ast, cexpr)?;
                //     if out_set {
                //         out = FOR(cexpr.instr_to_arg(out), cexpr.instr_to_arg(instr));
                //     } else {
                //         if let F(FCONST(c)) = instr {
                //             if c != 0.0 {
                //                 return Ok(instr);
                //             }
                //             // out = instr;     // Skip this 0 value (mostly so FOP don't complicate my logic in 'if out_set' since FOP can assume that any set value is non-const).
                //             // out_set = true;
                //         } else {
                //             out = instr;
                //             out_set = true;
                //         }
                //     }
                // }
                // Ok(out)
            }

            And => {
                unimplemented!();
                // let mut xss = Vec::<ExprSlice>::with_capacity(4);
                // self.split(And, &mut xss);
                // let mut out = F(FCONST(1.0));
                // let mut out_set = false;
                // for xs in xss.iter() {
                //     let instr = xs.compile(ast, cexpr)?;
                //     if let F(FCONST(c)) = instr {
                //         if c == 0.0 {
                //             return Ok(instr);
                //         }
                //     }
                //     if out_set {
                //         if let F(FCONST(_)) = out {
                //             // If we get here, we know that the const is non-zero.
                //             out = instr;
                //         } else {
                //             out = FAND(cexpr.instr_to_arg(out), cexpr.instr_to_arg(instr));
                //         }
                //     } else {
                //         out = instr;
                //         out_set = true;
                //     }
                // }
                // Ok(out)
            }

            Add => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Add, &mut xss);
                let mut ops = Vec::<OP<M>>::with_capacity(xss.len());
                for xs in xss {
                    let op = xs.compile(ast, cexpr, module)?;
                    match op {
                        FOP(FOP::ADD(licv, ricv)) => {
                            cexpr.push_fadd_leaf(&mut ops, ricv);
                            cexpr.push_fadd_leaf(&mut ops, licv);
                        }
                        UOP(UOP::ADD(licv, ricv)) => {
                            cexpr.push_uadd_leaf(&mut ops, ricv);
                            cexpr.push_uadd_leaf(&mut ops, licv);
                        }
                        _ => {
                            ops.push(op);
                        }
                    }
                }
                sort(&mut ops);
                // println!("sorted: {:?}", ops);
                Ok(cexpr.compile_add(ops))
            }

            Sub => {
                // Note: We don't need to push_add_leaves from here because Sub has a higher precedence than FADD.
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Sub, &mut xss);
                let mut ops = Vec::<OP<M>>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let op = xs.compile(ast, cexpr, module)?;
                    if i == 0 {
                        ops.push(op);
                    } else {
                        ops.push(cexpr.neg_wrap(op));
                    }
                }
                sort(&mut ops);

                Ok(cexpr.compile_add(ops))
            }
            Mul => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Mul, &mut xss);
                let mut ops = Vec::<OP<M>>::with_capacity(xss.len());
                for xs in xss {
                    let op = xs.compile(ast, cexpr, module)?;
                    match op {
                        FOP(FOP::MUL(licv, ricv)) => {
                            cexpr.push_fmul_leaf(&mut ops, ricv);
                            cexpr.push_fmul_leaf(&mut ops, licv);
                        }
                        UOP(UOP::MUL(licv, ricv)) => {
                            cexpr.push_umul_leaf(&mut ops, ricv);
                            cexpr.push_umul_leaf(&mut ops, licv);
                        }
                        _ => {
                            ops.push(op);
                        }
                    }
                }
                sort(&mut ops);
                Ok(cexpr.compile_mul(ops))
            }
            Div => {
                // Note: We don't need to push_mul_leaves from here because Div has a higher precedence than FMUL.

                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(Div, &mut xss);
                let mut ops = Vec::<OP<M>>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let op = xs.compile(ast, cexpr, module)?;
                    if i == 0 {
                        ops.push(op);
                    } else {
                        ops.push(cexpr.inv_wrap(op));
                    }
                }
                sort(&mut ops);
                Ok(cexpr.compile_mul(ops))
            }

            Rem => {
                let mut xss = Vec::<ExprSlice>::with_capacity(2);
                self.split(Rem, &mut xss);
                let mut out = FOP(FOP::CONST(0.0));
                let mut out_set = false;
                for xs in xss.iter() {
                    let op = xs.compile(ast, cexpr, module)?;
                    out = if out_set {
                        let licv = out.to_icv(cexpr);
                        let ricv = op.to_icv(cexpr);
                        match (licv, ricv) {
                            (F(F::CONST(dividend)), F(F::CONST(divisor))) => {
                                FOP(FOP::CONST(f64::rem(dividend, divisor)))
                            }
                            (F(lficv), F(rficv)) => FOP(FOP::REM(lficv, rficv)),
                            (licv @ (F(_) | U(_)), ricv @ (U(_) | F(_))) => {
                                let luicv = licv.try_into().unwrap();
                                let ruicv = ricv.try_into().unwrap();
                                UOP(match (luicv, ruicv) {
                                    (U::CONST(dividend), U::CONST(divisor)) => {
                                        UOP::CONST(<[f64; 2]>::rem(dividend, divisor))
                                    }
                                    _ => UOP::REM(luicv, ruicv),
                                })
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        out_set = true;
                        op
                    };
                }
                Ok(out)
            }
            Exp => {
                let mut xss = Vec::<ExprSlice>::with_capacity(2);
                self.split(Exp, &mut xss);
                let mut out = FOP(FOP::CONST(0.0));
                let mut out_set = false;
                // Right-to-Left Associativity
                for xs in xss.into_iter().rev() {
                    let op = xs.compile(ast, cexpr, module)?;
                    if out_set {
                        match (out, op) {
                            (FOP(FOP::CONST(power)), FOP(FOP::CONST(base))) => {
                                out = FOP(FOP::CONST(base.powf(power)));
                            }
                            (FOP(power), FOP(base)) => {
                                out = FOP(FOP::EXP(base.to_ficv(cexpr), power.to_ficv(cexpr)));
                            }
                            (power @ (FOP(_) | UOP(_)), base @ (UOP(_) | FOP(_))) => {
                                let base = base.to_icv(cexpr).try_into().unwrap();
                                let power = power.to_icv(cexpr).try_into().unwrap();

                                out = UOP(match (base, power) {
                                    (U::CONST(base), U::CONST(power)) => {
                                        UOP::CONST(<[f64; 2]>::pow(base, power))
                                    }
                                    _ => UOP::EXP(base, power),
                                });
                            }
                        }
                    } else {
                        out = op;
                        out_set = true;
                    }
                }
                Ok(out)
            }

            _ => unreachable!(),
        }
    }
}

impl<M: Module> Compiler<M> for Expr {
    fn compile(&self, ast: &Ast, cexpr: &mut Engine<M>, module: &M) -> Result<OP<M>, Error> {
        let top = ExprSlice::from_expr(&self);
        top.compile(ast, cexpr, module)
    }
}

impl<M: Module> Compiler<M> for UnaryOp {
    fn compile(&self, ast: &Ast, cexpr: &mut Engine<M>, module: &M) -> Result<OP<M>, Error> {
        match self {
            Neg(fcv) => {
                let op = fcv.compile(ast, cexpr, module)?;
                Ok(cexpr.neg_wrap(op))
            }

            Not(fcv) => {
                let op = fcv.compile(ast, cexpr, module)?;
                Ok(cexpr.not_wrap(op))
            }
        }
    }
}

impl<M: Module> Compiler<M> for ECV {
    fn compile(&self, ast: &Ast, cexpr: &mut Engine<M>, module: &M) -> Result<OP<M>, Error> {
        match self {
            Const(c) => Ok(FOP(FOP::CONST(*c))),
            Var(name) => {
                if let Some(op) = module.dispatch_var(name) {
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
            E(i) => ast.get_expr(*i).compile(ast, cexpr, module),
        }
    }
}

impl<M: Module> Compiler<M> for Value {
    fn compile(&self, ast: &Ast, cexpr: &mut Engine<M>, module: &M) -> Result<OP<M>, Error> {
        match self {
            ECV(ecv) => ecv.compile(ast, cexpr, module),
            UnaryOp(u) => u.compile(ast, cexpr, module),
            Func(name, sarg, eargs) => {
                let mut args = if let Some(s) = sarg {
                    let mut args = Vec::with_capacity(eargs.len() + 1);
                    args.push(s.clone().into());
                    args
                } else {
                    Vec::with_capacity(eargs.len())
                };

                for earg in eargs {
                    let op = earg.compile(ast, cexpr, module)?;
                    let arg = op.to_icv(cexpr);
                    args.push(arg);
                }
                match module.dispatch_func(&name, &args) {
                    Some(op) => Ok(op),
                    _ => Err(Error::Undefined(name.to_owned())),
                }
                // ("if", None, [cond, then, else_]) => {
                //     let cond = cond.compile(ast, cexpr)?;
                //     let then = then.compile(ast, cexpr)?;
                //     let else_ = else_.compile(ast, cexpr)?;
                //     match (cond, then, else_) {
                //         (FOP(FOP::CONST(0.0)), _, a2) => Ok(a2),
                //         (FOP(FOP::CONST(_)), a1, _) => Ok(a1),
                //         (FOP(cond), FOP(a1), FOP(a2)) => Ok(FOP(FIF(
                //             cond.to_icv(cexpr),
                //             a1.to_icv(cexpr),
                //             a2.to_icv(cexpr),
                //         ))),
                //         (FOP(cond), UOP(a1), UOP(a2)) => Ok(UOP(UIF(
                //             cond.to_icv(cexpr),
                //             a1.to_icv(cexpr),
                //             a2.to_icv(cexpr),
                //         ))),

                //         _ => Err(Error::Undefined("if".into())),
                //     }
                // }
                // _ => {
                //     let mut args = Vec::with_capacity(2);
                //     for earg in eargs {
                //         let op = earg.compile(ast, cexpr)?;
                //         let arg = op.to_icv(cexpr);
                //         args.push(arg);
                //     }

                //     if let Some(op) = cexpr.module.func(name, sarg, &args) {
                //         Ok(op)
                //     } else {
                //         Err(Error::Undefined(name.to_owned()))
                //     }
                //}
            }
            List(vals) => match &vals.as_slice() {
                &[ECV::Const(cx), ECV::Const(cy)] => Ok(UOP(UOP::CONST([*cx, *cy]))),
                &[x, y] => {
                    let x: FOP<M::FFN> = x.compile(ast, cexpr, module)?.try_into()?;
                    let y: FOP<M::FFN> = y.compile(ast, cexpr, module)?.try_into()?;
                    Ok(UOP(UOP::SET(x.to_ficv(cexpr), y.to_ficv(cexpr))))
                }
                _ => Err(Error::InvalidSyntax(
                    "The vector must be 2 to 3 elements long".into(),
                )),
            },

            _ => unreachable!(),
        }
    }
}
