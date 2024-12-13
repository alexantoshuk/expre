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
//! * The `FICV` enumeration helps to eliminate expensive function calls.

use crate::context::*;
use crate::error::Error;
// pub use crate::parser::F;
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

type OP<M: Module> = ops::OP<M::FFN, M::UFN>;

impl Ast {
    pub fn compile<M: Module>(&self, cexpr: &mut CExpr<M>, module: &M) -> Result<(), Error> {
        cexpr.compile(self, module)
    }
}

pub fn compile<M: Module>(ast: &Ast, cexpr: &mut CExpr<M>, module: &M) -> Result<(), Error> {
    CExpr::compile(cexpr, ast, module)
}

/// You must `use` the `Compiler` trait before you can call `.compile()` on parsed `Expr`s.
pub trait Compiler<M: Module> {
    /// Turns a parsed `Expr` into a compiled `OP`.
    ///
    /// Cannot fail, unless you run out of memory.
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>, module: &M) -> Result<OP<M>, Error>;
}

/// `CExpr` is where `compile()` results are stored.
pub struct CExpr<M: Module> {
    pub(crate) ops: Vec<OP<M>>,
}

impl<M: Module> CExpr<M> {
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
    /// located at `instr_i` within the `CExpr.ops'.
    ///
    /// If `instr_i` is out-of-bounds, a reference to a default `OP` is returned.
    ///
    #[inline]
    pub fn get(&self, instr_i: usize) -> &OP<M> {
        // unsafe{self.ops.get_unchecked(instr_i)}
        self.ops.get(instr_i).unwrap()
    }

    /// Appends an `OP` to `CExpr.ops`.
    #[inline]
    pub fn push(&mut self, instr: OP<M>) -> usize {
        let i = self.ops.len();
        self.ops.push(instr);
        i
    }

    /// Removes an `OP` from `CExpr.ops` as efficiently as possible.
    #[inline]
    pub fn pop(&mut self) -> OP<M> {
        self.ops.pop().unwrap()
    }

    /// Clears all data from `CExpr.ops`.
    #[inline]
    pub fn clear(&mut self) {
        self.ops.clear();
    }

    // #[inline]
    // pub fn instr_to_arg(&mut self, op: OP<M>) -> ICV {
    //     match op {
    //         F(FICV(a)) => ICV::FICV(a),
    //         U(UICV(a)) => ICV::UICV(a),
    //         F(_) => ICV::FICV(F(self.push(op))),
    //         U(_) => ICV::UICV(U(self.push(op))),
    //     }
    // }
}

// impl OP<M> {
//     #[inline]
//     fn to_uicv<M>(self, expr: &mut CExpr<M>) -> FICV {
//         match self {
//             F(op) => FICV::FICV(op.to_icv(expr)),
//             U(op) => UICV::UICV(op.to_icv(expr)),
//         }
//     }
// }

impl<FFN, UFN> ops::OP<FFN, UFN> {
    #[inline]
    fn to_ficv<M: Module<FFN = FFN, UFN = UFN>>(self, expr: &mut CExpr<M>) -> FICV {
        match self {
            F(F::CONST(c)) => FICV::CONST(c),
            F(F::VAR(v)) => FICV::VAR(v),
            F(_) => FICV::I(expr.push(self)),

            U(U::CONST(c)) => FICV::CONST(c[0]),
            U(U::VAR(v)) => FICV::VAR(v),
            U(_) => FICV::I(expr.push(self)),
        }
    }

    #[inline]
    fn to_uicv<M: Module<FFN = FFN, UFN = UFN>>(self, expr: &mut CExpr<M>) -> UICV {
        match self {
            U(U::CONST(c)) => UICV::CONST(c),
            U(U::VAR(v)) => UICV::VAR(v),
            U(_) => UICV::I(expr.push(self)),

            F(F::CONST(c)) => UICV::CONST([c; 2]),
            // F(F::VAR(c)) => UICV::FROM(FICV::VAR(c)),
            F(_) => UICV::I(expr.push(self)),
        }
    }
}

impl<FFN> F<FFN> {
    #[inline]
    fn to_ficv<M: Module<FFN = FFN>>(self, expr: &mut CExpr<M>) -> FICV {
        match self {
            F::CONST(c) => FICV::CONST(c),
            F::VAR(v) => FICV::VAR(v),
            _ => FICV::I(expr.push(F(self))),
        }
    }

    #[inline]
    fn to_uicv<M: Module<FFN = FFN>>(self, expr: &mut CExpr<M>) -> UICV {
        match self {
            F::CONST(c) => UICV::CONST([c; 2]),
            _ => UICV::I(expr.push(F(self))),
        }
    }
}

impl<UFN> U<UFN> {
    #[inline]
    fn to_ficv<M: Module<UFN = UFN>>(self, expr: &mut CExpr<M>) -> FICV {
        match self {
            U::CONST(c) => FICV::CONST(c[0]),
            U::VAR(v) => FICV::VAR(v),
            _ => FICV::I(expr.push(U(self))),
        }
    }

    #[inline]
    fn to_uicv<M: Module<UFN = UFN>>(self, expr: &mut CExpr<M>) -> UICV {
        match self {
            U::CONST(c) => UICV::CONST(c),
            U::VAR(v) => UICV::VAR(v),
            _ => UICV::I(expr.push(U(self))),
        }
    }
}

impl<M: Module> Debug for CExpr<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        debug_indexed_list(f, &self.ops)?;
        Ok(())
    }
}

impl<M: Module> CExpr<M> {
    #[inline]
    fn neg_wrap(&mut self, op: OP<M>) -> OP<M> {
        match op {
            F(F::NEG(_)) | U(U::NEG(_)) => self.pop(),
            F(F::CONST(c)) => F(F::CONST(-c)),
            F(op) => F(F::NEG(op.to_ficv(self))),
            U(U::CONST([x, y])) => U(U::CONST([-x, -y])),
            U(op) => U(U::NEG(op.to_uicv(self))),
        }
    }

    #[inline]
    fn not_wrap(&mut self, op: OP<M>) -> OP<M> {
        match op {
            F(F::NOT(_)) | U(U::NOT(_)) => self.pop(),
            F(F::CONST(c)) => F(F::CONST((c == 0.0).into())),
            F(op) => F(F::NOT(op.to_ficv(self))),
            U(U::CONST([x, y])) => U(U::CONST([(x == 0.0).into(), (y == 0.0).into()])),
            U(op) => U(U::NOT(op.to_uicv(self))),
        }
    }

    #[inline]
    fn inv_wrap(&mut self, op: OP<M>) -> OP<M> {
        match op {
            F(F::INV(_)) | U(U::INV(_)) => self.pop(),
            F(F::CONST(c)) => F(F::CONST(c.recip())),
            F(op) => F(F::INV(op.to_ficv(self))),
            U(U::CONST([x, y])) => U(U::CONST([x.recip(), y.recip()])),
            U(op) => U(U::INV(op.to_uicv(self))),
        }
    }

    #[inline]
    fn compile_mul(&mut self, sorted_ops: Vec<OP<M>>) -> OP<M> {
        let mut const_out = F(F::CONST(1.0));
        let mut out = F(F::CONST(1.0));

        for op in sorted_ops {
            match (out, op) {
                (F(F::CONST(c0)), F(F::CONST(c1))) => {
                    out = F(F::CONST(c0 * c1));
                }
                (F(F::CONST(c0)), U(U::CONST([cx1, cy1]))) => {
                    out = U(U::CONST([c0 * cx1, c0 * cy1]));
                }
                (U(U::CONST([cx0, cy0])), U(U::CONST([cx1, cy1]))) => {
                    out = U(U::CONST([cx0 * cx1, cy0 * cy1]));
                }
                (op1 @ (F(F::CONST(_)) | U(U::CONST(_))), op2 @ _) => {
                    const_out = op1;
                    out = op2;
                }
                (F(fop0), F(fop1)) => {
                    out = F(F::MUL(fop0.to_ficv(self), fop1.to_ficv(self)));
                }
                (F(fop0), U(uop1)) => {
                    out = U(U::MUL(fop0.to_uicv(self), uop1.to_uicv(self)));
                }
                (U(uop0), U(uop1)) => {
                    out = U(U::MUL(uop0.to_uicv(self), uop1.to_uicv(self)));
                }
                _ => unreachable!(), //because of sorting
            }
        }
        match (const_out, out) {
            (F(F::CONST(1.0)) | U(U::CONST([1.0, 1.0])), op1 @ _) => op1,
            (F(fop0), F(fop1)) => F(F::MUL(fop0.to_ficv(self), fop1.to_ficv(self))),
            (op0 @ (F(_) | U(_)), op1 @ (F(_) | U(_))) => {
                U(U::MUL(op0.to_uicv(self), op1.to_uicv(self)))
            } // (U(fop0), F(uop1)) => U(U::MUL(fop0.to_uicv(self), uop1.to_uicv(self))),
              // (U(uop0), U(uop1)) => U(U::MUL(uop0.to_uicv(self), uop1.to_uicv(self))),
        }
    }

    #[inline]
    fn compile_add(&mut self, sorted_ops: Vec<OP<M>>) -> OP<M> {
        let mut const_out = F(F::CONST(0.0));
        let mut out = F(F::CONST(0.0));
        // println!("SORTED {:?}", &sorted_ops);
        for op in sorted_ops {
            // println!("!!!!!!!! {:?} {:?}", &out, &op);
            match (out, op) {
                (F(F::CONST(c0)), F(F::CONST(c1))) => {
                    out = F(F::CONST(c0 + c1));
                }
                (F(F::CONST(c0)), U(U::CONST([cx1, cy1]))) => {
                    out = U(U::CONST([c0 + cx1, c0 + cy1]));
                }
                (U(U::CONST([cx0, cy0])), U(U::CONST([cx1, cy1]))) => {
                    out = U(U::CONST([cx0 + cx1, cy0 + cy1]));
                }
                (op1 @ (F(F::CONST(_)) | U(U::CONST(_))), op2 @ _) => {
                    const_out = op1;
                    out = op2;
                }
                (F(fop0), F(fop1)) => {
                    out = F(F::ADD(fop0.to_ficv(self), fop1.to_ficv(self)));
                }
                (F(fop0), U(uop1)) => {
                    out = U(U::ADD(fop0.to_uicv(self), uop1.to_uicv(self)));
                }
                (U(uop0), U(uop1)) => {
                    out = U(U::ADD(uop0.to_uicv(self), uop1.to_uicv(self)));
                }
                _ => unreachable!(), //because of sorting
            }
        }
        match (const_out, out) {
            (F(F::CONST(0.0)) | U(U::CONST([0.0, 0.0])), op1 @ _) => op1,
            (F(fop0), F(fop1)) => F(F::ADD(fop0.to_ficv(self), fop1.to_ficv(self))),
            (op0 @ (F(_) | U(_)), op1 @ (F(_) | U(_))) => {
                U(U::ADD(op0.to_uicv(self), op1.to_uicv(self)))
            } // (F(fop0), U(uop1)) => U(U::ADD(fop0.to_uicv(self), uop1.to_uicv(self))),
              // (U(fop0), F(uop1)) => U(U::ADD(fop0.to_uicv(self), uop1.to_uicv(self))),
              // (U(uop0), U(uop1)) => U(U::ADD(uop0.to_uicv(self), uop1.to_uicv(self))),
        }
    }

    fn push_fadd_leaf(&mut self, ops: &mut Vec<OP<M>>, icv: FICV) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match icv {
            FICV::I(_) => {
                let op = self.pop();
                match op {
                    F(F::ADD(l, r)) => {
                        self.push_fadd_leaf(ops, r);
                        self.push_fadd_leaf(ops, l);
                    }
                    U(U::ADD(l, r)) => {
                        self.push_uadd_leaf(ops, r);
                        self.push_uadd_leaf(ops, l);
                    }
                    _ => {
                        ops.push(op);
                    }
                }
            }
            FICV::CONST(c) => ops.push(F(F::CONST(c))),
            FICV::VAR(v) => ops.push(F(F::VAR(v))),
        };
    }
    fn push_uadd_leaf(&mut self, ops: &mut Vec<OP<M>>, icv: UICV) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match icv {
            UICV::I(_) => {
                let op = self.pop();
                match op {
                    U(U::ADD(l, r)) => {
                        self.push_uadd_leaf(ops, r);
                        self.push_uadd_leaf(ops, l);
                    }
                    F(F::ADD(l, r)) => {
                        self.push_fadd_leaf(ops, r);
                        self.push_fadd_leaf(ops, l);
                    }
                    _ => {
                        ops.push(op);
                    }
                }
            }
            // UICV::FROM(ficv) => self.push_fadd_leaf(ops, ficv),
            UICV::CONST(c) => ops.push(U(U::CONST(c))),
            UICV::VAR(v) => ops.push(U(U::VAR(v))),
        };
    }

    fn push_fmul_leaf(&mut self, ops: &mut Vec<OP<M>>, icv: FICV) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match icv {
            FICV::I(_) => {
                let op = self.pop();
                match op {
                    F(F::MUL(l, r)) => {
                        self.push_fmul_leaf(ops, r);
                        self.push_fmul_leaf(ops, l);
                    }
                    U(U::MUL(l, r)) => {
                        self.push_umul_leaf(ops, r);
                        self.push_umul_leaf(ops, l);
                    }
                    _ => {
                        ops.push(op);
                    }
                }
            }
            FICV::CONST(c) => ops.push(F(F::CONST(c))),
            FICV::VAR(v) => ops.push(F(F::VAR(v))),
        };
    }

    fn push_umul_leaf(&mut self, ops: &mut Vec<OP<M>>, icv: UICV) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match icv {
            UICV::I(_) => {
                let op = self.pop();
                match op {
                    U(U::MUL(l, r)) => {
                        self.push_umul_leaf(ops, r);
                        self.push_umul_leaf(ops, l);
                    }
                    F(F::MUL(l, r)) => {
                        self.push_fmul_leaf(ops, r);
                        self.push_fmul_leaf(ops, l);
                    }
                    _ => {
                        ops.push(op);
                    }
                }
            }
            // UICV::FROM(ficv) => self.push_fmul_leaf(ops, ficv),
            UICV::CONST(c) => ops.push(U(U::CONST(c))),
            UICV::VAR(v) => ops.push(U(U::VAR(v))),
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
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>, module: &M) -> Result<OP<M>, Error> {
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

            //     if let FICV(FCONST(l)) = out {
            //         if let FICV(FCONST(r)) = instr {
            //             out = match op {
            //                 EQ => FICV(FCONST((l == r).into())),
            //                 NE => FICV(FCONST((l != r).into())),
            //                 LT => FICV(FCONST((l < r).into())),
            //                 GT => FICV(FCONST((l > r).into())),
            //                 LTE => FICV(FCONST((l <= r).into())),
            //                 GTE => FICV(FCONST((l >= r).into())),
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
                // let mut out = FICV(FCONST(0.0));
                // let mut out_set = false;
                // for xs in xss.iter() {
                //     let instr = xs.compile(ast, cexpr)?;
                //     if out_set {
                //         out = FOR(cexpr.instr_to_arg(out), cexpr.instr_to_arg(instr));
                //     } else {
                //         if let FICV(FCONST(c)) = instr {
                //             if c != 0.0 {
                //                 return Ok(instr);
                //             }
                //             // out = instr;     // Skip this 0 value (mostly so F don't complicate my logic in 'if out_set' since F can assume that any set value is non-const).
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
                // let mut out = FICV(FCONST(1.0));
                // let mut out_set = false;
                // for xs in xss.iter() {
                //     let instr = xs.compile(ast, cexpr)?;
                //     if let FICV(FCONST(c)) = instr {
                //         if c == 0.0 {
                //             return Ok(instr);
                //         }
                //     }
                //     if out_set {
                //         if let FICV(FCONST(_)) = out {
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
                        F(F::ADD(licv, ricv)) => {
                            cexpr.push_fadd_leaf(&mut ops, ricv);
                            cexpr.push_fadd_leaf(&mut ops, licv);
                        }
                        U(U::ADD(licv, ricv)) => {
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
                        F(F::MUL(licv, ricv)) => {
                            cexpr.push_fmul_leaf(&mut ops, ricv);
                            cexpr.push_fmul_leaf(&mut ops, licv);
                        }
                        U(U::MUL(licv, ricv)) => {
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

            Mod => {
                let mut xss = Vec::<ExprSlice>::with_capacity(2);
                self.split(Mod, &mut xss);
                let mut out = F(F::CONST(0.0));
                let mut out_set = false;
                for xs in xss.iter() {
                    let op = xs.compile(ast, cexpr, module)?;
                    if out_set {
                        match (out, op) {
                            (F(F::CONST(dividend)), F(F::CONST(divisor))) => {
                                out = F(F::CONST(f64::rem(dividend, divisor)));
                            }
                            (F(divisor), F(dividend)) => {
                                out = F(F::MOD(dividend.to_ficv(cexpr), divisor.to_ficv(cexpr)));
                            }
                            (divisor @ (F(_) | U(_)), dividend @ (U(_) | F(_))) => {
                                let dividend = dividend.to_uicv(cexpr);
                                let divisor = divisor.to_uicv(cexpr);
                                out = U(match (dividend, divisor) {
                                    (UICV::CONST(dividend), UICV::CONST(divisor)) => {
                                        U::CONST(map2!(f64::rem, dividend, divisor))
                                    }
                                    _ => U::MOD(dividend, divisor),
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
            Exp => {
                let mut xss = Vec::<ExprSlice>::with_capacity(2);
                self.split(Exp, &mut xss);
                let mut out = F(F::CONST(0.0));
                let mut out_set = false;
                // Right-to-Left Associativity
                for xs in xss.into_iter().rev() {
                    let op = xs.compile(ast, cexpr, module)?;
                    if out_set {
                        match (out, op) {
                            (F(F::CONST(power)), F(F::CONST(base))) => {
                                out = F(F::CONST(base.powf(power)));
                            }
                            (F(power), F(base)) => {
                                out = F(F::EXP(base.to_ficv(cexpr), power.to_ficv(cexpr)));
                            }
                            (power @ (F(_) | U(_)), base @ (U(_) | F(_))) => {
                                let base = base.to_uicv(cexpr);
                                let power = power.to_uicv(cexpr);

                                out = U(match (base, power) {
                                    (UICV::CONST(base), UICV::CONST(power)) => {
                                        U::CONST(map2!(f64::pow, base, power))
                                    }
                                    _ => U::EXP(base, power),
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
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>, module: &M) -> Result<OP<M>, Error> {
        let top = ExprSlice::from_expr(&self);
        top.compile(ast, cexpr, module)
    }
}

impl<M: Module> Compiler<M> for UnaryOp {
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>, module: &M) -> Result<OP<M>, Error> {
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
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>, module: &M) -> Result<OP<M>, Error> {
        match self {
            Const(c) => Ok(F(F::CONST(*c))),
            Var(name) => {
                if let Some(op) = module.var(name) {
                    Ok(op)
                } else {
                    match name.as_str() {
                        // builtins constants
                        "PI" => Ok(F(F::CONST(f64::PI))),
                        "E" => Ok(F(F::CONST(f64::E))),
                        "EPS" => Ok(F(F::CONST(f64::EPSILON))),
                        _ => Err(Error::Undefined(name.to_owned())),
                    }
                }
            }
            E(i) => ast.get_expr(*i).compile(ast, cexpr, module),
        }
    }
}

impl<M: Module> Compiler<M> for Value {
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>, module: &M) -> Result<OP<M>, Error> {
        match self {
            ECV(ecv) => ecv.compile(ast, cexpr, module),
            UnaryOp(u) => u.compile(ast, cexpr, module),
            Func(name, sarg, eargs) => {
                match (name.as_str(), sarg.as_ref(), eargs.as_slice()) {
                    _ => unimplemented!(),
                }
                // ("if", None, [cond, then, else_]) => {
                //     let cond = cond.compile(ast, cexpr)?;
                //     let then = then.compile(ast, cexpr)?;
                //     let else_ = else_.compile(ast, cexpr)?;
                //     match (cond, then, else_) {
                //         (F(F::CONST(0.0)), _, a2) => Ok(a2),
                //         (F(F::CONST(_)), a1, _) => Ok(a1),
                //         (F(cond), F(a1), F(a2)) => Ok(F(FIF(
                //             cond.to_icv(cexpr),
                //             a1.to_icv(cexpr),
                //             a2.to_icv(cexpr),
                //         ))),
                //         (F(cond), U(a1), U(a2)) => Ok(U(UIF(
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
                &[ECV::Const(cx), ECV::Const(cy)] => Ok(U(U::CONST([*cx, *cy]))),
                &[x, y] => {
                    let x: F<M::FFN> = x.compile(ast, cexpr, module)?.try_into()?;
                    let y: F<M::FFN> = y.compile(ast, cexpr, module)?.try_into()?;
                    Ok(U(U::SET(x.to_ficv(cexpr), y.to_ficv(cexpr))))
                }
                _ => Err(Error::InvalidSyntax(
                    "The vector must be 2 to 3 elements long".into(),
                )),
            },

            _ => unreachable!(),
        }
    }
}
