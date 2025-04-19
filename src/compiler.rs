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

/// `Expression` is where `compile()` results are stored.
pub struct Expression<'m, M: Module> {
    module: &'m M,
    locals: IndexMap<String, ICV>,
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

        for stmt in &ast.stmts {
            match stmt {
                Statement::OpAssign(name, aop, ecv) => match aop {
                    Assign => {
                        let op = ecv.compile(ast, self)?;
                        let icv = op.into_icv(self);
                        self.locals.insert(name.into(), icv);
                    }
                    AddAssign => {
                        let ex = Expr(ECV(ECV::Var(name.clone())), vec![(Add, ECV(ecv.clone()))]);
                        let op = ex.compile(ast, self)?;
                        let icv = op.into_icv(self);
                        self.locals.insert(name.into(), icv);
                    }
                    _ => unimplemented!(),
                },
            }
        }
        let last = ast.exprs.last().unwrap();
        let op = last.compile(ast, self)?;
        match op {
            Fop(Fop::I(i)) => self.ops.truncate(i + 1),
            F2op(F2op::I(i)) => self.ops.truncate(i + 1),
            F3op(F3op::I(i)) => self.ops.truncate(i + 1),
            Bop(Bop::I(i)) => self.ops.truncate(i + 1),
            _ => self.ops.push(op),
        }

        Ok(())
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

pub trait IntoICV<M: Module, T>: Sized {
    fn into_icv(self, ex: &mut Expression<M>) -> T;
}

impl<M: Module> IntoICV<M, ICV> for OP {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> ICV {
        match self {
            Fop(f) => F(f.into_icv(ex)),
            F2op(f2) => F2(f2.into_icv(ex)),
            F3op(f3) => F3(f3.into_icv(ex)),
            Bop(b) => B(b.into_icv(ex)),
        }
    }
}

impl<M: Module> IntoICV<M, B> for Bop {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> B {
        match self {
            Bop::CONST(c) => B::CONST(c),
            Bop::I(i) => B::I(i),
            _ => B::I(ex.push(Bop(self))),
        }
    }
}

impl<M: Module> IntoICV<M, F> for Bop {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> F {
        match self {
            Bop::CONST(c) => F::CONST(c.into()),
            Bop::I(i) => F::I(i),
            _ => F::I(ex.push(Bop(self))),
        }
    }
}

impl<M: Module> IntoICV<M, F2> for Bop {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> F2 {
        match self {
            Bop::CONST(c) => F2::CONST([c.into(); 2]),
            Bop::I(i) => F2::F(F::I(i)),
            _ => F2::F(F::I(ex.push(Bop(self)))),
        }
    }
}

impl<M: Module> IntoICV<M, F3> for Bop {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> F3 {
        match self {
            Bop::CONST(c) => F3::CONST([c.into(); 3]),
            Bop::I(i) => F3::F(F::I(i)),
            _ => F3::F(F::I(ex.push(Bop(self)))),
        }
    }
}

impl<M: Module> IntoICV<M, F> for Fop {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> F {
        match self {
            Fop::CONST(c) => F::CONST(c),
            Fop::VAR(v) => F::VAR(v),
            Fop::I(i) => F::I(i),
            _ => F::I(ex.push(Fop(self))),
        }
    }
}

impl<M: Module> IntoICV<M, B> for Fop {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> B {
        match self {
            Fop::CONST(c) => B::CONST((c != 0.0).into()),
            Fop::VAR(v) => B::VAR(v),
            Fop::I(i) => B::I(i),
            _ => B::I(ex.push(Fop(self))),
        }
    }
}

impl<M: Module> IntoICV<M, F2> for Fop {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> F2 {
        match self {
            Fop::CONST(c) => F2::CONST([c; 2]),
            Fop::I(i) => F2::F(F::I(i)),
            _ => F2::F(F::I(ex.push(Fop(self)))),
        }
    }
}

impl<M: Module> IntoICV<M, F3> for Fop {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> F3 {
        match self {
            Fop::CONST(c) => F3::CONST([c; 3]),
            Fop::I(i) => F3::F(F::I(i)),
            _ => F3::F(F::I(ex.push(Fop(self)))),
        }
    }
}

impl<M: Module> IntoICV<M, F2> for F2op {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> F2 {
        match self {
            F2op::CONST(c) => F2::CONST(c),
            F2op::VAR(v) => F2::VAR(v),
            F2op::I(i) => F2::I(i),
            _ => F2::I(ex.push(F2op(self))),
        }
    }
}

impl<M: Module> IntoICV<M, F3> for F3op {
    #[inline]
    fn into_icv(self, ex: &mut Expression<M>) -> F3 {
        match self {
            F3op::CONST(c) => F3::CONST(c),
            F3op::VAR(v) => F3::VAR(v),
            F3op::I(i) => F3::I(i),
            _ => F3::I(ex.push(F3op(self))),
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
            Fop(Fop::NEG(_)) | F2op(F2op::NEG(_)) | F3op(F3op::NEG(_)) => self.pop(),
            Fop(Fop::CONST(c)) => Fop(Fop::CONST(-c)),
            Fop(op) => Fop(Fop::NEG(op.into_icv(self))),

            F2op(F2op::CONST([x, y])) => F2op(F2op::CONST([-x, -y])),
            F2op(op) => F2op(F2op::NEG(op.into_icv(self))),

            F3op(F3op::CONST([x, y, z])) => F3op(F3op::CONST([-x, -y, -z])),
            F3op(op) => F3op(F3op::NEG(op.into_icv(self))),

            Bop(Bop::CONST(c)) => Fop(Fop::CONST(-f64::from(c))),
            Bop(op) => Fop(Fop::NEG(op.into_icv(self))),
        }
    }

    #[inline]
    fn not_wrap(&mut self, op: OP) -> Result<OP, Error> {
        match op {
            Bop(Bop::NOT(_)) => Ok(self.pop()),
            Bop(Bop::CONST(c)) => Ok(Bop(Bop::CONST(!c))),
            Bop(op) => Ok(Bop(Bop::NOT(op.into_icv(self)))),

            Fop(Fop::CONST(c)) => Ok(Bop(Bop::CONST((c == 0.0).into()))),
            Fop(op) => Ok(Bop(Bop::NOT(op.into_icv(self)))),
            _ => Err(Error::InvalidType(
                "invalid operand type for ! operator".into(),
            )),
        }
    }

    #[inline]
    fn inv_wrap(&mut self, op: OP) -> OP {
        match op {
            Fop(Fop::INV(_)) | F2op(F2op::INV(_)) => self.pop(),
            Fop(Fop::CONST(c)) => Fop(Fop::CONST(c.recip())),
            Fop(op) => Fop(Fop::INV(op.into_icv(self))),

            F2op(F2op::CONST([x, y])) => F2op(F2op::CONST([x.recip(), y.recip()])),
            F2op(op) => F2op(F2op::INV(op.into_icv(self))),

            F3op(F3op::CONST([x, y, z])) => F3op(F3op::CONST([x.recip(), y.recip(), z.recip()])),
            F3op(op) => F3op(F3op::INV(op.into_icv(self))),

            Bop(Bop::CONST(c)) => Fop(Fop::CONST(f64::from(c).recip())),
            Bop(op) => Fop(Fop::INV(op.into_icv(self))),
        }
    }

    #[inline]
    fn compile_mul(&mut self, sorted_ops: Vec<OP>) -> Result<OP, Error> {
        let mut const_out = Fop(Fop::CONST(1.0));
        let mut out = Fop(Fop::CONST(1.0));

        for op in sorted_ops {
            match (out, op) {
                (Fop(Fop::CONST(c0)), Fop(Fop::CONST(c1))) => {
                    out = Fop(Fop::CONST(c0 * c1));
                }
                (Fop(Fop::CONST(c0)), F2op(F2op::CONST([cx1, cy1]))) => {
                    out = F2op(F2op::CONST([c0 * cx1, c0 * cy1]));
                }
                (F2op(F2op::CONST([cx0, cy0])), F2op(F2op::CONST([cx1, cy1]))) => {
                    out = F2op(F2op::CONST([cx0 * cx1, cy0 * cy1]));
                }
                (Fop(Fop::CONST(c0)), F3op(F3op::CONST([cx1, cy1, cz1]))) => {
                    out = F3op(F3op::CONST([c0 * cx1, c0 * cy1, c0 * cz1]));
                }
                (F3op(F3op::CONST([cx0, cy0, cz0])), F3op(F3op::CONST([cx1, cy1, cz1]))) => {
                    out = F3op(F3op::CONST([cx0 * cx1, cy0 * cy1, cz0 * cz1]));
                }
                (op1 @ (Fop(Fop::CONST(_)) | F2op(F2op::CONST(_)) | F3op(F3op::CONST(_))), op2) => {
                    const_out = op1;
                    out = op2;
                }

                (Fop(fop0), Fop(fop1)) => {
                    out = Fop(Fop::MUL(fop0.into_icv(self), fop1.into_icv(self)));
                }
                (Fop(fop0), F2op(uop1)) => {
                    out = F2op(F2op::MUL(fop0.into_icv(self), uop1.into_icv(self)));
                }
                (F2op(uop0), F2op(uop1)) => {
                    out = F2op(F2op::MUL(uop0.into_icv(self), uop1.into_icv(self)));
                }
                (Fop(fop0), F3op(uop1)) => {
                    out = F3op(F3op::MUL(fop0.into_icv(self), uop1.into_icv(self)));
                }
                (F3op(uop0), F3op(uop1)) => {
                    out = F3op(F3op::MUL(uop0.into_icv(self), uop1.into_icv(self)));
                }
                (l, r) => {
                    return Err(Error::InvalidType(
                        "invalid operands type for '*' operator".into(),
                    ))
                }
            }
        }

        match (const_out, out) {
            (Fop(Fop::CONST(1.0)), op1 @ Fop(_)) => Ok(op1),
            (Fop(fop0), Fop(fop1)) => Ok(Fop(Fop::MUL(fop0.into_icv(self), fop1.into_icv(self)))),
            (F2op(F2op::CONST([1.0, 1.0])), op1 @ F2op(_)) => Ok(op1),
            (op0 @ (Fop(_) | F2op(_)), op1 @ (Fop(_) | F2op(_))) => {
                let l = op0.into_icv(self).try_into().unwrap();
                let r = op1.into_icv(self).try_into().unwrap();
                Ok(F2op(F2op::MUL(l, r)))
            }
            (F3op(F3op::CONST([1.0, 1.0, 1.0])), op1 @ F3op(_)) => Ok(op1),
            (op0 @ (Fop(_) | F3op(_)), op1 @ (Fop(_) | F3op(_))) => {
                let l = op0.into_icv(self).try_into().unwrap();
                let r = op1.into_icv(self).try_into().unwrap();
                Ok(F3op(F3op::MUL(l, r)))
            }
            _ => Err(Error::Unreachable),
        }
    }

    #[inline]
    fn compile_add(&mut self, sorted_ops: Vec<OP>) -> Result<OP, Error> {
        let mut const_out = Fop(Fop::CONST(0.0));
        let mut out = Fop(Fop::CONST(0.0));

        for op in sorted_ops {
            match (out, op) {
                (Fop(Fop::CONST(c0)), Fop(Fop::CONST(c1))) => {
                    out = Fop(Fop::CONST(c0 + c1));
                }
                (Fop(Fop::CONST(c0)), F2op(F2op::CONST([cx1, cy1]))) => {
                    out = F2op(F2op::CONST([c0 + cx1, c0 + cy1]));
                }
                (F2op(F2op::CONST([cx0, cy0])), F2op(F2op::CONST([cx1, cy1]))) => {
                    out = F2op(F2op::CONST([cx0 + cx1, cy0 + cy1]));
                }
                (Fop(Fop::CONST(c0)), F3op(F3op::CONST([cx1, cy1, cz1]))) => {
                    out = F3op(F3op::CONST([c0 + cx1, c0 + cy1, c0 + cz1]));
                }
                (F3op(F3op::CONST([cx0, cy0, cz0])), F3op(F3op::CONST([cx1, cy1, cz1]))) => {
                    out = F3op(F3op::CONST([cx0 + cx1, cy0 + cy1, cz0 + cz1]));
                }
                (op1 @ (Fop(Fop::CONST(_)) | F2op(F2op::CONST(_)) | F3op(F3op::CONST(_))), op2) => {
                    const_out = op1;
                    out = op2;
                }

                (Fop(fop0), Fop(fop1)) => {
                    out = Fop(Fop::ADD(fop0.into_icv(self), fop1.into_icv(self)));
                }
                (Fop(fop0), F2op(uop1)) => {
                    out = F2op(F2op::ADD(fop0.into_icv(self), uop1.into_icv(self)));
                }
                (F2op(uop0), F2op(uop1)) => {
                    out = F2op(F2op::ADD(uop0.into_icv(self), uop1.into_icv(self)));
                }
                (Fop(fop0), F3op(uop1)) => {
                    out = F3op(F3op::ADD(fop0.into_icv(self), uop1.into_icv(self)));
                }
                (F3op(uop0), F3op(uop1)) => {
                    out = F3op(F3op::ADD(uop0.into_icv(self), uop1.into_icv(self)));
                }
                (l, r) => {
                    return Err(Error::InvalidType(
                        "invalid operands type for '+' operator".into(),
                    ))
                }
            }
        }

        match (const_out, out) {
            (Fop(Fop::CONST(0.0)), op1 @ Fop(_)) => Ok(op1),
            (Fop(fop0), Fop(fop1)) => Ok(Fop(Fop::ADD(fop0.into_icv(self), fop1.into_icv(self)))),
            (F2op(F2op::CONST([0.0, 0.0])), op1 @ F2op(_)) => Ok(op1),
            (op0 @ (Fop(_) | F2op(_)), op1 @ (Fop(_) | F2op(_))) => {
                let l = op0.into_icv(self).try_into().unwrap();
                let r = op1.into_icv(self).try_into().unwrap();
                Ok(F2op(F2op::ADD(l, r)))
            }
            (F3op(F3op::CONST([0.0, 0.0, 0.0])), op1 @ F3op(_)) => Ok(op1),
            (op0 @ (Fop(_) | F3op(_)), op1 @ (Fop(_) | F3op(_))) => {
                let l = op0.into_icv(self).try_into().unwrap();
                let r = op1.into_icv(self).try_into().unwrap();
                Ok(F3op(F3op::ADD(l, r)))
            }
            _ => Err(Error::Unreachable),
        }
    }

    #[inline]
    fn push_add_leafs(&mut self, ops: &mut Vec<OP>, op: OP) {
        match op {
            Fop(Fop::ADD(l, r)) => {
                self.push_f_add_leaf(ops, r);
                self.push_f_add_leaf(ops, l);
            }
            F2op(F2op::ADD(l, r)) => {
                self.push_f2_add_leaf(ops, r);
                self.push_f2_add_leaf(ops, l);
            }
            F3op(F3op::ADD(l, r)) => {
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
            F::CONST(c) => ops.push(Fop(Fop::CONST(c))),
            F::VAR(i) => ops.push(Fop(Fop::VAR(i))),
        };
    }
    fn push_f2_add_leaf(&mut self, ops: &mut Vec<OP>, f2: F2) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match f2 {
            F2::I(_) => {
                let op = self.pop();
                self.push_add_leafs(ops, op);
            }

            F2::CONST(c) => ops.push(F2op(F2op::CONST(c))),
            F2::VAR(i) => ops.push(F2op(F2op::VAR(i))),
            F2::F(f) => match f {
                F::I(_) => {
                    let op = self.pop();
                    self.push_add_leafs(ops, op);
                }
                F::CONST(c) => ops.push(Fop(Fop::CONST(c))),
                F::VAR(i) => ops.push(Fop(Fop::VAR(i))),
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

            F3::CONST(c) => ops.push(F3op(F3op::CONST(c))),
            F3::VAR(i) => ops.push(F3op(F3op::VAR(i))),
            F3::F(f) => match f {
                F::I(_) => {
                    let op = self.pop();
                    self.push_add_leafs(ops, op);
                }
                F::CONST(c) => ops.push(Fop(Fop::CONST(c))),
                F::VAR(i) => ops.push(Fop(Fop::VAR(i))),
            },
        };
    }

    #[inline]
    fn push_mul_leafs(&mut self, ops: &mut Vec<OP>, op: OP) {
        match op {
            Fop(Fop::MUL(l, r)) => {
                self.push_f_mul_leaf(ops, r);
                self.push_f_mul_leaf(ops, l);
            }
            F2op(F2op::MUL(l, r)) => {
                self.push_f2_mul_leaf(ops, r);
                self.push_f2_mul_leaf(ops, l);
            }
            F3op(F3op::MUL(l, r)) => {
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
            F::CONST(c) => ops.push(Fop(Fop::CONST(c))),
            F::VAR(i) => ops.push(Fop(Fop::VAR(i))),
        };
    }

    fn push_f2_mul_leaf(&mut self, ops: &mut Vec<OP>, f2: F2) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match f2 {
            F2::I(_) => {
                let op = self.pop();
                self.push_mul_leafs(ops, op);
            }

            F2::CONST(c) => ops.push(F2op(F2op::CONST(c))),
            F2::VAR(i) => ops.push(F2op(F2op::VAR(i))),
            F2::F(f) => match f {
                F::I(_) => {
                    let op = self.pop();
                    self.push_mul_leafs(ops, op);
                }
                F::CONST(c) => ops.push(Fop(Fop::CONST(c))),
                F::VAR(i) => ops.push(Fop(Fop::VAR(i))),
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

            F3::CONST(c) => ops.push(F3op(F3op::CONST(c))),
            F3::VAR(i) => ops.push(F3op(F3op::VAR(i))),
            F3::F(f) => match f {
                F::I(_) => {
                    let op = self.pop();
                    self.push_mul_leafs(ops, op);
                }
                F::CONST(c) => ops.push(Fop(Fop::CONST(c))),
                F::VAR(i) => ops.push(Fop(Fop::VAR(i))),
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
                let l = out.into_icv(ex).convert_bool();
                let r = op.into_icv(ex).convert_bool();

                out = match (_op, l, r) {
                    (EQ, F(F::CONST(l)), F(F::CONST(r))) => Bop(Bop::CONST(l == r)),
                    (EQ, F(l), F(r)) => Bop(Bop::EQ(l, r)),
                    (EQ, l @ (F(_) | F2(_)), r @ (F(_) | F2(_))) => {
                        let l = l.try_into().unwrap();
                        let r = r.try_into().unwrap();
                        match (l, r) {
                            (F2::CONST(l), F2::CONST(r)) => Bop(Bop::CONST(l == r)),
                            _ => Bop(Bop::EQ2(l, r)),
                        }
                    }
                    (EQ, l @ (F(_) | F3(_)), r @ (F(_) | F3(_))) => {
                        let l = l.try_into().unwrap();
                        let r = r.try_into().unwrap();
                        match (l, r) {
                            (F3::CONST(l), F3::CONST(r)) => Bop(Bop::CONST(l == r)),
                            _ => Bop(Bop::EQ3(l, r)),
                        }
                    }

                    (NE, F(F::CONST(l)), F(F::CONST(r))) => Bop(Bop::CONST(l != r)),
                    (NE, F(l), F(r)) => Bop(Bop::NE(l, r)),
                    (NE, l @ (F(_) | F2(_)), r @ (F(_) | F2(_))) => {
                        let l = l.try_into().unwrap();
                        let r = r.try_into().unwrap();
                        match (l, r) {
                            (F2::CONST(l), F2::CONST(r)) => Bop(Bop::CONST(l != r)),
                            _ => Bop(Bop::NE2(l, r)),
                        }
                    }
                    (NE, l @ (F(_) | F3(_)), r @ (F(_) | F3(_))) => {
                        let l = l.try_into().unwrap();
                        let r = r.try_into().unwrap();
                        match (l, r) {
                            (F3::CONST(l), F3::CONST(r)) => Bop(Bop::CONST(l != r)),
                            _ => Bop(Bop::NE3(l, r)),
                        }
                    }

                    (LT, F(F::CONST(l)), F(F::CONST(r))) => Bop(Bop::CONST(l < r)),
                    (LT, F(l), F(r)) => Bop(Bop::LT(l, r)),

                    (GT, F(F::CONST(l)), F(F::CONST(r))) => Bop(Bop::CONST(l > r)),
                    (GT, F(l), F(r)) => Bop(Bop::GT(l, r)),

                    (LE, F(F::CONST(l)), F(F::CONST(r))) => Bop(Bop::CONST(l <= r)),
                    (LE, F(l), F(r)) => Bop(Bop::LE(l, r)),

                    (GE, F(F::CONST(l)), F(F::CONST(r))) => Bop(Bop::CONST(l >= r)),
                    (GE, F(l), F(r)) => Bop(Bop::GE(l, r)),

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
                let mut out = Bop(Bop::CONST(false));
                let mut out_set = false;
                for xs in xss.iter() {
                    let op = xs.compile(ast, ex)?;
                    out = if out_set {
                        let l = out.into_icv(ex).try_into().map_err(|_| {
                            Error::InvalidType("Invalid operands type for '||' operator".into())
                        })?;
                        let r = op.into_icv(ex).try_into().map_err(|_| {
                            Error::InvalidType("Invalid operands type for '||' operator".into())
                        })?;
                        match (l, r) {
                            (B::CONST(l), B::CONST(r)) => Bop(Bop::CONST(l || r)),
                            _ => Bop(Bop::OR(l, r)),
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
                let mut out = Bop(Bop::CONST(true));
                let mut out_set = false;
                for xs in xss.iter() {
                    let op = xs.compile(ast, ex)?;
                    out = if out_set {
                        let l = out.into_icv(ex).try_into().map_err(|_| {
                            Error::InvalidType("invalid operands type for '&&' operator".into())
                        })?;
                        let r = op.into_icv(ex).try_into().map_err(|_| {
                            Error::InvalidType("invalid operands type for '&&' operator".into())
                        })?;
                        match (l, r) {
                            (B::CONST(l), B::CONST(r)) => Bop(Bop::CONST(l && r)),
                            _ => Bop(Bop::AND(l, r)),
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
                let mut out = Fop(Fop::CONST(0.0));
                let mut out_set = false;
                for xs in xss.iter() {
                    let op = xs.compile(ast, ex)?;
                    out = if out_set {
                        let l = out.into_icv(ex);
                        let r = op.into_icv(ex);
                        compile_op!(::REM(l, r), Float::rem)
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
                let mut out = Fop(Fop::CONST(0.0));
                let mut out_set = false;
                // Right-to-Left Associativity
                for xs in xss.into_iter().rev() {
                    let op = xs.compile(ast, ex)?;
                    out = if out_set {
                        let l = op.into_icv(ex);
                        let r = out.into_icv(ex);
                        compile_op!(::POW(l, r), Float::pow)
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
            Const(c) => Ok(Fop(Fop::CONST(*c))),
            Var(name) => {
                if let Some(icv) = ex.locals.get(name) {
                    Ok(icv.clone().into())
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
                    let cond: B = cond.into_icv(ex).try_into()?;
                    let then = then.compile(ast, ex)?;
                    let els = els.compile(ast, ex)?;

                    match (cond, then, els) {
                        (B::CONST(false), _, els) => Ok(els),
                        (B::CONST(_), then, _) => Ok(then),
                        (cond, then, els) => match then.optype().max(els.optype()) {
                            Type::B => Ok(Bop(Bop::IF(
                                cond,
                                then.into_icv(ex).try_into().unwrap(),
                                els.into_icv(ex).try_into().unwrap(),
                            ))),
                            Type::F => Ok(Fop(Fop::IF(
                                cond,
                                then.into_icv(ex).try_into().unwrap(),
                                els.into_icv(ex).try_into().unwrap(),
                            ))),
                            Type::F2 => Ok(F2op(F2op::IF(
                                cond,
                                then.into_icv(ex).try_into().unwrap(),
                                els.into_icv(ex).try_into().unwrap(),
                            ))),
                            Type::F3 => Ok(F3op(F3op::IF(
                                cond,
                                then.into_icv(ex).try_into()?,
                                els.into_icv(ex).try_into()?,
                            ))),
                        },
                    }
                } else {
                    let mut args = Vec::with_capacity(eargs.len());
                    for earg in eargs {
                        let op = earg.compile(ast, ex)?;
                        let icv = op.into_icv(ex);
                        args.push(icv);
                    }
                    let string = string.as_deref();
                    if let Some(op) = ex.module.dispatch_func(&name, string, &args) {
                        Ok(op)
                    } else {
                        builtins::dispatch_func(&name, string, &args)
                    }
                }
            }
            List(vals) => match &vals.as_slice() {
                &[ECV::Const(cx), ECV::Const(cy)] => Ok(F2op(F2op::CONST([*cx, *cy]))),
                &[ECV::Const(cx), ECV::Const(cy), ECV::Const(cz)] => {
                    Ok(F3op(F3op::CONST([*cx, *cy, *cz])))
                }
                &[x, y] => {
                    let x = x.compile(ast, ex)?.into_icv(ex).try_into()?;
                    let y = y.compile(ast, ex)?.into_icv(ex).try_into()?;
                    Ok(F2op(F2op::NEW([x, y])))
                }
                &[x, y, z] => {
                    let x = x.compile(ast, ex)?.into_icv(ex).try_into()?;
                    let y = y.compile(ast, ex)?.into_icv(ex).try_into()?;
                    let z = z.compile(ast, ex)?.into_icv(ex).try_into()?;
                    Ok(F3op(F3op::NEW([x, y, z])))
                }
                _ => Err(Error::InvalidSyntax(
                    "The vector must be 2 to 3 elements long".into(),
                )),
            },

            _ => Err(Error::Unreachable),
        }
    }
}

//
// trait OP: Compiler + Eval
