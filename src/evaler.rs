//! This module evaluates parsed `Expr`s and compiled `Instruction`s.
//!
//! Everything can be evaluated using the `.eval()` method, but compiled
//! `Instruction`s also have the option of using the `eval_compiled!()` macro
//! which is much faster for common cases.

use crate::builtins::{float_eq, float_ne};
use crate::compiler::CExpr;
use crate::compiler::{Instruction, Instruction::*, ICV};
use crate::context::Context;
use crate::error::Error;
use std::collections::{btree_map::Entry, BTreeSet};
use std::fmt;

impl CExpr {
    pub fn eval(&self, ctx: &impl Context) -> Result<f64, Error> {
        self.instrs.last().unwrap().eval(self, ctx)
    }

    pub fn var_names(&self) -> BTreeSet<String> {
        self.instrs.last().unwrap().var_names(self)
    }

    fn _var_names(&self, icv: &ICV, dst: &mut BTreeSet<String>) {
        match icv {
            ICV::I(i, _) => {
                self.get(*i)._var_names(self, dst);
            }
            ICV::IVar(s) => {
                dst.insert(s.clone());
            }
            _ => {}
        }
    }

    #[inline(always)]
    fn _eval(&self, icv: &ICV, ctx: &impl Context) -> Result<f64, Error> {
        match icv {
            ICV::IConst(c) => Ok(*c),
            ICV::IVar(name) => match ctx.lookup(name, &[]) {
                Some(f) => Ok(f),
                None => Err(Error::Undefined(name.to_string())),
            },
            ICV::I(i, cache) => self._eval_ref(*i, *cache, ctx),
        }
    }

    #[inline(always)]
    fn _eval_ref(&self, i: usize, cache: bool, ctx: &impl Context) -> Result<f64, Error> {
        if cache {
            let entry = unsafe { &mut *self.cache.get() }.entry(i);
            match entry {
                Entry::Occupied(occupied) => {
                    // println!("Get :{:?} from cache", i);
                    Ok(*occupied.get())
                }
                Entry::Vacant(vacant) => {
                    let v = self.get(i).eval(self, ctx)?;
                    // println!("Write :{:?} to cache", i);
                    Ok(*vacant.insert(v))
                }
            }
        } else {
            self.get(i).eval(self, ctx)
        }
    }
}

/// You must `use` this trait so you can call `.eval()`.
pub trait Evaler: fmt::Debug {
    /// Evaluate this `Expr`/`Instruction` and return an `f64`.
    ///
    /// Returns a `fasteval::Error` if there are any problems, such as undefined variables.
    fn eval(&self, cexpr: &CExpr, ctx: &impl Context) -> Result<f64, Error>;

    /// Don't call this directly.  Use `var_names()` instead.
    ///
    /// This exists because of ternary short-circuits; they prevent us from
    /// getting a complete list of vars just by doing eval() with a clever
    /// callback.
    fn _var_names(&self, cexpr: &CExpr, dst: &mut BTreeSet<String>);

    /// Returns a list of variables and custom functions that are used by this `Expr`/`Instruction`.
    #[inline(always)]
    fn var_names(&self, cexpr: &CExpr) -> BTreeSet<String> {
        let mut set = BTreeSet::new();
        self._var_names(cexpr, &mut set);
        set
    }
}

impl Evaler for Instruction {
    #[inline(always)]
    fn _var_names(&self, cexpr: &CExpr, dst: &mut BTreeSet<String>) {
        match self {
            IVar(s) => {
                dst.insert(s.clone());
            }

            IFunc(name, _, nicv) => {
                dst.insert(name.clone());
                for icv in nicv {
                    cexpr._var_names(icv, dst);
                }
            }

            INeg(icv) | INot(icv) | IInv(icv) | IFunc_1F(_, icv) => {
                cexpr._var_names(icv, dst);
            }

            IFunc_2F(_, icv0, icv1) => {
                cexpr._var_names(icv0, dst);
                cexpr._var_names(icv1, dst);
            }

            IFunc_3F(_, icv0, icv1, icv2) => {
                cexpr._var_names(icv0, dst);
                cexpr._var_names(icv1, dst);
                cexpr._var_names(icv2, dst);
            }

            IFunc_1S_NF(_, _, nicv) => {
                for icv in nicv {
                    cexpr._var_names(icv, dst);
                }
            }

            ILT(licv, ricv)
            | ILTE(licv, ricv)
            | IEQ(licv, ricv)
            | INE(licv, ricv)
            | IGTE(licv, ricv)
            | IGT(licv, ricv)
            | IMod(licv, ricv)
            | IExp(licv, ricv)
            | IAdd(licv, ricv)
            | IMul(licv, ricv)
            | IOr(licv, ricv)
            | IAnd(licv, ricv)
            | IMin(licv, ricv)
            | IMax(licv, ricv) => {
                cexpr._var_names(licv, dst);
                cexpr._var_names(ricv, dst);
            }
            _ => (),
        }
    }
    #[inline]
    fn eval(&self, cexpr: &CExpr, ctx: &impl Context) -> Result<f64, Error> {
        match self {
            // I have manually ordered these match arms in a way that I feel should deliver good performance.
            // (I don't think this ordering actually affects the generated code, though.)s
            IMul(licv, ricv) => Ok(cexpr._eval(licv, ctx)? * cexpr._eval(ricv, ctx)?),
            IAdd(licv, ricv) => Ok(cexpr._eval(licv, ctx)? + cexpr._eval(ricv, ctx)?),
            IMod(licv, ricv) => Ok(cexpr._eval(licv, ctx)? % cexpr._eval(ricv, ctx)?),
            IExp(base, power) => Ok(cexpr._eval(base, ctx)?.powf(cexpr._eval(power, ctx)?)),
            INeg(icv) => Ok(-cexpr._eval(icv, ctx)?),
            IInv(icv) => Ok(1.0 / cexpr._eval(icv, ctx)?),

            IVar(name) => ctx
                .lookup(name, &[])
                .ok_or_else(|| Error::Undefined(name.to_string())),

            IFunc_1F(f, icv) => {
                let v = cexpr._eval(icv, ctx)?;
                Ok(f(v))
            }

            IFunc_2F(f, icv0, icv1) => {
                let v0 = cexpr._eval(icv0, ctx)?;
                let v1 = cexpr._eval(icv1, ctx)?;
                Ok(f(v0, v1))
            }

            IFunc_3F(f, icv0, icv1, icv2) => {
                let v0 = cexpr._eval(icv0, ctx)?;
                let v1 = cexpr._eval(icv1, ctx)?;
                let v2 = cexpr._eval(icv2, ctx)?;
                Ok(f(v0, v1, v2))
            }

            IFunc_1S_NF(f, s, nicv) => {
                let mut args = Vec::with_capacity(nicv.len());
                for icv in nicv {
                    args.push(cexpr._eval(icv, ctx)?);
                }
                Ok(f(&s, &args))
            }

            IFunc(name, _, nicv) => {
                let mut args = Vec::with_capacity(nicv.len());
                for icv in nicv {
                    args.push(cexpr._eval(icv, ctx)?);
                }
                ctx.lookup(name, &args)
                    .ok_or_else(|| Error::Undefined(name.to_string()))
            }

            IMin(licv, ricv) => {
                let l = cexpr._eval(licv, ctx)?;
                let r = cexpr._eval(ricv, ctx)?;
                Ok(l.min(r))
            }
            IMax(licv, ricv) => {
                let l = cexpr._eval(licv, ctx)?;
                let r = cexpr._eval(ricv, ctx)?;
                Ok(l.max(r))
            }

            IEQ(licv, ricv) => {
                Ok(float_eq(cexpr._eval(licv, ctx)?, cexpr._eval(ricv, ctx)?).into())
            }
            INE(licv, ricv) => {
                Ok(float_ne(cexpr._eval(licv, ctx)?, cexpr._eval(ricv, ctx)?).into())
            }
            ILT(licv, ricv) => Ok((cexpr._eval(licv, ctx)? < cexpr._eval(ricv, ctx)?).into()),
            ILTE(licv, ricv) => Ok((cexpr._eval(licv, ctx)? <= cexpr._eval(ricv, ctx)?).into()),
            IGTE(licv, ricv) => Ok((cexpr._eval(licv, ctx)? >= cexpr._eval(ricv, ctx)?).into()),
            IGT(licv, ricv) => Ok((cexpr._eval(licv, ctx)? > cexpr._eval(ricv, ctx)?).into()),

            INot(icv) => Ok(float_eq(cexpr._eval(icv, ctx)?, 0.0).into()),

            IAnd(licv, ricv) => {
                let l = cexpr._eval(licv, ctx)?;
                if float_eq(l, 0.0) {
                    Ok(l)
                } else {
                    Ok(cexpr._eval(ricv, ctx)?)
                }
            }
            IOr(licv, ricv) => {
                let l = cexpr._eval(licv, ctx)?;
                if float_ne(l, 0.0) {
                    Ok(l)
                } else {
                    Ok(cexpr._eval(ricv, ctx)?)
                }
            }

            // Put these last because you should be using the eval_compiled*!() macros to eliminate function calls.
            IConst(c) => Ok(*c),
            IRef(i, cache) => cexpr._eval_ref(*i, *cache, ctx),
            // _ => unreachable!(),
        }
    }
}
