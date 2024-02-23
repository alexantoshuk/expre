//! This module evaluates parsed `Expr`s and compiled `Instruction`s.
//!
//! Everything can be evaluated using the `.eval()` method, but compiled
//! `Instruction`s also have the option of using the `eval_compiled!()` macro
//! which is much faster for common cases.

use crate::builtins::{float_eq, float_ne};
use crate::compiler::CExpr;
use crate::compiler::{Instruction, Instruction::*, ICV};
use crate::error::Error;
use crate::evalns::EvalNamespace;
use std::collections::BTreeSet;
use std::fmt;

impl CExpr {
    pub fn eval(&self, ns: &mut impl EvalNamespace) -> Result<f64, Error> {
        self.instrs.last().unwrap().eval(self, ns)
    }

    #[inline(always)]
    fn eval_icv(&self, icv: &ICV, ns: &mut impl EvalNamespace) -> Result<f64, Error> {
        match icv {
            ICV::IConst(c) => Ok(*c),
            ICV::IVar(name) => match ns.lookup(name, Vec::new()) {
                Some(f) => Ok(f),
                None => Err(Error::Undefined(name.to_string())),
            },
            ICV::I(i) => {
                let instr_ref = self.get(*i);

                #[cfg(feature = "unsafe-vars")]
                {
                    if let crate::IUnsafeVar { ptr, .. } = instr_ref {
                        unsafe { **ptr }
                    } else {
                        instr_ref.eval(self, ns)?
                    }
                }

                #[cfg(not(feature = "unsafe-vars"))]
                instr_ref.eval(self, ns)
            }
        }
    }

    #[inline(always)]
    fn var_names(&self, icv: &ICV, dst: &mut BTreeSet<String>) {
        match icv {
            ICV::I(i) => {
                self.get(*i)._var_names(self, dst);
            }
            ICV::IVar(s) => {
                dst.insert(s.clone());
            }
            _ => {}
        }
    }
}

/// You must `use` this trait so you can call `.eval()`.
pub trait Evaler: fmt::Debug {
    /// Evaluate this `Expr`/`Instruction` and return an `f64`.
    ///
    /// Returns a `fasteval::Error` if there are any problems, such as undefined variables.
    fn eval(&self, cexpr: &CExpr, ns: &mut impl EvalNamespace) -> Result<f64, Error>;

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
            #[cfg(feature = "unsafe-vars")]
            IUnsafeVar { name, .. } => {
                dst.insert(name.clone());
            }

            IVar(s) => {
                dst.insert(s.clone());
            }

            IFunc(name, _, nic) => {
                dst.insert(name.clone());
                for ic in nic {
                    cexpr.var_names(ic, dst);
                }
            }

            IFunc_1F(_, ii) => {
                cexpr.var_names(ii, dst);
            }

            IFunc_2F(_, ic0, ic1) => {
                cexpr.var_names(ic0, dst);
                cexpr.var_names(ic1, dst);
            }

            IFunc_3F(_, ic0, ic1, ic2) => {
                cexpr.var_names(ic0, dst);
                cexpr.var_names(ic1, dst);
                cexpr.var_names(ic2, dst);
            }

            IFunc_1S_NF(_, _, nic) => {
                for ic in nic {
                    cexpr.var_names(ic, dst);
                }
            }

            IConst(_) => (),

            INeg(ii) | INot(ii) | IInv(ii) => cexpr.var_names(ii, dst),

            ILT(lic, ric)
            | ILTE(lic, ric)
            | IEQ(lic, ric)
            | INE(lic, ric)
            | IGTE(lic, ric)
            | IGT(lic, ric)
            | IMod(lic, ric)
            | IExp(lic, ric) => {
                cexpr.var_names(lic, dst);
                cexpr.var_names(ric, dst);
            }

            IAdd(li, ric)
            | IMul(li, ric)
            | IOR(li, ric)
            | IAND(li, ric)
            | IMin(li, ric)
            | IMax(li, ric) => {
                cexpr.var_names(li, dst);
                cexpr.var_names(ric, dst);
            }
        }
    }
    #[inline]
    fn eval(&self, cexpr: &CExpr, ns: &mut impl EvalNamespace) -> Result<f64, Error> {
        match self {
            // I have manually ordered these match arms in a way that I feel should deliver good performance.
            // (I don't think this ordering actually affects the generated code, though.)s
            IMul(li, ric) => Ok(cexpr.eval_icv(li, ns)? * cexpr.eval_icv(ric, ns)?),
            IAdd(li, ric) => Ok(cexpr.eval_icv(li, ns)? + cexpr.eval_icv(ric, ns)?),

            IExp(base, power) => Ok(cexpr.eval_icv(base, ns)?.powf(cexpr.eval_icv(power, ns)?)),

            INeg(i) => Ok(-cexpr.eval_icv(i, ns)?),
            IMod(dividend, divisor) => {
                Ok(cexpr.eval_icv(dividend, ns)? % cexpr.eval_icv(divisor, ns)?)
            }
            IInv(i) => Ok(1.0 / cexpr.eval_icv(i, ns)?),

            IVar(name) => ns
                .lookup(name, Vec::new())
                .ok_or_else(|| Error::Undefined(name.to_string())),

            IFunc_1F(f, i) => {
                let v = cexpr.eval_icv(i, ns)?;
                Ok(f(v))
            }

            IFunc_2F(f, ric0, ric1) => {
                let v0 = cexpr.eval_icv(ric0, ns)?;
                let v1 = cexpr.eval_icv(ric1, ns)?;
                Ok(f(v0, v1))
            }

            IFunc_3F(f, ric0, ric1, ric2) => {
                let v0 = cexpr.eval_icv(ric0, ns)?;
                let v1 = cexpr.eval_icv(ric1, ns)?;
                let v2 = cexpr.eval_icv(ric2, ns)?;
                Ok(f(v0, v1, v2))
            }

            IFunc_1S_NF(f, s, nic) => {
                let mut args = Vec::with_capacity(nic.len());
                for ic in nic {
                    args.push(cexpr.eval_icv(ic, ns)?);
                }
                Ok(f(&s, args))
            }

            IFunc(name, _, ics) => {
                let mut args = Vec::with_capacity(ics.len());
                for ic in ics {
                    args.push(cexpr.eval_icv(ic, ns)?);
                }
                ns.lookup(name, args)
                    .ok_or_else(|| Error::Undefined(name.to_string()))
            }

            IMin(li, ric) => {
                let left = cexpr.eval_icv(li, ns)?;
                let right = cexpr.eval_icv(ric, ns)?;
                Ok(left.min(right))
            }
            IMax(li, ric) => {
                let left = cexpr.eval_icv(li, ns)?;
                let right = cexpr.eval_icv(ric, ns)?;
                Ok(left.max(right))
            }

            IEQ(left, right) => {
                Ok(float_eq(cexpr.eval_icv(left, ns)?, cexpr.eval_icv(right, ns)?).into())
            }
            INE(left, right) => {
                Ok(float_ne(cexpr.eval_icv(left, ns)?, cexpr.eval_icv(right, ns)?).into())
            }
            ILT(left, right) => Ok((cexpr.eval_icv(left, ns)? < cexpr.eval_icv(right, ns)?).into()),
            ILTE(left, right) => {
                Ok((cexpr.eval_icv(left, ns)? <= cexpr.eval_icv(right, ns)?).into())
            }
            IGTE(left, right) => {
                Ok((cexpr.eval_icv(left, ns)? >= cexpr.eval_icv(right, ns)?).into())
            }
            IGT(left, right) => Ok((cexpr.eval_icv(left, ns)? > cexpr.eval_icv(right, ns)?).into()),

            INot(i) => Ok(float_eq(cexpr.eval_icv(i, ns)?, 0.0).into()),
            IAND(li, ric) => {
                let left = cexpr.eval_icv(li, ns)?;
                if float_eq(left, 0.0) {
                    Ok(left)
                } else {
                    Ok(cexpr.eval_icv(ric, ns)?)
                }
            }
            IOR(li, ric) => {
                let left = cexpr.eval_icv(li, ns)?;
                if float_ne(left, 0.0) {
                    Ok(left)
                } else {
                    Ok(cexpr.eval_icv(ric, ns)?)
                }
            }

            // Put these last because you should be using the eval_compiled*!() macros to eliminate function calls.
            IConst(c) => Ok(*c),
            #[cfg(feature = "unsafe-vars")]
            IUnsafeVar { ptr, .. } => unsafe { Ok(**ptr) },
            // _ => unreachable!(),
        }
    }
}
