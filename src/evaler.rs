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
    pub fn eval(&self, ns: &impl EvalNamespace) -> Result<f64, Error> {
        self.instrs.last().unwrap().eval(self, ns)
    }

    pub fn var_names(&self) -> BTreeSet<String> {
        self.instrs.last().unwrap().var_names(self)
    }

    fn _var_names(&self, icv: &ICV, dst: &mut BTreeSet<String>) {
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

    #[inline(always)]
    fn _eval(&self, icv: &ICV, ns: &impl EvalNamespace) -> Result<f64, Error> {
        match icv {
            ICV::IConst(c) => Ok(*c),
            ICV::IVar(name) => match ns.lookup(name, Vec::new()) {
                Some(f) => Ok(f),
                None => Err(Error::Undefined(name.to_string())),
            },
            ICV::I(i) => {
                let instr_ref = self.get(*i);
                instr_ref.eval(self, ns)
            }
        }
    }
}

/// You must `use` this trait so you can call `.eval()`.
pub trait Evaler: fmt::Debug {
    /// Evaluate this `Expr`/`Instruction` and return an `f64`.
    ///
    /// Returns a `fasteval::Error` if there are any problems, such as undefined variables.
    fn eval(&self, cexpr: &CExpr, ns: &impl EvalNamespace) -> Result<f64, Error>;

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
    fn eval(&self, cexpr: &CExpr, ns: &impl EvalNamespace) -> Result<f64, Error> {
        match self {
            // I have manually ordered these match arms in a way that I feel should deliver good performance.
            // (I don't think this ordering actually affects the generated code, though.)s
            IMul(licv, ricv) => Ok(cexpr._eval(licv, ns)? * cexpr._eval(ricv, ns)?),
            IAdd(licv, ricv) => Ok(cexpr._eval(licv, ns)? + cexpr._eval(ricv, ns)?),
            IMod(licv, ricv) => Ok(cexpr._eval(licv, ns)? % cexpr._eval(ricv, ns)?),
            IExp(base, power) => Ok(cexpr._eval(base, ns)?.powf(cexpr._eval(power, ns)?)),
            INeg(icv) => Ok(-cexpr._eval(icv, ns)?),
            IInv(icv) => Ok(1.0 / cexpr._eval(icv, ns)?),

            IVar(name) => ns
                .lookup(name, vec![])
                .ok_or_else(|| Error::Undefined(name.to_string())),

            IFunc_1F(f, icv) => {
                let v = cexpr._eval(icv, ns)?;
                Ok(f(v))
            }

            IFunc_2F(f, icv0, icv1) => {
                let v0 = cexpr._eval(icv0, ns)?;
                let v1 = cexpr._eval(icv1, ns)?;
                Ok(f(v0, v1))
            }

            IFunc_3F(f, icv0, icv1, icv2) => {
                let v0 = cexpr._eval(icv0, ns)?;
                let v1 = cexpr._eval(icv1, ns)?;
                let v2 = cexpr._eval(icv2, ns)?;
                Ok(f(v0, v1, v2))
            }

            IFunc_1S_NF(f, s, nicv) => {
                let mut args = Vec::with_capacity(nicv.len());
                for icv in nicv {
                    args.push(cexpr._eval(icv, ns)?);
                }
                Ok(f(&s, args))
            }

            IFunc(name, _, nicv) => {
                let mut args = Vec::with_capacity(nicv.len());
                for icv in nicv {
                    args.push(cexpr._eval(icv, ns)?);
                }
                ns.lookup(name, args)
                    .ok_or_else(|| Error::Undefined(name.to_string()))
            }

            IMin(licv, ricv) => {
                let l = cexpr._eval(licv, ns)?;
                let r = cexpr._eval(ricv, ns)?;
                Ok(l.min(r))
            }
            IMax(licv, ricv) => {
                let l = cexpr._eval(licv, ns)?;
                let r = cexpr._eval(ricv, ns)?;
                Ok(l.max(r))
            }

            IEQ(licv, ricv) => Ok(float_eq(cexpr._eval(licv, ns)?, cexpr._eval(ricv, ns)?).into()),
            INE(licv, ricv) => Ok(float_ne(cexpr._eval(licv, ns)?, cexpr._eval(ricv, ns)?).into()),
            ILT(licv, ricv) => Ok((cexpr._eval(licv, ns)? < cexpr._eval(ricv, ns)?).into()),
            ILTE(licv, ricv) => Ok((cexpr._eval(licv, ns)? <= cexpr._eval(ricv, ns)?).into()),
            IGTE(licv, ricv) => Ok((cexpr._eval(licv, ns)? >= cexpr._eval(ricv, ns)?).into()),
            IGT(licv, ricv) => Ok((cexpr._eval(licv, ns)? > cexpr._eval(ricv, ns)?).into()),

            INot(icv) => Ok(float_eq(cexpr._eval(icv, ns)?, 0.0).into()),

            IAnd(licv, ricv) => {
                let l = cexpr._eval(licv, ns)?;
                if float_eq(l, 0.0) {
                    Ok(l)
                } else {
                    Ok(cexpr._eval(ricv, ns)?)
                }
            }
            IOr(licv, ricv) => {
                let l = cexpr._eval(licv, ns)?;
                if float_ne(l, 0.0) {
                    Ok(l)
                } else {
                    Ok(cexpr._eval(ricv, ns)?)
                }
            }

            // Put these last because you should be using the eval_compiled*!() macros to eliminate function calls.
            IConst(c) => Ok(*c),
        }
    }
}
