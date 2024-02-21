//! This module evaluates parsed `Expr`s and compiled `Instruction`s.
//!
//! Everything can be evaluated using the `.eval()` method, but compiled
//! `Instruction`s also have the option of using the `eval_compiled!()` macro
//! which is much faster for common cases.

use crate::compiler::OAST;
use crate::compiler::{Instruction, Instruction::*, I, IC};
use crate::error::Error;
use crate::evalns::EvalNamespace;
use std::collections::BTreeSet;
use std::fmt;

impl OAST {
    pub fn eval(&self, ns: &mut impl EvalNamespace) -> Result<f64, Error> {
        self.instrs.last().unwrap().eval(self, ns)
    }
}

/// The same as `evaler_ref.eval(&oast, &mut ns)`, but more efficient for common cases.
///
/// This macro is exactly the same as [`eval_compiled!()`](macro.eval_compiled.html) but
/// is useful when you hold a reference to the evaler, rather than having ownership of it.
///
/// Only use this for compiled expressions.  (If you use it for interpreted
/// expressions, it will work but will always be slower than calling `eval()` directly.)
///
/// This macro is able to eliminate function calls for constants and Unsafe Variables.
/// Since evaluation is a performance-critical operation, saving some function
/// calls actually makes a huge performance difference.
///
#[macro_export]
macro_rules! eval_compiled_ref {
    ($evaler:ident, $cslab_ref:expr, $ns_mut:expr) => {
        if let IConst(c) = $evaler {
            *c
        } else {
            #[cfg(feature = "unsafe-vars")]
            {
                if let IUnsafeVar { ptr, .. } = $evaler {
                    unsafe { **ptr }
                } else {
                    $evaler.eval($cslab_ref, $ns_mut)?
                }
            }

            #[cfg(not(feature = "unsafe-vars"))]
            $evaler.eval($cslab_ref, $ns_mut)?
        }
    };
    ($evaler:expr, $cslab_ref:expr, $ns_mut:expr) => {{
        let evaler = $evaler;
        eval_compiled_ref!(evaler, $cslab_ref, $ns_mut)
    }};
}

macro_rules! eval_ic_ref {
    ($ic:ident, $cslab_ref:ident, $ns_mut:expr) => {
        match $ic {
            IC::IConst(c) => *c,
            IC::I(i) => {
                let instr_ref = $cslab_ref.get(*i);

                #[cfg(feature = "unsafe-vars")]
                {
                    if let crate::IUnsafeVar { ptr, .. } = instr_ref {
                        unsafe { **ptr }
                    } else {
                        instr_ref.eval($cslab_ref, $ns_mut)?
                    }
                }

                #[cfg(not(feature = "unsafe-vars"))]
                instr_ref.eval($cslab_ref, $ns_mut)?
            }
        }
    };
}

/// You must `use` this trait so you can call `.eval()`.
pub trait Evaler: fmt::Debug {
    /// Evaluate this `Expr`/`Instruction` and return an `f64`.
    ///
    /// Returns a `fasteval::Error` if there are any problems, such as undefined variables.
    fn eval(&self, oast: &OAST, ns: &mut impl EvalNamespace) -> Result<f64, Error>;

    /// Don't call this directly.  Use `var_names()` instead.
    ///
    /// This exists because of ternary short-circuits; they prevent us from
    /// getting a complete list of vars just by doing eval() with a clever
    /// callback.
    fn _var_names(&self, oast: &OAST, dst: &mut BTreeSet<String>);

    /// Returns a list of variables and custom functions that are used by this `Expr`/`Instruction`.
    #[inline(always)]
    fn var_names(&self, oast: &OAST) -> BTreeSet<String> {
        let mut set = BTreeSet::new();
        self._var_names(oast, &mut set);
        set
    }
}

macro_rules! eval_var {
    ($ns:ident, $name:ident, $args:expr) => {
        match $ns.lookup($name, $args) {
            Some(f) => Ok(f),
            None => Err(Error::Undefined($name.to_string())),
        }
    };
}

impl Evaler for Instruction {
    #[inline(always)]
    fn _var_names(&self, oast: &OAST, dst: &mut BTreeSet<String>) {
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
                    if let IC::I(i) = ic {
                        oast.get(*i)._var_names(oast, dst);
                    }
                }
            }

            IFunc_1F(_, ii) => {
                oast.get(*ii)._var_names(oast, dst);
            }

            IFunc_2F(_, ic0, ic1) => {
                if let IC::I(i) = ic0 {
                    oast.get(*i)._var_names(oast, dst);
                }
                if let IC::I(i) = ic1 {
                    oast.get(*i)._var_names(oast, dst);
                }
            }

            IFunc_1S_NF(_, _, nic) => {
                for ic in nic {
                    if let IC::I(i) = ic {
                        oast.get(*i)._var_names(oast, dst);
                    }
                }
            }

            IConst(_) => (),

            INeg(ii) | INot(ii) | IInv(ii) => oast.get(*ii)._var_names(oast, dst),

            ILT(lic, ric)
            | ILTE(lic, ric)
            | IEQ(lic, ric)
            | INE(lic, ric)
            | IGTE(lic, ric)
            | IGT(lic, ric)
            | IMod(lic, ric)
            | IExp(lic, ric) => {
                if let IC::I(i) = lic {
                    oast.get(*i)._var_names(oast, dst);
                }
                if let IC::I(i) = ric {
                    oast.get(*i)._var_names(oast, dst);
                }
            }

            IAdd(li, ric)
            | IMul(li, ric)
            | IOR(li, ric)
            | IAND(li, ric)
            | IMin(li, ric)
            | IMax(li, ric) => {
                oast.get(*li)._var_names(oast, dst);
                if let IC::I(i) = ric {
                    oast.get(*i)._var_names(oast, dst);
                }
            } // IPrintFunc(_, args) => {
              //     for ic in args {
              //         if let IC::I(i) = ic {
              //             oast.get(*i)._var_names(oast, dst);
              //         }
              //     }
              // }
        }
    }
    #[inline(always)]
    fn eval(&self, oast: &OAST, ns: &mut impl EvalNamespace) -> Result<f64, Error> {
        match self {
            // I have manually ordered these match arms in a way that I feel should deliver good performance.
            // (I don't think this ordering actually affects the generated code, though.)
            IMul(li, ric) => {
                Ok(eval_compiled_ref!(oast.get(*li), oast, ns) * eval_ic_ref!(ric, oast, ns))
            }
            IAdd(li, ric) => {
                Ok(eval_compiled_ref!(oast.get(*li), oast, ns) + eval_ic_ref!(ric, oast, ns))
            }

            IExp(base, power) => {
                Ok(eval_ic_ref!(base, oast, ns).powf(eval_ic_ref!(power, oast, ns)))
            }

            INeg(i) => Ok(-eval_compiled_ref!(oast.get(*i), oast, ns)),
            IMod(dividend, divisor) => {
                Ok(eval_ic_ref!(dividend, oast, ns) % eval_ic_ref!(divisor, oast, ns))
            }
            IInv(i) => Ok(1.0 / eval_compiled_ref!(oast.get(*i), oast, ns)),

            IVar(name) => eval_var!(ns, name, Vec::new()),

            IFunc_1F(f, i) => {
                let v = eval_compiled_ref!(oast.get(*i), oast, ns);
                Ok(f(v))
            }

            IFunc_2F(f, ric0, ric1) => {
                let v0 = eval_ic_ref!(ric0, oast, ns);
                let v1 = eval_ic_ref!(ric1, oast, ns);
                Ok(f(v0, v1))
            }

            IFunc_1S_NF(f, s, nic) => {
                let mut args = Vec::with_capacity(nic.len());
                for ic in nic {
                    args.push(eval_ic_ref!(ic, oast, ns));
                }
                Ok(f(&s, args))
            }

            // IFunc(name, ics) => {
            //     let mut args = Vec::with_capacity(ics.len());
            //     for ic in ics {
            //         args.push(eval_ic_ref!(ic, oast, ns));
            //     }
            //     eval_var!(ns, name, args)
            // }
            IFunc(name, _, ics) => {
                let mut args = Vec::with_capacity(ics.len());
                for ic in ics {
                    args.push(eval_ic_ref!(ic, oast, ns));
                }
                eval_var!(ns, name, args)
            }

            IMin(li, ric) => {
                let left = eval_compiled_ref!(oast.get(*li), oast, ns);
                let right = eval_ic_ref!(ric, oast, ns);
                Ok(left.min(right))
            }
            IMax(li, ric) => {
                let left = eval_compiled_ref!(oast.get(*li), oast, ns);
                let right = eval_ic_ref!(ric, oast, ns);
                Ok(left.max(right))
            }

            IEQ(left, right) => {
                Ok(f64_eq!(eval_ic_ref!(left, oast, ns), eval_ic_ref!(right, oast, ns)).into())
            }
            INE(left, right) => {
                Ok(f64_ne!(eval_ic_ref!(left, oast, ns), eval_ic_ref!(right, oast, ns)).into())
            }
            ILT(left, right) => {
                Ok((eval_ic_ref!(left, oast, ns) < eval_ic_ref!(right, oast, ns)).into())
            }
            ILTE(left, right) => {
                Ok((eval_ic_ref!(left, oast, ns) <= eval_ic_ref!(right, oast, ns)).into())
            }
            IGTE(left, right) => {
                Ok((eval_ic_ref!(left, oast, ns) >= eval_ic_ref!(right, oast, ns)).into())
            }
            IGT(left, right) => {
                Ok((eval_ic_ref!(left, oast, ns) > eval_ic_ref!(right, oast, ns)).into())
            }

            INot(i) => Ok(f64_eq!(eval_compiled_ref!(oast.get(*i), oast, ns), 0.0).into()),
            IAND(li, ric) => {
                let left = eval_compiled_ref!(oast.get(*li), oast, ns);
                if f64_eq!(left, 0.0) {
                    Ok(left)
                } else {
                    Ok(eval_ic_ref!(ric, oast, ns))
                }
            }
            IOR(li, ric) => {
                let left = eval_compiled_ref!(oast.get(*li), oast, ns);
                if f64_ne!(left, 0.0) {
                    Ok(left)
                } else {
                    Ok(eval_ic_ref!(ric, oast, ns))
                }
            }
            // IPrintFunc(fstr, args) => {
            //     let mut v = Vec::with_capacity(args.len());
            //     let mut last = 0.0;
            //     for ic in args {
            //         last = eval_ic_ref!(ic, oast, ns);
            //         v.push(last);
            //     }
            //     eprintln!("{}", dyn_fmt::Arguments::new(fstr, &v));
            //     Ok(last)
            // }

            // Put these last because you should be using the eval_compiled*!() macros to eliminate function calls.
            IConst(c) => Ok(*c),
            #[cfg(feature = "unsafe-vars")]
            IUnsafeVar { ptr, .. } => unsafe { Ok(**ptr) },
            // _ => unreachable!(),
        }
    }
}
