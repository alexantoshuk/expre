//! This module evaluates parsed `Expr`s and compiled `Instruction`s.
//!
//! Everything can be evaluated using the `.eval()` method, but compiled
//! `Instruction`s also have the option of using the `eval_compiled!()` macro
//! which is much faster for common cases.

use crate::compiler::OAST;
use crate::compiler::{Instruction, Instruction::*, ICV};
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
// #[macro_export]
// macro_rules! eval_compiled_ref {
//     ($evaler:ident, $oast_ref:expr, $ns_mut:expr) => {
//         if let IConst(c) = $evaler {
//             *c
//         } else {
//             #[cfg(feature = "unsafe-vars")]
//             {
//                 if let IUnsafeVar { ptr, .. } = $evaler {
//                     unsafe { **ptr }
//                 } else {
//                     $evaler.eval($oast_ref, $ns_mut)?
//                 }
//             }

//             #[cfg(not(feature = "unsafe-vars"))]
//             $evaler.eval($oast_ref, $ns_mut)?
//         }
//     };
//     ($evaler:expr, $oast_ref:expr, $ns_mut:expr) => {{
//         let evaler = $evaler;
//         eval_compiled_ref!(evaler, $oast_ref, $ns_mut)
//     }};
// }

macro_rules! eval_icv_ref {
    ($icv:ident, $oast_ref:ident, $ns_mut:expr) => {
        match $icv {
            ICV::IConst(c) => *c,
            ICV::IVar(name) => match $ns_mut.lookup(name, Vec::new()) {
                Some(f) => f,
                None => return Err(Error::Undefined(name.to_string())),
            },
            ICV::I(i) => {
                let instr_ref = $oast_ref.get(*i);

                #[cfg(feature = "unsafe-vars")]
                {
                    if let crate::IUnsafeVar { ptr, .. } = instr_ref {
                        unsafe { **ptr }
                    } else {
                        instr_ref.eval($oast_ref, $ns_mut)?
                    }
                }

                #[cfg(not(feature = "unsafe-vars"))]
                instr_ref.eval($oast_ref, $ns_mut)?
            }
        }
    };
}

macro_rules! eval_var {
    ($ns:ident, $name:ident, $args:expr) => {
        match $ns.lookup($name, $args) {
            Some(f) => Ok(f),
            None => Err(Error::Undefined($name.to_string())),
        }
    };
}

macro_rules! var_names {
    ($icv:ident, $oast_ref:expr, $dst:expr) => {
        match $icv {
            ICV::I(i) => {
                $oast_ref.get(*i)._var_names($oast_ref, $dst);
            }
            ICV::IVar(s) => {
                $dst.insert(s.clone());
            }
            _ => {}
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
                    var_names!(ic, oast, dst);
                }
            }

            IFunc_1F(_, ii) => {
                var_names!(ii, oast, dst);
            }

            IFunc_2F(_, ic0, ic1) => {
                var_names!(ic0, oast, dst);
                var_names!(ic1, oast, dst);
            }

            IFunc_1S_NF(_, _, nic) => {
                for ic in nic {
                    var_names!(ic, oast, dst);
                }
            }

            IConst(_) => (),

            INeg(ii) | INot(ii) | IInv(ii) => var_names!(ii, oast, dst),

            ILT(lic, ric)
            | ILTE(lic, ric)
            | IEQ(lic, ric)
            | INE(lic, ric)
            | IGTE(lic, ric)
            | IGT(lic, ric)
            | IMod(lic, ric)
            | IExp(lic, ric) => {
                var_names!(lic, oast, dst);
                var_names!(ric, oast, dst);
            }

            IAdd(li, ric)
            | IMul(li, ric)
            | IOR(li, ric)
            | IAND(li, ric)
            | IMin(li, ric)
            | IMax(li, ric) => {
                var_names!(li, oast, dst);
                var_names!(ric, oast, dst);
            }
        }
    }
    #[inline]
    fn eval(&self, oast: &OAST, ns: &mut impl EvalNamespace) -> Result<f64, Error> {
        match self {
            // I have manually ordered these match arms in a way that I feel should deliver good performance.
            // (I don't think this ordering actually affects the generated code, though.)
            IMul(li, ric) => Ok(eval_icv_ref!(li, oast, ns) * eval_icv_ref!(ric, oast, ns)),
            IAdd(li, ric) => Ok(eval_icv_ref!(li, oast, ns) + eval_icv_ref!(ric, oast, ns)),

            IExp(base, power) => {
                Ok(eval_icv_ref!(base, oast, ns).powf(eval_icv_ref!(power, oast, ns)))
            }

            INeg(i) => Ok(-eval_icv_ref!(i, oast, ns)),
            IMod(dividend, divisor) => {
                Ok(eval_icv_ref!(dividend, oast, ns) % eval_icv_ref!(divisor, oast, ns))
            }
            IInv(i) => Ok(1.0 / eval_icv_ref!(i, oast, ns)),

            IVar(name) => eval_var!(ns, name, Vec::new()),

            IFunc_1F(f, i) => {
                // let v = eval_compiled_ref!(oast.get(*i), oast, ns);
                let v = eval_icv_ref!(i, oast, ns);
                Ok(f(v))
            }

            IFunc_2F(f, ric0, ric1) => {
                let v0 = eval_icv_ref!(ric0, oast, ns);
                let v1 = eval_icv_ref!(ric1, oast, ns);
                Ok(f(v0, v1))
            }

            IFunc_1S_NF(f, s, nic) => {
                let mut args = Vec::with_capacity(nic.len());
                for ic in nic {
                    args.push(eval_icv_ref!(ic, oast, ns));
                }
                Ok(f(&s, args))
            }

            // IFunc(name, ics) => {
            //     let mut args = Vec::with_capacity(ics.len());
            //     for ic in ics {
            //         args.push(eval_icv_ref!(ic, oast, ns));
            //     }
            //     eval_var!(ns, name, args)
            // }
            IFunc(name, _, ics) => {
                let mut args = Vec::with_capacity(ics.len());
                for ic in ics {
                    args.push(eval_icv_ref!(ic, oast, ns));
                }
                eval_var!(ns, name, args)
            }

            IMin(li, ric) => {
                let left = eval_icv_ref!(li, oast, ns);
                let right = eval_icv_ref!(ric, oast, ns);
                Ok(left.min(right))
            }
            IMax(li, ric) => {
                let left = eval_icv_ref!(li, oast, ns);
                let right = eval_icv_ref!(ric, oast, ns);
                Ok(left.max(right))
            }

            IEQ(left, right) => Ok(f64_eq!(
                eval_icv_ref!(left, oast, ns),
                eval_icv_ref!(right, oast, ns)
            )
            .into()),
            INE(left, right) => Ok(f64_ne!(
                eval_icv_ref!(left, oast, ns),
                eval_icv_ref!(right, oast, ns)
            )
            .into()),
            ILT(left, right) => {
                Ok((eval_icv_ref!(left, oast, ns) < eval_icv_ref!(right, oast, ns)).into())
            }
            ILTE(left, right) => {
                Ok((eval_icv_ref!(left, oast, ns) <= eval_icv_ref!(right, oast, ns)).into())
            }
            IGTE(left, right) => {
                Ok((eval_icv_ref!(left, oast, ns) >= eval_icv_ref!(right, oast, ns)).into())
            }
            IGT(left, right) => {
                Ok((eval_icv_ref!(left, oast, ns) > eval_icv_ref!(right, oast, ns)).into())
            }

            INot(i) => Ok(f64_eq!(eval_icv_ref!(i, oast, ns), 0.0).into()),
            IAND(li, ric) => {
                let left = eval_icv_ref!(li, oast, ns);
                if f64_eq!(left, 0.0) {
                    Ok(left)
                } else {
                    Ok(eval_icv_ref!(ric, oast, ns))
                }
            }
            IOR(li, ric) => {
                let left = eval_icv_ref!(li, oast, ns);
                if f64_ne!(left, 0.0) {
                    Ok(left)
                } else {
                    Ok(eval_icv_ref!(ric, oast, ns))
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
