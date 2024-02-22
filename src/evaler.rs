//! This module evaluates parsed `Expr`s and compiled `Instruction`s.
//!
//! Everything can be evaluated using the `.eval()` method, but compiled
//! `Instruction`s also have the option of using the `eval_compiled!()` macro
//! which is much faster for common cases.

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
}

/// The same as `evaler_ref.eval(&cexpr, &mut ns)`, but more efficient for common cases.
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
//     ($evaler:ident, $cexpr_ref:expr, $ns_mut:expr) => {
//         if let IConst(c) = $evaler {
//             *c
//         } else {
//             #[cfg(feature = "unsafe-vars")]
//             {
//                 if let IUnsafeVar { ptr, .. } = $evaler {
//                     unsafe { **ptr }
//                 } else {
//                     $evaler.eval($cexpr_ref, $ns_mut)?
//                 }
//             }

//             #[cfg(not(feature = "unsafe-vars"))]
//             $evaler.eval($cexpr_ref, $ns_mut)?
//         }
//     };
//     ($evaler:expr, $cexpr_ref:expr, $ns_mut:expr) => {{
//         let evaler = $evaler;
//         eval_compiled_ref!(evaler, $cexpr_ref, $ns_mut)
//     }};
// }

macro_rules! eval_icv_ref {
    ($icv:ident, $cexpr_ref:ident, $ns_mut:expr) => {
        match $icv {
            ICV::IConst(c) => *c,
            ICV::IVar(name) => match $ns_mut.lookup(name, Vec::new()) {
                Some(f) => f,
                None => return Err(Error::Undefined(name.to_string())),
            },
            ICV::I(i) => {
                let instr_ref = $cexpr_ref.get(*i);

                #[cfg(feature = "unsafe-vars")]
                {
                    if let crate::IUnsafeVar { ptr, .. } = instr_ref {
                        unsafe { **ptr }
                    } else {
                        instr_ref.eval($cexpr_ref, $ns_mut)?
                    }
                }

                #[cfg(not(feature = "unsafe-vars"))]
                instr_ref.eval($cexpr_ref, $ns_mut)?
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
    ($icv:ident, $cexpr_ref:expr, $dst:expr) => {
        match $icv {
            ICV::I(i) => {
                $cexpr_ref.get(*i)._var_names($cexpr_ref, $dst);
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
                    var_names!(ic, cexpr, dst);
                }
            }

            IFunc_1F(_, ii) => {
                var_names!(ii, cexpr, dst);
            }

            IFunc_2F(_, ic0, ic1) => {
                var_names!(ic0, cexpr, dst);
                var_names!(ic1, cexpr, dst);
            }

            IFunc_3F(_, ic0, ic1, ic2) => {
                var_names!(ic0, cexpr, dst);
                var_names!(ic1, cexpr, dst);
                var_names!(ic2, cexpr, dst);
            }

            IFunc_1S_NF(_, _, nic) => {
                for ic in nic {
                    var_names!(ic, cexpr, dst);
                }
            }

            IConst(_) => (),

            INeg(ii) | INot(ii) | IInv(ii) => var_names!(ii, cexpr, dst),

            ILT(lic, ric)
            | ILTE(lic, ric)
            | IEQ(lic, ric)
            | INE(lic, ric)
            | IGTE(lic, ric)
            | IGT(lic, ric)
            | IMod(lic, ric)
            | IExp(lic, ric) => {
                var_names!(lic, cexpr, dst);
                var_names!(ric, cexpr, dst);
            }

            IAdd(li, ric)
            | IMul(li, ric)
            | IOR(li, ric)
            | IAND(li, ric)
            | IMin(li, ric)
            | IMax(li, ric) => {
                var_names!(li, cexpr, dst);
                var_names!(ric, cexpr, dst);
            }
        }
    }
    #[inline]
    fn eval(&self, cexpr: &CExpr, ns: &mut impl EvalNamespace) -> Result<f64, Error> {
        match self {
            // I have manually ordered these match arms in a way that I feel should deliver good performance.
            // (I don't think this ordering actually affects the generated code, though.)
            IMul(li, ric) => Ok(eval_icv_ref!(li, cexpr, ns) * eval_icv_ref!(ric, cexpr, ns)),
            IAdd(li, ric) => Ok(eval_icv_ref!(li, cexpr, ns) + eval_icv_ref!(ric, cexpr, ns)),

            IExp(base, power) => {
                Ok(eval_icv_ref!(base, cexpr, ns).powf(eval_icv_ref!(power, cexpr, ns)))
            }

            INeg(i) => Ok(-eval_icv_ref!(i, cexpr, ns)),
            IMod(dividend, divisor) => {
                Ok(eval_icv_ref!(dividend, cexpr, ns) % eval_icv_ref!(divisor, cexpr, ns))
            }
            IInv(i) => Ok(1.0 / eval_icv_ref!(i, cexpr, ns)),

            IVar(name) => eval_var!(ns, name, Vec::new()),

            IFunc_1F(f, i) => {
                // let v = eval_compiled_ref!(cexpr.get(*i), cexpr, ns);
                let v = eval_icv_ref!(i, cexpr, ns);
                Ok(f(v))
            }

            IFunc_2F(f, ric0, ric1) => {
                let v0 = eval_icv_ref!(ric0, cexpr, ns);
                let v1 = eval_icv_ref!(ric1, cexpr, ns);
                Ok(f(v0, v1))
            }

            IFunc_3F(f, ric0, ric1, ric2) => {
                let v0 = eval_icv_ref!(ric0, cexpr, ns);
                let v1 = eval_icv_ref!(ric1, cexpr, ns);
                let v2 = eval_icv_ref!(ric2, cexpr, ns);
                Ok(f(v0, v1, v2))
            }

            IFunc_1S_NF(f, s, nic) => {
                let mut args = Vec::with_capacity(nic.len());
                for ic in nic {
                    args.push(eval_icv_ref!(ic, cexpr, ns));
                }
                Ok(f(&s, args))
            }

            // IFunc(name, ics) => {
            //     let mut args = Vec::with_capacity(ics.len());
            //     for ic in ics {
            //         args.push(eval_icv_ref!(ic, cexpr, ns));
            //     }
            //     eval_var!(ns, name, args)
            // }
            IFunc(name, _, ics) => {
                let mut args = Vec::with_capacity(ics.len());
                for ic in ics {
                    args.push(eval_icv_ref!(ic, cexpr, ns));
                }
                eval_var!(ns, name, args)
            }

            IMin(li, ric) => {
                let left = eval_icv_ref!(li, cexpr, ns);
                let right = eval_icv_ref!(ric, cexpr, ns);
                Ok(left.min(right))
            }
            IMax(li, ric) => {
                let left = eval_icv_ref!(li, cexpr, ns);
                let right = eval_icv_ref!(ric, cexpr, ns);
                Ok(left.max(right))
            }

            IEQ(left, right) => Ok(f64_eq!(
                eval_icv_ref!(left, cexpr, ns),
                eval_icv_ref!(right, cexpr, ns)
            )
            .into()),
            INE(left, right) => Ok(f64_ne!(
                eval_icv_ref!(left, cexpr, ns),
                eval_icv_ref!(right, cexpr, ns)
            )
            .into()),
            ILT(left, right) => {
                Ok((eval_icv_ref!(left, cexpr, ns) < eval_icv_ref!(right, cexpr, ns)).into())
            }
            ILTE(left, right) => {
                Ok((eval_icv_ref!(left, cexpr, ns) <= eval_icv_ref!(right, cexpr, ns)).into())
            }
            IGTE(left, right) => {
                Ok((eval_icv_ref!(left, cexpr, ns) >= eval_icv_ref!(right, cexpr, ns)).into())
            }
            IGT(left, right) => {
                Ok((eval_icv_ref!(left, cexpr, ns) > eval_icv_ref!(right, cexpr, ns)).into())
            }

            INot(i) => Ok(f64_eq!(eval_icv_ref!(i, cexpr, ns), 0.0).into()),
            IAND(li, ric) => {
                let left = eval_icv_ref!(li, cexpr, ns);
                if f64_eq!(left, 0.0) {
                    Ok(left)
                } else {
                    Ok(eval_icv_ref!(ric, cexpr, ns))
                }
            }
            IOR(li, ric) => {
                let left = eval_icv_ref!(li, cexpr, ns);
                if f64_ne!(left, 0.0) {
                    Ok(left)
                } else {
                    Ok(eval_icv_ref!(ric, cexpr, ns))
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
