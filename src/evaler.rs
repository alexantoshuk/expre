//! This module evaluates parsed `Expr`s and compiled `Instruction`s.
//!
//! Everything can be evaluated using the `.eval()` method, but compiled
//! `Instruction`s also have the option of using the `eval_compiled!()` macro
//! which is much faster for common cases.

use crate::compiler::CExpr;
use crate::compiler::{Instruction, Instruction::*, ICV};
use crate::context::Context;
use crate::error::Error;
use crate::module::*;
use indexmap::*;
use std::collections::{btree_map::Entry, BTreeSet};
use std::fmt;

impl CExpr {
    pub fn eval(&self, ctx: &[f64]) -> Result<f64, Error> {
        self.instrs.last().unwrap().eval(self, ctx)
    }

    // pub fn var_names(&self) -> BTreeSet<String> {
    //     self.instrs.last().unwrap().var_names(self)
    // }

    // fn _var_names(&self, icv: &ICV, dst: &mut BTreeSet<String>) {
    //     match icv {
    //         ICV::I(i) => {
    //             self.get(*i)._var_names(self, dst);
    //         }
    //         ICV::IVar(s) => {
    //             dst.insert(s.clone());
    //         }
    //         _ => {}
    //     }
    // }

    #[inline]
    fn _eval(&self, icv: &ICV, ctx: &[f64]) -> Result<f64, Error> {
        match icv {
            ICV::IConst(c) => Ok(*c),
            ICV::IVar(i) => match ctx.get(*i) {
                Some(f) => Ok(*f),
                None => Err(Error::Undefined("ERROR".to_string())),
            },
            ICV::I(i) => self.get(*i).eval(self, ctx),
        }
    }

    // #[inline]
    // fn _eval_ref(&self, i: usize, cache: bool, ctx: &impl Context) -> Result<f64, Error> {
    //     if cache {
    //         let entry = unsafe { &mut *self.cache.get() }.entry(i);
    //         match entry {
    //             Entry::Occupied(occupied) => {
    //                 // println!("Get :{:?} from cache", i);
    //                 Ok(*occupied.get())
    //             }
    //             Entry::Vacant(vacant) => {
    //                 let v = self.get(i).eval(self, ctx)?;
    //                 // println!("Write :{:?} to cache", i);
    //                 Ok(*vacant.insert(v))
    //             }
    //         }
    //     } else {
    //         self.get(i).eval(self, ctx)
    //     }
    // }
}

/// You must `use` this trait so you can call `.eval()`.
pub trait Evaler: fmt::Debug {
    /// Evaluate this `Expr`/`Instruction` and return an `f64`.
    ///
    /// Returns a `fasteval::Error` if there are any problems, such as undefined variables.
    fn eval(&self, cexpr: &CExpr, ctx: &[f64]) -> Result<f64, Error>;
}

impl Evaler for Instruction {
    #[inline]
    fn eval(&self, cexpr: &CExpr, ctx: &[f64]) -> Result<f64, Error> {
        match self {
            // I have manually ordered these match arms in a way that I feel should deliver good performance.
            // (I don't think this ordering actually affects the generated code, though.)s
            IMul(licv, ricv) => Ok(cexpr._eval(licv, ctx)? * cexpr._eval(ricv, ctx)?),
            IAdd(licv, ricv) => Ok(cexpr._eval(licv, ctx)? + cexpr._eval(ricv, ctx)?),
            IMod(licv, ricv) => Ok(cexpr._eval(licv, ctx)? % cexpr._eval(ricv, ctx)?),
            IExp(base, power) => Ok(cexpr._eval(base, ctx)?.powf(cexpr._eval(power, ctx)?)),
            INeg(icv) => Ok(-cexpr._eval(icv, ctx)?),
            IInv(icv) => Ok(1.0 / cexpr._eval(icv, ctx)?),

            IVar(i) => ctx
                .get(*i)
                .ok_or_else(|| Error::Undefined("ERROR".to_string()))
                .copied(),

            IFunc_F_F(f, icv) => {
                let v = cexpr._eval(icv, ctx)?;
                Ok(f(v))
            }

            IFunc_FF_F(f, icv0, icv1) => {
                let v0 = cexpr._eval(icv0, ctx)?;
                let v1 = cexpr._eval(icv1, ctx)?;
                Ok(f(v0, v1))
            }

            IFunc_FFF_F(f, icv0, icv1, icv2) => {
                let v0 = cexpr._eval(icv0, ctx)?;
                let v1 = cexpr._eval(icv1, ctx)?;
                let v2 = cexpr._eval(icv2, ctx)?;
                Ok(f(v0, v1, v2))
            }

            IFunc_FFFF_F(f, icv0, icv1, icv2, icv3) => {
                let v0 = cexpr._eval(icv0, ctx)?;
                let v1 = cexpr._eval(icv1, ctx)?;
                let v2 = cexpr._eval(icv2, ctx)?;
                let v3 = cexpr._eval(icv3, ctx)?;
                Ok(f(v0, v1, v2, v3))
            }

            IFunc_FFFFF_F(f, icv0, icv1, icv2, icv3, icv4) => {
                let v0 = cexpr._eval(icv0, ctx)?;
                let v1 = cexpr._eval(icv1, ctx)?;
                let v2 = cexpr._eval(icv2, ctx)?;
                let v3 = cexpr._eval(icv3, ctx)?;
                let v4 = cexpr._eval(icv4, ctx)?;
                Ok(f(v0, v1, v2, v3, v4))
            }

            IFunc_1S_NF(f, s, nicv) => {
                let mut args = Vec::with_capacity(nicv.len());
                for icv in nicv {
                    args.push(cexpr._eval(icv, ctx)?);
                }
                Ok(f(&s, &args))
            }

            IFunc_NF(f, nicv) => {
                let mut args = Vec::with_capacity(nicv.len());
                for icv in nicv {
                    args.push(cexpr._eval(icv, ctx)?);
                }
                Ok(f(&args))
            }

            IFunc_NS_NF(f, ns, nicv) => {
                let mut args = Vec::with_capacity(nicv.len());
                for icv in nicv {
                    args.push(cexpr._eval(icv, ctx)?);
                }

                let mut sargs = Vec::with_capacity(ns.len());
                for s in ns.iter() {
                    sargs.push(s.as_str());
                }
                Ok(f(&sargs, &args))
            }

            // IFunc(name, _, nicv) => {
            //     let mut args = Vec::with_capacity(nicv.len());
            //     for icv in nicv {
            //         args.push(cexpr._eval(icv, ctx)?);
            //     }
            //     ctx.lookup(name, &args)
            //         .ok_or_else(|| Error::Undefined(name.to_string()))
            // }
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
                Ok(Float::float_eq(cexpr._eval(licv, ctx)?, cexpr._eval(ricv, ctx)?).into())
            }
            INE(licv, ricv) => {
                Ok(Float::float_ne(cexpr._eval(licv, ctx)?, cexpr._eval(ricv, ctx)?).into())
            }
            ILT(licv, ricv) => Ok((cexpr._eval(licv, ctx)? < cexpr._eval(ricv, ctx)?).into()),
            ILTE(licv, ricv) => Ok((cexpr._eval(licv, ctx)? <= cexpr._eval(ricv, ctx)?).into()),
            IGTE(licv, ricv) => Ok((cexpr._eval(licv, ctx)? >= cexpr._eval(ricv, ctx)?).into()),
            IGT(licv, ricv) => Ok((cexpr._eval(licv, ctx)? > cexpr._eval(ricv, ctx)?).into()),

            INot(icv) => Ok(Float::float_eq(cexpr._eval(icv, ctx)?, 0.0).into()),

            IAnd(licv, ricv) => {
                let l = cexpr._eval(licv, ctx)?;
                if Float::float_eq(l, 0.0) {
                    Ok(l)
                } else {
                    Ok(cexpr._eval(ricv, ctx)?)
                }
            }
            IOr(licv, ricv) => {
                let l = cexpr._eval(licv, ctx)?;
                if Float::float_ne(l, 0.0) {
                    Ok(l)
                } else {
                    Ok(cexpr._eval(ricv, ctx)?)
                }
            }

            // Put these last because you should be using the eval_compiled*!() macros to eliminate function calls.
            IConst(c) => Ok(*c),
            // IRef(i, cache) => cexpr._eval_ref(*i, *cache, ctx),
            // _ => unimplemented!(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::Ast;

    #[test]
    fn test_eval() {
        let mut ast = Ast::new();
        let mut cexpr = CExpr::new();

        // let ctx = |name: &str, _: &[_]| match name {
        //     "x" => Some(10.0),
        //     "y" => Some(5.0),
        //     "z" => Some(3.0),
        //     "w" => Some(4.0),
        //     _ => None,
        // };

        let expr_str = "i=8;b=4+7+i; a=((1+5) -b+4 +x -x+x+5+b-i);a";
        eprintln!("Test expr: '{}'\n", expr_str);

        ast.parse(expr_str);
        cexpr.vars = IndexSet::from_iter(
            [
                "x".to_owned(),
                "y".to_owned(),
                "z".to_owned(),
                "w".to_owned(),
            ]
            .into_iter(),
        );
        let ctx = [10.0, 5.0, 3.0, 4.0];
        ast.compile(&mut cexpr);
        println!("{:?}", ast);
        let v = cexpr.eval(&ctx).unwrap();
        println!("{:?}", cexpr);
        assert_eq!(1.0, v);
    }
}
