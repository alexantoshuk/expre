//! This module evaluates parsed `Expr`s and compiled `Instruction`s.
//!
//! Everything can be evaluated using the `.eval()` method, but compiled
//! `Instruction`s also have the option of using the `eval_compiled!()` macro
//! which is much faster for common cases.

use crate::compiler::{CExpr, Func, Instruction, Instruction::*, ICV};
use crate::context::Context;
use crate::error::Error;
use crate::module::*;
use std::fmt;

impl<M: Module> CExpr<M> {
    pub fn eval(&self) -> Result<f64, Error> {
        self.instrs.last().unwrap().eval(self)
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
}

impl<M: Module> Evaler<M> for ICV {
    #[inline]
    fn eval(&self, cexpr: &CExpr<M>) -> Result<f64, Error> {
        match self {
            ICV::IConst(c) => Ok(*c),
            ICV::IVar(ptr) => unsafe { Ok(**ptr) },
            ICV::I(i) => cexpr.get(*i).eval(cexpr),
        }
    }
}

/// You must `use` this trait so you can call `.eval()`.
pub trait Evaler<M: Module> {
    /// Evaluate this `Expr`/`Instruction` and return an `f64`.
    ///
    /// Returns a `fasteval::Error` if there are any problems, such as undefined variables.
    fn eval(&self, cexpr: &CExpr<M>) -> Result<f64, Error>;
}

impl<M: Module> Evaler<M> for Instruction {
    #[inline]
    fn eval(&self, cexpr: &CExpr<M>) -> Result<f64, Error> {
        match self {
            // I have manually ordered these match arms in a way that I feel should deliver good performance.
            // (I don't think this ordering actually affects the generated code, though.)s
            IMul(licv, ricv) => Ok(licv.eval(cexpr)? * ricv.eval(cexpr)?),
            IAdd(licv, ricv) => Ok(licv.eval(cexpr)? + ricv.eval(cexpr)?),
            IMod(licv, ricv) => Ok(licv.eval(cexpr)? % ricv.eval(cexpr)?),
            IExp(base, power) => Ok(base.eval(cexpr)?.powf(power.eval(cexpr)?)),
            INeg(icv) => Ok(-icv.eval(cexpr)?),
            IInv(icv) => Ok(1.0 / icv.eval(cexpr)?),

            IVar(ptr) => unsafe { Ok(**ptr) },

            IFunc(f) => match f {
                Func::F_F(f, icv0) => icv0.eval(cexpr).map(f),
                Func::FF_F(f, icv0, icv1) => Ok(f(icv0.eval(cexpr)?, icv1.eval(cexpr)?)),
                _ => unreachable!(),
            },

            IMin(licv, ricv) => {
                let l = licv.eval(cexpr)?;
                let r = ricv.eval(cexpr)?;
                Ok(l.min(r))
            }
            IMax(licv, ricv) => {
                let l = licv.eval(cexpr)?;
                let r = ricv.eval(cexpr)?;
                Ok(l.max(r))
            }

            IEQ(licv, ricv) => Ok(Float::float_eq(licv.eval(cexpr)?, ricv.eval(cexpr)?).into()),
            INE(licv, ricv) => Ok(Float::float_ne(licv.eval(cexpr)?, ricv.eval(cexpr)?).into()),
            ILT(licv, ricv) => Ok((licv.eval(cexpr)? < ricv.eval(cexpr)?).into()),
            ILTE(licv, ricv) => Ok((licv.eval(cexpr)? <= ricv.eval(cexpr)?).into()),
            IGTE(licv, ricv) => Ok((licv.eval(cexpr)? >= ricv.eval(cexpr)?).into()),
            IGT(licv, ricv) => Ok((licv.eval(cexpr)? > ricv.eval(cexpr)?).into()),

            INot(icv) => Ok(Float::float_eq(icv.eval(cexpr)?, 0.0).into()),

            IAnd(licv, ricv) => {
                let l = licv.eval(cexpr)?;
                if Float::float_eq(l, 0.0) {
                    Ok(l)
                } else {
                    Ok(ricv.eval(cexpr)?)
                }
            }
            IOr(licv, ricv) => {
                let l = licv.eval(cexpr)?;
                if Float::float_ne(l, 0.0) {
                    Ok(l)
                } else {
                    Ok(ricv.eval(cexpr)?)
                }
            }

            // Put these last because you should be using the eval_compiled*!() macros to eliminate function calls.
            IConst(c) => Ok(*c),
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
        let mut cexpr = CExpr::<Builtins>::new();

        let expr_str = "a=x+x+5;a*a";
        eprintln!("Test expr: '{}'\n", expr_str);

        println!("PARSE: {:?}", ast.parse(expr_str));
        println!("{:?}", ast);
        struct Data {
            x: f64,
            y: f64,
            z: f64,
            // w: UnsafeCell<f64>,
        }
        // {
        let mut data = Data {
            x: 10.0,
            y: 5.0,
            z: 3.0,
            // w: 4.0.into(),
        };

        cexpr.add_var("x".to_owned(), &data.x);
        cexpr.add_var("y".to_owned(), &data.y);
        cexpr.add_var("z".to_owned(), &data.z);
        // cexpr.add_var("w".to_owned(), &data.w);

        let ok = ast.compile(&mut cexpr);

        eprintln!("CEXPR: {:?}", ok);
        // data.x = 0.0;
        // }

        let v = cexpr.eval().unwrap();
        println!("{:?}", cexpr);
        assert_eq!(1.0, v);
    }
}
