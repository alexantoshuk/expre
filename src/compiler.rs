//! This module compiles parsed `Expr`s into an optimized Ast node called an `Instruction`.
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
//! * Variable-length `Expr`/`Value` Ast nodes are converted into constant-sized `Instruction` nodes.
//! * The `ICV` enumeration helps to eliminate expensive function calls.

use crate::error::Error;
use crate::module::*;
// pub use crate::parser::I;
use crate::parser::{
    self, Ast,
    BinaryOp::{self, *},
    Expr, ExprPair,
    UnaryOp::{self, *},
    Value::{self, *},
};

use crate::write_indexed_list;
use indexmap::IndexMap;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Debug};
use std::marker::PhantomData;
use std::mem;

/// An `Instruction` is an optimized Ast node resulting from compilation.
#[allow(non_camel_case_types)]
#[derive(Debug, PartialEq, Clone)]
pub enum Instruction {
    //---- Primitive Value Types:
    IConst(f64),
    IVar(*const f64),

    //---- Unary Ops:
    // Parentheses is a noop
    // Pos is a noop
    INeg(ICV),
    INot(ICV),
    IInv(ICV),

    //---- Binary Math Ops:
    IAdd(ICV, ICV),
    // A Sub(x) is converted to an Add(Neg(x)).
    IMul(ICV, ICV),
    // A Div(n,d) is converted to a Mul(n,Inv(d)).
    IMod(ICV, ICV),

    IExp(ICV, ICV),

    //---- Binary Comparison Ops:
    ILT(ICV, ICV),
    ILTE(ICV, ICV),
    IEQ(ICV, ICV),
    INE(ICV, ICV),
    IGTE(ICV, ICV),
    IGT(ICV, ICV),

    //---- Binary Logic Ops:
    IOr(ICV, ICV),
    IAnd(ICV, ICV),

    //---- Callables:
    // IFunc(String, Vec<String>, Vec<ICV>),
    // IFunc_F_F(fn(f64) -> f64, ICV),
    // IFunc_FF_F(fn(f64, f64) -> f64, ICV, ICV),
    // IFunc_FFF_F(fn(f64, f64, f64) -> f64, ICV, ICV, ICV),
    // IFunc_FFFF_F(fn(f64, f64, f64, f64) -> f64, ICV, ICV, ICV, ICV),
    // IFunc_FFFFF_F(fn(f64, f64, f64, f64, f64) -> f64, ICV, ICV, ICV, ICV, ICV),
    IFunc(Func),
    // IFunc_NF(fn(&[f64]) -> f64, Vec<ICV>),

    // IFunc_1S_NF(fn(&str, &[f64]) -> f64, String, Vec<ICV>),
    // IFunc_NS_NF(fn(&[&str], &[f64]) -> f64, Vec<String>, Vec<ICV>),
    IMin(ICV, ICV),
    IMax(ICV, ICV),
}

use Instruction::*;

/// This enumeration boosts performance because it eliminates expensive function calls and redirection for constant values and vars.
#[derive(PartialEq, Clone, Copy)]
pub enum ICV {
    I(usize),
    IConst(f64),
    IVar(*const f64),
}

impl Debug for ICV {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ICV::I(i) => write!(f, ":{:?}", i),
            ICV::IConst(v) => write!(f, "IConst({:?})", v),
            ICV::IVar(s) => write!(f, "IVar({:?})", s),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum Func {
    F_F(fn(f64) -> f64, ICV),
    FF_F(fn(f64, f64) -> f64, ICV, ICV),
    FFF_F(fn(f64, f64, f64) -> f64, ICV, ICV, ICV),
    FFFF_F(fn(f64, f64, f64, f64) -> f64, ICV, ICV, ICV, ICV),
    FFFFF_F(fn(f64, f64, f64, f64, f64) -> f64, ICV, ICV, ICV, ICV, ICV),
}

pub enum Type {
    Float, //F
    Vec2,  //U
    Vec3,  //V
           // Vec4, //P
}

impl From<Type> for usize {
    fn from(t: Type) -> Self {
        match t {
            Type::Float => 1,
            Type::Vec2 => 2,
            Type::Vec3 => 3,
        }
    }
}

impl Ast {
    pub fn compile<M: Module>(&self, cexpr: &mut CExpr<M>) -> Result<(), Error> {
        cexpr.compile(self)
    }
}

pub fn compile<M: Module>(ast: &Ast, cexpr: &mut CExpr<M>) -> Result<(), Error> {
    CExpr::compile(cexpr, ast)
}

/// You must `use` the `Compiler` trait before you can call `.compile()` on parsed `Expr`s.
pub trait Compiler<M: Module> {
    /// Turns a parsed `Expr` into a compiled `Instruction`.
    ///
    /// Cannot fail, unless you run out of memory.
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>) -> Result<Instruction, Error>;
}

/// `CExpr` is where `compile()` results are stored.
pub struct CExpr<M> {
    pub module: M,
    pub(crate) instrs: Vec<Instruction>,
}

impl<M: Module> CExpr<M> {
    pub fn new() -> Self {
        Self {
            module: Default::default(),
            instrs: Vec::new(),
        }
    }

    pub fn with_module(module: M) -> Self {
        Self {
            module,
            instrs: Vec::new(),
        }
    }

    pub fn add_var(&mut self, name: String, val: &f64) {
        self.module.add_var(name, val);
    }

    fn get_var(&self, name: &str) -> Option<*const f64> {
        self.module.get_var(name)
    }

    #[inline]
    pub fn compile(&mut self, ast: &Ast) -> Result<(), Error> {
        self.instrs.clear();

        let expr = ast.exprs.last().unwrap();
        let instr = expr.compile(ast, self)?;

        self.instrs.push(instr);
        Ok(())
    }

    #[inline]
    pub fn last(&self) -> Option<&Instruction> {
        self.instrs.last()
    }

    /// Returns a reference to the [`Instruction`](../compiler/enum.Instruction.html)
    /// located at `instr_i` within the `CExpr.instrs'.
    ///
    /// If `instr_i` is out-of-bounds, a reference to a default `Instruction` is returned.
    ///
    #[inline]
    pub fn get(&self, instr_i: usize) -> &Instruction {
        // unsafe{self.instrs.get_unchecked(instr_i)}
        self.instrs.get(instr_i).unwrap()
    }

    /// Appends an `Instruction` to `CExpr.instrs`.
    #[inline]
    pub fn push(&mut self, instr: Instruction) -> usize {
        let i = self.instrs.len();
        self.instrs.push(instr);
        i
    }

    /// Removes an `Instruction` from `CExpr.instrs` as efficiently as possible.
    #[inline]
    pub fn pop(&mut self) -> Instruction {
        self.instrs.pop().unwrap()
    }

    /// Clears all data from `CExpr.instrs`.
    #[inline]
    pub fn clear(&mut self) {
        self.instrs.clear();
    }

    #[inline]
    pub fn instr_to_icv(&mut self, instr: Instruction) -> ICV {
        match instr {
            IConst(c) => ICV::IConst(c),
            IVar(s) => ICV::IVar(s),
            _ => ICV::I(self.push(instr)),
        }
    }
}

impl<M> Debug for CExpr<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "CExpr[")?;
        write_indexed_list(f, &self.instrs)?;
        write!(f, "]")?;
        Ok(())
    }
}

impl<M: Module> CExpr<M> {
    #[inline]
    fn neg_wrap(&mut self, instr: Instruction) -> Instruction {
        match instr {
            IConst(c) => IConst(-c),
            INeg(_) => self.pop(),
            _ => INeg(self.instr_to_icv(instr)),
        }
    }

    #[inline]
    fn not_wrap(&mut self, instr: Instruction) -> Instruction {
        match instr {
            IConst(c) => IConst((Float::float_eq(c, 0.0)).into()),
            INot(_) => self.pop(),
            _ => INot(self.instr_to_icv(instr)),
        }
    }
    #[inline]
    fn inv_wrap(&mut self, instr: Instruction) -> Instruction {
        match instr {
            IConst(c) => IConst(1.0 / c),
            IInv(_) => self.pop(),
            _ => IInv(self.instr_to_icv(instr)),
        }
    }

    #[inline]
    fn compile_mul(&mut self, instrs: Vec<Instruction>) -> Instruction {
        let mut out = IConst(1.0);
        let mut out_set = false;
        let mut const_prod = 1.0;
        for instr in instrs {
            if let IConst(c) = instr {
                if c.is_nan() {
                    return instr;
                }
                const_prod *= c; // Floats don't overflow.
            } else {
                if out_set {
                    out = IMul(self.instr_to_icv(out), self.instr_to_icv(instr));
                } else {
                    out = instr;
                    out_set = true;
                }
            }
        }
        if Float::float_ne(const_prod, 1.0) {
            if out_set {
                out = IMul(self.instr_to_icv(out), ICV::IConst(const_prod));
            } else {
                out = IConst(const_prod);
            }
        }
        out
    }

    #[inline]
    fn compile_add(&mut self, instrs: Vec<Instruction>) -> Instruction {
        let mut out = IConst(0.0);
        let mut out_set = false;
        let mut const_sum = 0.0;
        for instr in instrs {
            if let IConst(c) = instr {
                if c.is_nan() {
                    return instr;
                }
                const_sum += c; // Floats don't overflow.
            } else {
                if out_set {
                    // println!("var: {:?}", instr);
                    out = IAdd(self.instr_to_icv(out), self.instr_to_icv(instr));
                } else {
                    out = instr;
                    out_set = true;
                }
            }
        }
        if Float::float_ne(const_sum, 0.0) {
            if out_set {
                out = IAdd(self.instr_to_icv(out), ICV::IConst(const_sum));
            } else {
                out = IConst(const_sum);
            }
        }
        out
    }

    // Can't inline recursive functions:
    fn push_mul_leaves(&mut self, instrs: &mut Vec<Instruction>, licv: ICV, ricv: ICV) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match ricv {
            ICV::I(..) => {
                let instr = self.pop();
                if let IMul(l, r) = instr {
                    self.push_mul_leaves(instrs, l, r);
                } else {
                    instrs.push(instr);
                }
            }
            ICV::IConst(c) => instrs.push(IConst(c)),
            ICV::IVar(s) => instrs.push(IVar(s)),
        };

        match licv {
            ICV::I(..) => {
                let instr = self.pop();
                if let IMul(l, r) = instr {
                    self.push_mul_leaves(instrs, l, r);
                } else {
                    instrs.push(instr);
                }
            }
            ICV::IConst(c) => instrs.push(IConst(c)),
            ICV::IVar(s) => instrs.push(IVar(s)),
        };
    }
    // Can't inline recursive functions:
    fn push_add_leaves(&mut self, instrs: &mut Vec<Instruction>, licv: ICV, ricv: ICV) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match ricv {
            ICV::I(..) => {
                let instr = self.pop();
                if let IAdd(l, r) = instr {
                    self.push_add_leaves(instrs, l, r);
                } else {
                    instrs.push(instr);
                }
            }

            ICV::IConst(c) => instrs.push(IConst(c)),
            ICV::IVar(c) => instrs.push(IVar(c)),
        };
        match licv {
            ICV::I(..) => {
                let instr = self.pop();
                if let IAdd(l, r) = instr {
                    self.push_add_leaves(instrs, l, r);
                } else {
                    instrs.push(instr);
                }
            }
            ICV::IConst(c) => instrs.push(IConst(c)),
            ICV::IVar(s) => instrs.push(IVar(s)),
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

impl<M: Module> Compiler<M> for ExprSlice<'_> {
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>) -> Result<Instruction, Error> {
        // Associative:  (2+3)+4 = 2+(3+4)
        // Commutative:  1+2 = 2+1
        //
        //          Only         Only
        // Neither  Associative  Commutative  Both
        // -------  -----------  -----------  ----
        // GTE      (none)       (none)       OR
        // LTE                                AND
        // GT                                 NE
        // LT                                 EQ
        // Minus (opt with neg & add)         Plus
        // Div (opt with inv & mul)           Mul
        // Mod
        // Exp

        // Find the lowest-priority BinaryOp:
        let mut lowest_op = match self.1.first() {
            Some(p0) => p0.0,
            None => return self.0.compile(ast, cexpr),
        };
        for exprpair in self.1.iter() {
            if exprpair.0 < lowest_op {
                lowest_op = exprpair.0
            }
        }

        // All comparisons have equal precedence:
        if lowest_op == EEQ
            || lowest_op == ENE
            || lowest_op == ELT
            || lowest_op == EGT
            || lowest_op == ELTE
            || lowest_op == EGTE
        {
            let mut ops = Vec::<&BinaryOp>::with_capacity(4);
            let mut xss = Vec::<ExprSlice>::with_capacity(ops.len() + 1);
            self.split_multi(&[EEQ, ENE, ELT, EGT, ELTE, EGTE], &mut xss, &mut ops);
            let mut out = xss.first().unwrap().compile(ast, cexpr)?;

            for (i, op) in ops.into_iter().enumerate() {
                let instr = xss.get(i + 1).unwrap().compile(ast, cexpr)?;

                if let IConst(l) = out {
                    if let IConst(r) = instr {
                        out = match op {
                            EEQ => IConst((Float::float_eq(l, r)).into()),
                            ENE => IConst((Float::float_ne(l, r)).into()),
                            ELT => IConst((l < r).into()),
                            EGT => IConst((l > r).into()),
                            ELTE => IConst((l <= r).into()),
                            EGTE => IConst((l >= r).into()),
                            _ => unreachable!(),
                        };
                        continue;
                    }
                }

                out = match op {
                    EEQ => IEQ(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr)),
                    ENE => INE(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr)),
                    ELT => ILT(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr)),
                    EGT => IGT(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr)),
                    ELTE => ILTE(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr)),
                    EGTE => IGTE(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr)),
                    _ => unreachable!(),
                };
            }
            return Ok(out);
        }

        match lowest_op {
            EOr => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EOr, &mut xss);
                let mut out = IConst(0.0);
                let mut out_set = false;
                for xs in xss.iter() {
                    let instr = xs.compile(ast, cexpr)?;
                    if out_set {
                        out = IOr(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr));
                    } else {
                        if let IConst(c) = instr {
                            if Float::float_ne(c, 0.0) {
                                return Ok(instr);
                            }
                            // out = instr;     // Skip this 0 value (mostly so I don't complicate my logic in 'if out_set' since I can assume that any set value is non-const).
                            // out_set = true;
                        } else {
                            out = instr;
                            out_set = true;
                        }
                    }
                }
                Ok(out)
            }

            EAnd => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EAnd, &mut xss);
                let mut out = IConst(1.0);
                let mut out_set = false;
                for xs in xss.iter() {
                    let instr = xs.compile(ast, cexpr)?;
                    if let IConst(c) = instr {
                        if Float::float_eq(c, 0.0) {
                            return Ok(instr);
                        }
                    }
                    if out_set {
                        if let IConst(_) = out {
                            // If we get here, we know that the const is non-zero.
                            out = instr;
                        } else {
                            out = IAnd(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr));
                        }
                    } else {
                        out = instr;
                        out_set = true;
                    }
                }
                Ok(out)
            }

            EAdd => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EAdd, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for xs in xss {
                    let instr = xs.compile(ast, cexpr)?;
                    if let IAdd(licv, ricv) = instr {
                        cexpr.push_add_leaves(&mut instrs, licv, ricv); // Flatten nested structures like "x - 1 + 2 - 3".
                    } else {
                        instrs.push(instr);
                    }
                }
                Ok(cexpr.compile_add(instrs))
            }

            ESub => {
                // Note: We don't need to push_add_leaves from here because Sub has a higher precedence than Add.

                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(ESub, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let instr = xs.compile(ast, cexpr)?;
                    if i == 0 {
                        instrs.push(instr);
                    } else {
                        instrs.push(cexpr.neg_wrap(instr));
                    }
                }
                Ok(cexpr.compile_add(instrs))
            }
            EMul => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EMul, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for xs in xss {
                    let instr = xs.compile(ast, cexpr)?;
                    if let IMul(licv, ricv) = instr {
                        cexpr.push_mul_leaves(&mut instrs, licv, ricv); // Flatten nested structures like "deg/360 * 2*pi()".
                    } else {
                        instrs.push(instr);
                    }
                }
                Ok(cexpr.compile_mul(instrs))
            }
            EDiv => {
                // Note: We don't need to push_mul_leaves from here because Div has a higher precedence than Mul.

                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EDiv, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let instr = xs.compile(ast, cexpr)?;
                    if i == 0 {
                        instrs.push(instr);
                    } else {
                        instrs.push(cexpr.inv_wrap(instr));
                    }
                }
                Ok(cexpr.compile_mul(instrs))
            }

            EMod => {
                let mut xss = Vec::<ExprSlice>::with_capacity(2);
                self.split(EMod, &mut xss);
                let mut out = IConst(0.0);
                let mut out_set = false;
                for xs in xss.iter() {
                    let instr = xs.compile(ast, cexpr)?;
                    if out_set {
                        if let (IConst(dividend), IConst(divisor)) = (&out, &instr) {
                            out = IConst(dividend % divisor);
                            continue;
                        }
                        out = IMod(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr));
                    } else {
                        out = instr;
                        out_set = true;
                    }
                }
                Ok(out)
            }
            EExp => {
                // Right-to-Left Associativity
                let mut xss = Vec::<ExprSlice>::with_capacity(2);
                self.split(EExp, &mut xss);
                let mut out = IConst(0.0);
                let mut out_set = false;
                for xs in xss.into_iter().rev() {
                    let instr = xs.compile(ast, cexpr)?;
                    if out_set {
                        if let (IConst(power), IConst(base)) = (&out, &instr) {
                            out = IConst(base.powf(*power));
                            continue;
                        }
                        out = IExp(cexpr.instr_to_icv(instr), cexpr.instr_to_icv(out));
                    } else {
                        out = instr;
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
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>) -> Result<Instruction, Error> {
        let top = ExprSlice::from_expr(&self);
        top.compile(ast, cexpr)
    }
}

impl<M: Module> Compiler<M> for UnaryOp {
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>) -> Result<Instruction, Error> {
        match self {
            // EPos(i) => ast.get_val(*i).compile(ast, cexpr),
            ENeg(icv) => {
                let instr = icv.compile(ast, cexpr)?;
                if let IConst(c) = instr {
                    Ok(IConst(-c))
                } else {
                    Ok(cexpr.neg_wrap(instr))
                }
            }
            ENot(icv) => {
                let instr = icv.compile(ast, cexpr)?;
                if let IConst(c) = instr {
                    Ok(IConst(Float::float_eq(c, 0.0).into()))
                } else {
                    Ok(cexpr.not_wrap(instr))
                }
            }
        }
    }
}

impl<M: Module> Compiler<M> for parser::ICV {
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>) -> Result<Instruction, Error> {
        match self {
            parser::ICV::EConst(c) => Ok(IConst(*c)),
            parser::ICV::EVar(name) => {
                if let Some(c) = M::constant(name) {
                    Ok(IConst(c))
                } else if let Some(ptr) = cexpr.module.get_var(name) {
                    Ok(IVar(ptr))
                } else {
                    Err(Error::Undefined(name.to_owned()))
                }
            }
            parser::ICV::I(i) => {
                let instr = ast.get_expr(*i).compile(ast, cexpr);
                instr
            }
        }
    }
}

impl<M: Module> Compiler<M> for Value {
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr<M>) -> Result<Instruction, Error> {
        match self {
            ICV(icv) => icv.compile(ast, cexpr),
            EUnaryOp(u) => u.compile(ast, cexpr),
            EFunc { name, args } => {
                match (name.as_str(), args.as_slice()) {
                    //Special case for 'min' function
                    ("min", [fi, is @ ..]) => {
                        let first = fi.compile(ast, cexpr)?;
                        let mut rest = Vec::<Instruction>::with_capacity(is.len());
                        for i in is {
                            rest.push(i.compile(ast, cexpr)?);
                        }
                        let mut out = IConst(0.0);
                        let mut out_set = false;
                        let mut const_min = 0.0;
                        let mut const_min_set = false;
                        if let IConst(f) = first {
                            const_min = f;
                            const_min_set = true;
                        } else {
                            out = first;
                            out_set = true;
                        }
                        for instr in rest {
                            if let IConst(f) = instr {
                                if const_min_set {
                                    const_min = const_min.min(f)
                                    // if f < const_min {
                                    //     const_min = f;
                                    // }
                                } else {
                                    const_min = f;
                                    const_min_set = true;
                                }
                            } else {
                                if out_set {
                                    out = IMin(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr));
                                } else {
                                    out = instr;
                                    out_set = true;
                                }
                            }
                        }
                        if const_min_set {
                            if out_set {
                                out = IMin(cexpr.instr_to_icv(out), ICV::IConst(const_min));
                            } else {
                                out = IConst(const_min);
                                // out_set = true;  // Comment out so the compiler doesn't complain about unused assignments.
                            }
                        }
                        //assert!(out_set);
                        Ok(out)
                    }

                    // Special case for 'max' function
                    ("max", [fi, is @ ..]) => {
                        let first = fi.compile(ast, cexpr)?;
                        let mut rest = Vec::<Instruction>::with_capacity(is.len());
                        for i in is {
                            rest.push(i.compile(ast, cexpr)?);
                        }
                        let mut out = IConst(0.0);
                        let mut out_set = false;
                        let mut const_max = 0.0;
                        let mut const_max_set = false;
                        if let IConst(f) = first {
                            const_max = f;
                            const_max_set = true;
                        } else {
                            out = first;
                            out_set = true;
                        }
                        for instr in rest {
                            if let IConst(f) = instr {
                                if const_max_set {
                                    const_max = const_max.max(f);
                                    // if f > const_max {
                                    //     const_max = f;
                                    // }
                                } else {
                                    const_max = f;
                                    const_max_set = true;
                                }
                            } else {
                                if out_set {
                                    out = IMax(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr));
                                } else {
                                    out = instr;
                                    out_set = true;
                                }
                            }
                        }
                        if const_max_set {
                            if out_set {
                                out = IMax(cexpr.instr_to_icv(out), ICV::IConst(const_max));
                            } else {
                                out = IConst(const_max);
                                // out_set = true;  // Comment out so the compiler doesn't complain about unused assignments.
                            }
                        }
                        //assert!(out_set);
                        Ok(out)
                    }

                    (name, args) => {
                        let mut icv_args = Vec::with_capacity(6);
                        for arg in args {
                            let instr = arg.compile(ast, cexpr)?;
                            let icv = cexpr.instr_to_icv(instr);
                            icv_args.push(icv);
                        }

                        match cexpr.module.func(name, &icv_args) {
                            Some(Func::F_F(f, ICV::IConst(a0))) => Ok(Instruction::IConst(f(a0))),
                            Some(Func::FF_F(f, ICV::IConst(a0), ICV::IConst(a1))) => {
                                Ok(Instruction::IConst(f(a0, a1)))
                            }
                            Some(f) => Ok(Instruction::IFunc(f)),
                            None => Err(Error::Undefined(name.to_owned())),
                        }
                    }
                }
            }
            _ => unreachable!(),
        }
    }
}
