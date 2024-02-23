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

use crate::builtins;
use crate::builtins::{float_eq, float_ne};

#[cfg(feature = "unsafe-vars")]
use crate::parser::StdFunc::EUnsafeVar;

// pub use crate::parser::I;
use crate::parser::{
    Ast,
    BinaryOp::{self, *},
    Expr, ExprPair,
    UnaryOp::{self, *},
    Value::{self, *},
};
use crate::write_indexed_list;
use std::fmt::{self, Debug};
use std::mem;

impl Ast {
    pub fn compile(&self, cexpr: &mut CExpr) {
        cexpr.compile(self)
    }
}

/// This enumeration boosts performance because it eliminates expensive function calls for constant values.
#[derive(PartialEq)]
pub enum ICV {
    I(usize),
    IConst(f64),
    IVar(String),
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

impl From<usize> for ICV {
    #[inline(always)]
    fn from(value: usize) -> Self {
        ICV::I(value)
    }
}

/// `CExpr` is where `compile()` results are stored.
pub struct CExpr {
    pub(crate) instrs: Vec<Instruction>,
}

impl CExpr {
    /// Creates a new default-sized `Ast`.
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(32)
    }

    /// Creates a new `Ast` with the given capacity.
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            instrs: Vec::with_capacity(cap),
        }
    }

    /// Creates a new `Ast` with the given capacity.
    #[inline]
    pub fn compile(&mut self, ast: &Ast) {
        self.clear();
        let expr = ast.exprs.last().unwrap();
        let instr = expr.compile(ast, self);

        self.instrs.push(instr);
    }

    #[inline]
    pub fn from_ast(ast: &Ast) -> Self {
        let mut cexpr = Self::new();
        cexpr.compile(ast);
        cexpr
    }

    #[inline]
    pub fn from_str<S: AsRef<str>>(expr_str: S) -> Self {
        let mut ast = Ast::new();
        ast.parse(expr_str);
        Self::from_ast(&ast)
    }

    #[inline(always)]
    pub fn last(&self) -> Option<&Instruction> {
        self.instrs.last()
    }

    /// Returns a reference to the [`Instruction`](../compiler/enum.Instruction.html)
    /// located at `instr_i` within the `CExpr.instrs'.
    ///
    /// If `instr_i` is out-of-bounds, a reference to a default `Instruction` is returned.
    ///
    #[inline(always)]
    pub fn get(&self, instr_i: usize) -> &Instruction {
        self.instrs.get(instr_i).unwrap()
    }

    #[inline(always)]
    pub fn instr_to_icv(&mut self, instr: Instruction) -> ICV {
        match instr {
            IConst(c) => ICV::IConst(c),
            IVar(s) => ICV::IVar(s),
            _ => ICV::from(self.push(instr)),
        }
    }

    /// Appends an `Instruction` to `CExpr.instrs`.
    #[inline(always)]
    fn push(&mut self, instr: Instruction) -> usize {
        let i = self.instrs.len();
        self.instrs.push(instr);
        i
    }

    /// Removes an `Instruction` from `CExpr.instrs` as efficiently as possible.
    #[inline(always)]
    fn pop(&mut self) -> Instruction {
        self.instrs.pop().unwrap()
    }

    /// Clears all data from `CExpr.instrs`.
    #[inline(always)]
    pub fn clear(&mut self) {
        self.instrs.clear();
    }

    #[inline(always)]
    fn neg_wrap(&mut self, instr: Instruction) -> Instruction {
        match instr {
            IConst(c) => IConst(-c),
            INeg(_) => self.pop(),
            _ => INeg(self.instr_to_icv(instr)),
        }
    }
    #[inline(always)]
    fn not_wrap(&mut self, instr: Instruction) -> Instruction {
        match instr {
            IConst(c) => IConst((float_eq(c, 0.0)).into()),
            INot(_) => self.pop(),
            _ => INot(self.instr_to_icv(instr)),
        }
    }
    #[inline(always)]
    fn inv_wrap(&mut self, instr: Instruction) -> Instruction {
        match instr {
            IConst(c) => IConst(1.0 / c),
            IInv(_) => self.pop(),
            _ => IInv(self.instr_to_icv(instr)),
        }
    }

    #[inline(always)]
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
        if float_ne(const_prod, 1.0) {
            if out_set {
                out = IMul(self.instr_to_icv(out), ICV::IConst(const_prod));
            } else {
                out = IConst(const_prod);
            }
        }
        out
    }

    #[inline(always)]
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
                    out = IAdd(self.instr_to_icv(out), self.instr_to_icv(instr));
                } else {
                    out = instr;
                    out_set = true;
                }
            }
        }
        if float_ne(const_sum, 0.0) {
            if out_set {
                out = IAdd(self.instr_to_icv(out), ICV::IConst(const_sum));
            } else {
                out = IConst(const_sum);
            }
        }
        out
    }

    // Can't inline recursive functions:
    fn push_mul_leaves(&mut self, instrs: &mut Vec<Instruction>, li: ICV, ric: ICV) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match ric {
            ICV::I(_) => {
                let instr = self.pop();
                if let IMul(rli, rric) = instr {
                    self.push_mul_leaves(instrs, rli, rric);
                } else {
                    instrs.push(instr);
                }
            }
            ICV::IConst(c) => instrs.push(IConst(c)),
            ICV::IVar(c) => instrs.push(IVar(c)),
        };

        let instr = self.pop();
        if let IMul(lli, lric) = instr {
            self.push_mul_leaves(instrs, lli, lric);
        } else {
            instrs.push(instr);
        }
    }
    // Can't inline recursive functions:
    fn push_add_leaves(&mut self, instrs: &mut Vec<Instruction>, li: ICV, ric: ICV) {
        // Take 'r' before 'l' for a chance for more efficient memory usage:
        match ric {
            ICV::I(_) => {
                let instr = self.pop();
                if let IAdd(rli, rric) = instr {
                    self.push_add_leaves(instrs, rli, rric);
                } else {
                    instrs.push(instr);
                }
            }
            ICV::IConst(c) => instrs.push(IConst(c)),
            ICV::IVar(c) => instrs.push(IVar(c)),
        };

        let instr = self.pop();
        if let IAdd(lli, lric) = instr {
            self.push_add_leaves(instrs, lli, lric);
        } else {
            instrs.push(instr);
        }
    }
}

impl Debug for CExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "CExpr[")?;
        write_indexed_list(f, &self.instrs)?;
        write!(f, "]")?;
        Ok(())
    }
}

/// An `Instruction` is an optimized Ast node resulting from compilation.
#[allow(non_camel_case_types)]
#[derive(Debug, PartialEq)]
pub enum Instruction {
    //---- Primitive Value Types:
    IConst(f64),

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
    IOR(ICV, ICV),
    IAND(ICV, ICV),

    //---- Callables:
    IVar(String),
    #[cfg(feature = "unsafe-vars")]
    IUnsafeVar {
        name: String,
        ptr: *const f64,
    },
    IFunc(String, Vec<String>, Vec<ICV>),
    IFunc_1F(fn(f64) -> f64, ICV),
    IFunc_2F(fn(f64, f64) -> f64, ICV, ICV),
    IFunc_3F(fn(f64, f64, f64) -> f64, ICV, ICV, ICV),
    IFunc_1S_NF(fn(&str, Vec<f64>) -> f64, String, Vec<ICV>),

    IMin(ICV, ICV),
    IMax(ICV, ICV),
}
use Instruction::*;

/// You must `use` the `Compiler` trait before you can call `.compile()` on parsed `Expr`s.
pub trait Compiler {
    /// Turns a parsed `Expr` into a compiled `Instruction`.
    ///
    /// Cannot fail, unless you run out of memory.
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr) -> Instruction;
}

#[derive(Debug)]
struct ExprSlice<'s>(&'s Value, Vec<&'s ExprPair>);

impl<'s> ExprSlice<'s> {
    fn new(first: &Value) -> ExprSlice<'_> {
        ExprSlice(first, Vec::with_capacity(8))
    }
    #[inline(always)]
    fn from_expr(expr: &Expr) -> ExprSlice<'_> {
        let mut sl = ExprSlice::new(&expr.0);
        for exprpairref in expr.1.iter() {
            sl.1.push(exprpairref)
        }
        sl
    }
    #[inline(always)]
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

    #[inline(always)]
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

impl Compiler for ExprSlice<'_> {
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr) -> Instruction {
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
            let mut out = xss.first().unwrap().compile(ast, cexpr);

            for (i, op) in ops.into_iter().enumerate() {
                let instr = xss.get(i + 1).unwrap().compile(ast, cexpr);

                if let IConst(l) = out {
                    if let IConst(r) = instr {
                        out = match op {
                            EEQ => IConst((float_eq(l, r)).into()),
                            ENE => IConst((float_ne(l, r)).into()),
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
            return out;
        }

        match lowest_op {
            EOR => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EOR, &mut xss);
                let mut out = IConst(0.0);
                let mut out_set = false;
                for xs in xss.iter() {
                    let instr = xs.compile(ast, cexpr);
                    if out_set {
                        out = IOR(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr));
                    } else {
                        if let IConst(c) = instr {
                            if float_ne(c, 0.0) {
                                return instr;
                            }
                            // out = instr;     // Skip this 0 value (mostly so I don't complicate my logic in 'if out_set' since I can assume that any set value is non-const).
                            // out_set = true;
                        } else {
                            out = instr;
                            out_set = true;
                        }
                    }
                }
                out
            }
            EAND => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EAND, &mut xss);
                let mut out = IConst(1.0);
                let mut out_set = false;
                for xs in xss.iter() {
                    let instr = xs.compile(ast, cexpr);
                    if let IConst(c) = instr {
                        if float_eq(c, 0.0) {
                            return instr;
                        }
                    }
                    if out_set {
                        if let IConst(_) = out {
                            // If we get here, we know that the const is non-zero.
                            out = instr;
                        } else {
                            out = IAND(cexpr.instr_to_icv(out), cexpr.instr_to_icv(instr));
                        }
                    } else {
                        out = instr;
                        out_set = true;
                    }
                }
                out
            }
            EAdd => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EAdd, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for xs in xss {
                    let instr = xs.compile(ast, cexpr);
                    if let IAdd(li, ric) = instr {
                        cexpr.push_add_leaves(&mut instrs, li, ric); // Flatten nested structures like "x - 1 + 2 - 3".
                    } else {
                        instrs.push(instr);
                    }
                }
                cexpr.compile_add(instrs)
            }
            ESub => {
                // Note: We don't need to push_add_leaves from here because Sub has a higher precedence than Add.

                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(ESub, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let instr = xs.compile(ast, cexpr);
                    if i == 0 {
                        instrs.push(instr);
                    } else {
                        instrs.push(cexpr.neg_wrap(instr));
                    }
                }
                cexpr.compile_add(instrs)
            }
            EMul => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EMul, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for xs in xss {
                    let instr = xs.compile(ast, cexpr);
                    if let IMul(li, ric) = instr {
                        cexpr.push_mul_leaves(&mut instrs, li, ric); // Flatten nested structures like "deg/360 * 2*pi()".
                    } else {
                        instrs.push(instr);
                    }
                }
                cexpr.compile_mul(instrs)
            }
            EDiv => {
                // Note: We don't need to push_mul_leaves from here because Div has a higher precedence than Mul.

                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EDiv, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let instr = xs.compile(ast, cexpr);
                    if i == 0 {
                        instrs.push(instr);
                    } else {
                        instrs.push(cexpr.inv_wrap(instr));
                    }
                }
                cexpr.compile_mul(instrs)
            }

            EMod => {
                let mut xss = Vec::<ExprSlice>::with_capacity(2);
                self.split(EMod, &mut xss);
                let mut out = IConst(0.0);
                let mut out_set = false;
                for xs in xss.iter() {
                    let instr = xs.compile(ast, cexpr);
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
                out
            }
            EExp => {
                // Right-to-Left Associativity
                let mut xss = Vec::<ExprSlice>::with_capacity(2);
                self.split(EExp, &mut xss);
                let mut out = IConst(0.0);
                let mut out_set = false;
                for xs in xss.into_iter().rev() {
                    let instr = xs.compile(ast, cexpr);
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
                out
            }
            _ => unreachable!(),
        }
    }
}

impl Compiler for Expr {
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr) -> Instruction {
        let top = ExprSlice::from_expr(&self);
        top.compile(ast, cexpr)
    }
}

impl Compiler for UnaryOp {
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr) -> Instruction {
        match self {
            EPos(i) => ast.get_val(*i).compile(ast, cexpr),
            ENeg(i) => {
                let instr = ast.get_val(*i).compile(ast, cexpr);
                if let IConst(c) = instr {
                    IConst(-c)
                } else {
                    cexpr.neg_wrap(instr)
                }
            }
            ENot(i) => {
                let instr = ast.get_val(*i).compile(ast, cexpr);
                if let IConst(c) = instr {
                    IConst((float_eq(c, 0.0)).into())
                } else {
                    cexpr.not_wrap(instr)
                }
            }
            EParen(i) => ast.get_expr(*i).compile(ast, cexpr),
        }
    }
}

impl Compiler for Value {
    fn compile(&self, ast: &Ast, cexpr: &mut CExpr) -> Instruction {
        match self {
            EConst(c) => IConst(*c),
            EUnaryOp(u) => u.compile(ast, cexpr),

            EVar(name) => {
                if let Some(c) = builtins::constant(name) {
                    IConst(c)
                } else {
                    IVar(name.clone())
                }
            }
            #[cfg(feature = "unsafe-vars")]
            EUnsafeVar { name, ptr } => IUnsafeVar {
                name: name.clone(),
                ptr: *ptr,
            },

            EFunc { name, sargs, args } => {
                match (name.as_str(), sargs.as_slice(), args.as_slice()) {
                    //Special case for 'min' function
                    ("min", [], [fi, is @ ..]) => {
                        let first = ast.get_expr(*fi).compile(ast, cexpr);
                        let mut rest = Vec::<Instruction>::with_capacity(is.len());
                        for i in is {
                            rest.push(ast.get_expr(*i).compile(ast, cexpr));
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
                        return out;
                    }

                    // Special case for 'max' function
                    ("max", [], [fi, is @ ..]) => {
                        let first = ast.get_expr(*fi).compile(ast, cexpr);
                        let mut rest = Vec::<Instruction>::with_capacity(is.len());
                        for i in is {
                            rest.push(ast.get_expr(*i).compile(ast, cexpr));
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
                        return out;
                    }
                    (_, [], [arg]) => {
                        if let Some(f) = builtins::func_1f(name) {
                            let instr = ast.get_expr(*arg).compile(ast, cexpr);
                            return {
                                if let IConst(c) = instr {
                                    IConst(f(c))
                                } else {
                                    // IFunc_1F(f, cexpr.push(instr))
                                    IFunc_1F(f, cexpr.instr_to_icv(instr))
                                }
                            };
                        }
                    }
                    (_, [], [arg0, arg1]) => {
                        if let Some(f) = builtins::func_2f(name) {
                            let instr0 = ast.get_expr(*arg0).compile(ast, cexpr);
                            let instr1 = ast.get_expr(*arg1).compile(ast, cexpr);
                            return {
                                if let (IConst(c0), IConst(c1)) = (&instr0, &instr1) {
                                    IConst(f(*c0, *c1))
                                } else {
                                    IFunc_2F(
                                        f,
                                        cexpr.instr_to_icv(instr0),
                                        cexpr.instr_to_icv(instr1),
                                    )
                                }
                            };
                        }
                    }
                    (_, [], [arg0, arg1, arg2]) => {
                        if let Some(f) = builtins::func_3f(name) {
                            let instr0 = ast.get_expr(*arg0).compile(ast, cexpr);
                            let instr1 = ast.get_expr(*arg1).compile(ast, cexpr);
                            let instr2 = ast.get_expr(*arg2).compile(ast, cexpr);
                            return {
                                if let (IConst(c0), IConst(c1), IConst(c2)) =
                                    (&instr0, &instr1, &instr2)
                                {
                                    IConst(f(*c0, *c1, *c2))
                                } else {
                                    IFunc_3F(
                                        f,
                                        cexpr.instr_to_icv(instr0),
                                        cexpr.instr_to_icv(instr1),
                                        cexpr.instr_to_icv(instr2),
                                    )
                                }
                            };
                        }
                    }
                    (_, [sarg], _) => {
                        if let Some(f) = builtins::func_1s_nf(name) {
                            let mut iargs = Vec::<ICV>::with_capacity(args.len());
                            for i in args {
                                let instr = ast.get_expr(*i).compile(ast, cexpr);
                                iargs.push(cexpr.instr_to_icv(instr));
                            }
                            return IFunc_1S_NF(f, sarg.clone(), iargs);
                        }
                    }
                    _ => (),
                }

                let mut iargs = Vec::<ICV>::with_capacity(args.len());
                for i in args {
                    let instr = ast.get_expr(*i).compile(ast, cexpr);
                    iargs.push(cexpr.instr_to_icv(instr));
                }
                IFunc(name.clone(), sargs.clone(), iargs)
            }
        }
    }
}
