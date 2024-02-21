//! This module compiles parsed `Expr`s into an optimized AST node called an `Instruction`.
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
//! * Variable-length `Expr`/`Value` AST nodes are converted into constant-sized `Instruction` nodes.
//! * The `IC` enumeration helps to eliminate expensive function calls.

use crate::builtins;
#[cfg(feature = "unsafe-vars")]
use crate::parser::StdFunc::EUnsafeVar;
use crate::parser::AST;
use crate::parser::{
    BinaryOp::{self, *},
    Expr, ExprPair,
    StdFunc::{self, *},
    UnaryOp::{self, *},
    Value,
};
use crate::write_indexed_list;
use std::fmt;
use std::mem;

impl AST {
    #[inline]
    pub fn compile(&self, oast: &mut OAST) {
        oast.clear();
        let expr = self.exprs.last().unwrap();
        let instr = expr.compile(self, oast);

        oast.instrs.push(instr);
    }
}
/// `OAST` is where `compile()` results are stored.
pub struct OAST {
    pub(crate) instrs: Vec<Instruction>,
}

impl OAST {
    /// Creates a new default-sized `AST`.
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(32)
    }

    /// Creates a new `AST` with the given capacity.
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            instrs: Vec::with_capacity(cap),
        }
    }

    #[inline(always)]
    pub fn last(&self) -> Option<&Instruction> {
        self.instrs.last()
    }

    /// Returns a reference to the [`Instruction`](../compiler/enum.Instruction.html)
    /// located at `instr_i` within the `OAST.instrs'.
    ///
    /// If `instr_i` is out-of-bounds, a reference to a default `Instruction` is returned.
    ///
    #[inline(always)]
    pub fn get(&self, instr_i: usize) -> &Instruction {
        self.instrs.get(instr_i).unwrap()
    }

    #[inline(always)]
    pub fn instr_to_ic(&mut self, instr: Instruction) -> IC {
        match instr {
            IConst(c) => IC::C(c),
            _ => IC::I(self.push(instr)),
        }
    }
    /// Appends an `Instruction` to `OAST.instrs`.
    #[inline(always)]
    fn push(&mut self, instr: Instruction) -> usize {
        let i = self.instrs.len();
        self.instrs.push(instr);
        i
    }

    /// Removes an `Instruction` from `OAST.instrs` as efficiently as possible.
    #[inline(always)]
    fn pop(&mut self) -> Instruction {
        self.instrs.pop().unwrap()
    }

    /// Clears all data from `OAST.instrs`.
    #[inline(always)]
    pub fn clear(&mut self) {
        self.instrs.clear();
    }
}

impl fmt::Debug for OAST {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "OAST [")?;
        write_indexed_list(f, &self.instrs)?;
        write!(f, "]")?;
        Ok(())
    }
}

/// This enumeration boosts performance because it eliminates expensive function calls for constant values.
#[derive(PartialEq)]
pub enum IC {
    I(usize),
    C(f64),
}
impl fmt::Debug for IC {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            IC::I(i) => write!(f, "{}", i)?,
            IC::C(v) => write!(f, "IConst({})", v)?,
        }

        Ok(())
    }
}
/// An `Instruction` is an optimized AST node resulting from compilation.
#[allow(non_camel_case_types)]
#[derive(Debug, PartialEq)]
pub enum Instruction {
    //---- Primitive Value Types:
    IConst(f64),

    //---- Unary Ops:
    // Parentheses is a noop
    // Pos is a noop
    INeg(usize),
    INot(usize),
    IInv(usize),

    //---- Binary Math Ops:
    IAdd(usize, IC),
    // A Sub(x) is converted to an Add(Neg(x)).
    IMul(usize, IC),
    // A Div(n,d) is converted to a Mul(n,Inv(d)).
    IMod(IC, IC),

    IExp(IC, IC),

    //---- Binary Comparison Ops:
    ILT(IC, IC),
    ILTE(IC, IC),
    IEQ(IC, IC),
    INE(IC, IC),
    IGTE(IC, IC),
    IGT(IC, IC),

    //---- Binary Logic Ops:
    IOR(usize, IC),
    IAND(usize, IC),

    //---- Callables:
    IVar(String),
    #[cfg(feature = "unsafe-vars")]
    IUnsafeVar {
        name: String,
        ptr: *const f64,
    },
    // IFunc(String, Vec<IC>),
    IFunc(String, Vec<String>, Vec<IC>),
    IFunc_f(fn(f64) -> f64, usize),
    IFunc_f_f(fn(f64, f64) -> f64, IC, IC),
    IFunc_s_nf(fn(&str, Vec<f64>) -> f64, String, Vec<IC>),

    IMin(usize, IC),
    IMax(usize, IC),
    // IPrintFunc(String, Vec<IC>),
}
use Instruction::*;

/// You must `use` the `Compiler` trait before you can call `.compile()` on parsed `Expr`s.
pub trait Compiler {
    /// Turns a parsed `Expr` into a compiled `Instruction`.
    ///
    /// Cannot fail, unless you run out of memory.
    fn compile(&self, ast: &AST, oast: &mut OAST) -> Instruction;
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

/// Uses [`EPSILON`](https://doc.rust-lang.org/core/f64/constant.EPSILON.html) to determine equality of two `f64`s.
#[macro_export]
macro_rules! f64_eq {
    ($l:ident, $r:literal) => {
        ($l - $r).abs() <= 8.0 * std::f64::EPSILON
    };
    ($l:ident, $r:ident) => {
        ($l - $r).abs() <= 8.0 * std::f64::EPSILON
    };
    ($l:expr, $r:literal) => {
        ($l - $r).abs() <= 8.0 * std::f64::EPSILON
    };
    ($l:expr, $r:expr) => {
        (($l) - ($r)).abs() <= 8.0 * std::f64::EPSILON
    };
}

/// Uses [`EPSILON`](https://doc.rust-lang.org/core/f64/constant.EPSILON.html) to determine inequality of two `f64`s.
///
/// This is exactly the same as saying `!f64_eq(x,y)` but it is slightly more efficient.
#[macro_export]
macro_rules! f64_ne {
    ($l:ident, $r:literal) => {
        ($l - $r).abs() > 8.0 * std::f64::EPSILON
    };
    ($l:ident, $r:ident) => {
        ($l - $r).abs() > 8.0 * std::f64::EPSILON
    };
    ($l:expr, $r:literal) => {
        ($l - $r).abs() > 8.0 * std::f64::EPSILON
    };
    ($l:expr, $r:expr) => {
        (($l) - ($r)).abs() > 8.0 * std::f64::EPSILON
    };
}
#[inline]
fn neg_wrap(instr: Instruction, oast: &mut OAST) -> Instruction {
    match instr {
        IConst(c) => IConst(-c),
        INeg(i) => oast.pop(),
        _ => INeg(oast.push(instr)),
    }
}
#[inline]
fn not_wrap(instr: Instruction, oast: &mut OAST) -> Instruction {
    match instr {
        IConst(c) => IConst((f64_eq!(c, 0.0)).into()),
        INot(i) => oast.pop(),
        _ => INot(oast.push(instr)),
    }
}
#[inline]
fn inv_wrap(instr: Instruction, oast: &mut OAST) -> Instruction {
    match instr {
        IConst(c) => IConst(1.0 / c),
        IInv(i) => oast.pop(),
        _ => IInv(oast.push(instr)),
    }
}

#[inline]
fn compile_mul(instrs: Vec<Instruction>, oast: &mut OAST) -> Instruction {
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
                out = IMul(oast.push(out), IC::I(oast.push(instr)));
            } else {
                out = instr;
                out_set = true;
            }
        }
    }
    if f64_ne!(const_prod, 1.0) {
        if out_set {
            out = IMul(oast.push(out), IC::C(const_prod));
        } else {
            out = IConst(const_prod);
        }
    }
    out
}

#[inline]
fn compile_add(instrs: Vec<Instruction>, oast: &mut OAST) -> Instruction {
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
                out = IAdd(oast.push(out), IC::I(oast.push(instr)));
            } else {
                out = instr;
                out_set = true;
            }
        }
    }
    if f64_ne!(const_sum, 0.0) {
        if out_set {
            out = IAdd(oast.push(out), IC::C(const_sum));
        } else {
            out = IConst(const_sum);
        }
    }
    out
}

// Can't inline recursive functions:
fn push_mul_leaves(instrs: &mut Vec<Instruction>, oast: &mut OAST, li: usize, ric: IC) {
    // Take 'r' before 'l' for a chance for more efficient memory usage:
    match ric {
        IC::I(ri) => {
            let instr = oast.pop();
            if let IMul(rli, rric) = instr {
                push_mul_leaves(instrs, oast, rli, rric);
            } else {
                instrs.push(instr);
            }
        }
        IC::C(c) => instrs.push(IConst(c)),
    };

    let instr = oast.pop();
    if let IMul(lli, lric) = instr {
        push_mul_leaves(instrs, oast, lli, lric);
    } else {
        instrs.push(instr);
    }
}

fn push_add_leaves(instrs: &mut Vec<Instruction>, oast: &mut OAST, li: usize, ric: IC) {
    // Take 'r' before 'l' for a chance for more efficient memory usage:
    match ric {
        IC::I(ri) => {
            let instr = oast.pop();
            if let IAdd(rli, rric) = instr {
                push_add_leaves(instrs, oast, rli, rric);
            } else {
                instrs.push(instr);
            }
        }
        IC::C(c) => instrs.push(IConst(c)),
    };

    let instr = oast.pop();
    if let IAdd(lli, lric) = instr {
        push_add_leaves(instrs, oast, lli, lric);
    } else {
        instrs.push(instr);
    }
}

impl Compiler for ExprSlice<'_> {
    fn compile(&self, ast: &AST, oast: &mut OAST) -> Instruction {
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
            None => return self.0.compile(ast, oast),
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
            let mut out = xss.first().unwrap().compile(ast, oast);

            for (i, op) in ops.into_iter().enumerate() {
                let instr = xss.get(i + 1).unwrap().compile(ast, oast);

                if let IConst(l) = out {
                    if let IConst(r) = instr {
                        out = match op {
                            EEQ => IConst((f64_eq!(l, r)).into()),
                            ENE => IConst((f64_ne!(l, r)).into()),
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
                    EEQ => IEQ(oast.instr_to_ic(out), oast.instr_to_ic(instr)),
                    ENE => INE(oast.instr_to_ic(out), oast.instr_to_ic(instr)),
                    ELT => ILT(oast.instr_to_ic(out), oast.instr_to_ic(instr)),
                    EGT => IGT(oast.instr_to_ic(out), oast.instr_to_ic(instr)),
                    ELTE => ILTE(oast.instr_to_ic(out), oast.instr_to_ic(instr)),
                    EGTE => IGTE(oast.instr_to_ic(out), oast.instr_to_ic(instr)),
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
                    let instr = xs.compile(ast, oast);
                    if out_set {
                        out = IOR(oast.push(out), oast.instr_to_ic(instr));
                    } else {
                        if let IConst(c) = instr {
                            if f64_ne!(c, 0.0) {
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
                    let instr = xs.compile(ast, oast);
                    if let IConst(c) = instr {
                        if f64_eq!(c, 0.0) {
                            return instr;
                        }
                    }
                    if out_set {
                        if let IConst(_) = out {
                            // If we get here, we know that the const is non-zero.
                            out = instr;
                        } else {
                            out = IAND(oast.push(out), oast.instr_to_ic(instr));
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
                    let instr = xs.compile(ast, oast);
                    if let IAdd(li, ric) = instr {
                        push_add_leaves(&mut instrs, oast, li, ric); // Flatten nested structures like "x - 1 + 2 - 3".
                    } else {
                        instrs.push(instr);
                    }
                }
                compile_add(instrs, oast)
            }
            ESub => {
                // Note: We don't need to push_add_leaves from here because Sub has a higher precedence than Add.

                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(ESub, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let instr = xs.compile(ast, oast);
                    if i == 0 {
                        instrs.push(instr);
                    } else {
                        instrs.push(neg_wrap(instr, oast));
                    }
                }
                compile_add(instrs, oast)
            }
            EMul => {
                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EMul, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for xs in xss {
                    let instr = xs.compile(ast, oast);
                    if let IMul(li, ric) = instr {
                        push_mul_leaves(&mut instrs, oast, li, ric); // Flatten nested structures like "deg/360 * 2*pi()".
                    } else {
                        instrs.push(instr);
                    }
                }
                compile_mul(instrs, oast)
            }
            EDiv => {
                // Note: We don't need to push_mul_leaves from here because Div has a higher precedence than Mul.

                let mut xss = Vec::<ExprSlice>::with_capacity(4);
                self.split(EDiv, &mut xss);
                let mut instrs = Vec::<Instruction>::with_capacity(xss.len());
                for (i, xs) in xss.into_iter().enumerate() {
                    let instr = xs.compile(ast, oast);
                    if i == 0 {
                        instrs.push(instr);
                    } else {
                        instrs.push(inv_wrap(instr, oast));
                    }
                }
                compile_mul(instrs, oast)
            }

            EMod => {
                let mut xss = Vec::<ExprSlice>::with_capacity(2);
                self.split(EMod, &mut xss);
                let mut out = IConst(0.0);
                let mut out_set = false;
                for xs in xss.iter() {
                    let instr = xs.compile(ast, oast);
                    if out_set {
                        if let IConst(dividend) = out {
                            if let IConst(divisor) = instr {
                                out = IConst(dividend % divisor);
                                continue;
                            }
                        }
                        out = IMod(oast.instr_to_ic(out), oast.instr_to_ic(instr));
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
                    let instr = xs.compile(ast, oast);
                    if out_set {
                        if let IConst(power) = out {
                            if let IConst(base) = instr {
                                out = IConst(base.powf(power));
                                continue;
                            }
                        }
                        out = IExp(oast.instr_to_ic(instr), oast.instr_to_ic(out));
                    } else {
                        out = instr;
                        out_set = true;
                    }
                }
                out
            }

            _ => unreachable!(), // unreachable
        }
    }
}

impl Compiler for Expr {
    fn compile(&self, ast: &AST, oast: &mut OAST) -> Instruction {
        let top = ExprSlice::from_expr(&self);
        top.compile(ast, oast)
    }
}

impl Compiler for Value {
    fn compile(&self, ast: &AST, oast: &mut OAST) -> Instruction {
        match self {
            Value::EConst(c) => IConst(*c),
            Value::EUnaryOp(u) => u.compile(ast, oast),
            Value::EStdFunc(f) => f.compile(ast, oast),
        }
    }
}

impl Compiler for UnaryOp {
    fn compile(&self, ast: &AST, oast: &mut OAST) -> Instruction {
        match self {
            EPos(i) => ast.get_val(*i).compile(ast, oast),
            ENeg(i) => {
                let instr = ast.get_val(*i).compile(ast, oast);
                if let IConst(c) = instr {
                    IConst(-c)
                } else {
                    neg_wrap(instr, oast)
                }
            }
            ENot(i) => {
                let instr = ast.get_val(*i).compile(ast, oast);
                if let IConst(c) = instr {
                    IConst((f64_eq!(c, 0.0)).into())
                } else {
                    not_wrap(instr, oast)
                }
            }
            EParen(i) => ast.get_expr(*i).compile(ast, oast),
        }
    }
}

impl Compiler for StdFunc {
    fn compile(&self, ast: &AST, oast: &mut OAST) -> Instruction {
        match self {
            EMin {
                first: fi,
                rest: is,
            } => {
                let first = ast.get_expr(*fi).compile(ast, oast);
                let mut rest = Vec::<Instruction>::with_capacity(is.len());
                for i in is {
                    rest.push(ast.get_expr(*i).compile(ast, oast));
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
                            out = IMin(oast.push(out), IC::I(oast.push(instr)));
                        } else {
                            out = instr;
                            out_set = true;
                        }
                    }
                }
                if const_min_set {
                    if out_set {
                        out = IMin(oast.push(out), IC::C(const_min));
                    } else {
                        out = IConst(const_min);
                        // out_set = true;  // Comment out so the compiler doesn't complain about unused assignments.
                    }
                }
                //assert!(out_set);
                out
            }

            EMax {
                first: fi,
                rest: is,
            } => {
                let first = ast.get_expr(*fi).compile(ast, oast);
                let mut rest = Vec::<Instruction>::with_capacity(is.len());
                for i in is {
                    rest.push(ast.get_expr(*i).compile(ast, oast));
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
                            out = IMax(oast.push(out), IC::I(oast.push(instr)));
                        } else {
                            out = instr;
                            out_set = true;
                        }
                    }
                }
                if const_max_set {
                    if out_set {
                        out = IMax(oast.push(out), IC::C(const_max));
                    } else {
                        out = IConst(const_max);
                        // out_set = true;  // Comment out so the compiler doesn't complain about unused assignments.
                    }
                }
                //assert!(out_set);
                out
            }

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

            // EFunc { name, args } => {
            //     match args.as_slice() {
            //         [arg] => {
            //             if let Some(f) = builtins::func_f(name) {
            //                 let instr = ast.get_expr(*arg).compile(ast, oast);
            //                 return {
            //                     if let IConst(c) = instr {
            //                         IConst(f(c))
            //                     } else {
            //                         IFunc_f(f, oast.push(instr))
            //                     }
            //                 };
            //             }
            //         }
            //         [arg0, arg1] => {
            //             if let Some(f) = builtins::func_f_f(name) {
            //                 let instr0 = ast.get_expr(*arg0).compile(ast, oast);
            //                 let instr1 = ast.get_expr(*arg1).compile(ast, oast);
            //                 return {
            //                     if let (IConst(c0), IConst(c1)) = (&instr0, &instr1) {
            //                         IConst(f(*c0, *c1))
            //                     } else {
            //                         IFunc_f_f(f, oast.instr_to_ic(instr0), oast.instr_to_ic(instr1))
            //                     }
            //                 };
            //             }
            //         }
            //         _ => (),
            //     }

            //     let mut iargs = Vec::<IC>::with_capacity(args.len());
            //     for i in args {
            //         let instr = ast.get_expr(*i).compile(ast, oast);
            //         iargs.push(oast.instr_to_ic(instr));
            //     }
            //     IFunc(name.clone(), iargs)
            // }
            EFunc { name, sargs, args } => {
                match (sargs.as_slice(), args.as_slice()) {
                    ([], [arg]) => {
                        if let Some(f) = builtins::func_1f(name) {
                            let instr = ast.get_expr(*arg).compile(ast, oast);
                            return {
                                if let IConst(c) = instr {
                                    IConst(f(c))
                                } else {
                                    IFunc_f(f, oast.push(instr))
                                }
                            };
                        }
                    }
                    ([], [arg0, arg1]) => {
                        if let Some(f) = builtins::func_2f(name) {
                            let instr0 = ast.get_expr(*arg0).compile(ast, oast);
                            let instr1 = ast.get_expr(*arg1).compile(ast, oast);
                            return {
                                if let (IConst(c0), IConst(c1)) = (&instr0, &instr1) {
                                    IConst(f(*c0, *c1))
                                } else {
                                    IFunc_f_f(f, oast.instr_to_ic(instr0), oast.instr_to_ic(instr1))
                                }
                            };
                        }
                    }
                    ([sarg], _) => {
                        if let Some(f) = builtins::func_1s_nf(name) {
                            let mut iargs = Vec::<IC>::with_capacity(args.len());
                            for i in args {
                                let instr = ast.get_expr(*i).compile(ast, oast);
                                iargs.push(oast.instr_to_ic(instr));
                            }
                            return IFunc_s_nf(f, sarg.clone(), iargs);
                        }
                    }
                    _ => (),
                }

                let mut iargs = Vec::<IC>::with_capacity(args.len());
                for i in args {
                    let instr = ast.get_expr(*i).compile(ast, oast);
                    iargs.push(oast.instr_to_ic(instr));
                }
                IFunc(name.clone(), sargs.clone(), iargs)
            }
        }
    }
}
