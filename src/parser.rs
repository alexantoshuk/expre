//! This module parses string expressions into an Ast which can then be compiled or evaluated.
//!
//! # fasteval Algebra Grammar
//! ```text
//! Expr: Value (BinaryOp Value)*
//!
//! Value: Constant || UnaryOp || PrintFunc || StdFunc
//!
//! Constant: [+-]?[0-9]*(\.[0-9]+)?( ([eE][+-]?[0-9]+) || [pnuµmkKMGT] )?  || [+-]?(NaN || inf)
//!
//! UnaryOp: +Value || -Value || (Expr) || [Expr] || !Value
//!
//! BinaryOp: + || - || * || / || % || ^ || < || <= || == || != || >= || > || (or || '||') || (and || '&&')
//!
//! VarName: [a-zA-Z_][a-zA-Z_0-9]*
//!
//! StdFunc: VarName((Expr,)*)?  ||  VarName[(Expr,)*]?
//!
//! PrintFunc: print(ExprOrString,*)
//!
//! ExprOrString: Expr || String
//!
//! String: ".*"
//! ```

use crate::error::Error;
use crate::write_indexed_list;
#[cfg(feature = "unsafe-vars")]
use std::collections::BTreeMap;
use std::fmt::{self, Debug};
use std::ops::Deref;
use std::ptr;
use std::str::{from_utf8, from_utf8_unchecked};

pub const DEFAULT_EXPR_LEN_LIMIT: usize = 1024 * 10;
pub const DEFAULT_EXPR_DEPTH_LIMIT: usize = 32;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct I(pub usize);

impl Debug for I {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, ":{}", self.0)
    }
}

impl Deref for I {
    type Target = usize;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<usize> for I {
    #[inline(always)]
    fn from(value: usize) -> Self {
        I(value)
    }
}

impl From<I> for usize {
    #[inline(always)]
    fn from(value: I) -> Self {
        value.0
    }
}

pub struct Ast {
    pub(crate) exprs: Vec<Expr>,
    char_buf: String,
    #[cfg(feature = "unsafe-vars")]
    pub(crate) unsafe_vars: BTreeMap<String, *const f64>,
}

impl Ast {
    /// Creates a new default-sized `Ast`.
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(64)
    }

    /// Creates a new `Ast` with the given capacity.
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            exprs: Vec::with_capacity(cap),
            char_buf: String::with_capacity(64),
            #[cfg(feature = "unsafe-vars")]
            unsafe_vars: BTreeMap::new(),
        }
    }

    /// Clears all data from [`Ast`](struct.ParseAST.html) and [`Ast`](struct.CompileAST.html).
    #[inline(always)]
    pub fn clear(&mut self) {
        self.exprs.clear();
    }

    /// Returns a reference to the [`Expr`](../parser/struct.Expr.html)
    /// located at `expr_i` within the `Ast.exprs'.
    ///
    #[inline(always)]
    pub fn get_expr(&self, expr_i: I) -> &Expr {
        // I'm using this non-panic match structure to boost performance:
        self.exprs.get(expr_i.0).unwrap()
    }

    #[inline(always)]
    pub fn last(&self) -> Option<&Expr> {
        self.exprs.last()
    }

    /// Returns a reference to the [`Value`](../parser/enum.Value.html)
    /// located at `val_i` within the `Ast.vals'.
    ///
    #[inline(always)]
    pub fn get_val(&self, val_i: I) -> &Value {
        // self.vals.get(val_i).unwrap()
        &self.exprs.get(val_i.0).unwrap().0
    }

    /// Appends an `Expr` to `Ast.exprs`.
    ///
    /// # Errors
    ///
    /// If `Ast.exprs` is already full, a `ASTOverflow` error is returned.
    ///
    #[inline(always)]
    pub(crate) fn push_expr(&mut self, expr: Expr) -> Result<I, Error> {
        let i = self.exprs.len();
        // if i >= self.exprs.capacity() {
        //     return Err(Error::ASTOverflow);
        // }
        self.exprs.push(expr);
        Ok(i.into())
    }

    #[inline(always)]
    pub(crate) fn push_val(&mut self, val: Value) -> Result<I, Error> {
        let i = self.exprs.len();
        // if i >= self.exprs.capacity() {
        //     return Err(Error::ASTOverflow);
        // }
        self.exprs.push(Expr(val, vec![]));
        Ok(i.into())
    }

    /// [See the `add_unsafe_var()` documentation above.](#unsafe-variable-registration-with-add_unsafe_var)
    #[cfg(feature = "unsafe-vars")]
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub unsafe fn add_unsafe_var(&mut self, name: String, ptr: &f64) {
        self.unsafe_vars.insert(name, ptr as *const f64);
    }
}

impl Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "Ast[")?;
        write_indexed_list(f, &self.exprs)?;
        write!(f, "]")?;
        Ok(())
    }
}

pub trait ParseExpr {
    fn parse_expr(&self, ast: &mut Ast) -> Result<(), Error>;
}

impl<S: AsRef<str>> ParseExpr for S {
    #[inline(always)]
    fn parse_expr(&self, ast: &mut Ast) -> Result<(), Error> {
        super::parse(self, ast)
    }
}

pub(crate) type ExprPair = (BinaryOp, Value);

/// An `Expr` is the top node of a parsed Ast.
///
/// It can be `compile()`d or `eval()`d.
#[derive(PartialEq)]
pub struct Expr(
    pub Value,
    pub Vec<ExprPair>, // cap=8
);

impl Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.1.is_empty() {
            write!(f, "{:?}", self.0)
        } else {
            write!(f, "{:?}, {:?}", self.0, self.1)
        }
    }
}

/// A `Value` can be a Constant, a UnaryOp, a StdFunc, or a PrintFunc.
#[derive(Debug, PartialEq)]
pub enum Value {
    EConst(f64),
    EUnaryOp(UnaryOp),
    EVar(String),
    #[cfg(feature = "unsafe-vars")]
    EUnsafeVar {
        name: String,
        ptr: *const f64,
    },

    EFunc {
        name: String,
        sargs: Vec<String>, // cap=2
        args: Vec<I>,       // cap=4
    },
}
use Value::*;

/// Unary Operators
#[derive(Debug, PartialEq)]
pub enum UnaryOp {
    EPos(I),
    ENeg(I),
    ENot(I),
    EParen(I),
}
use UnaryOp::*;

/// Binary Operators
#[derive(Debug, PartialEq, PartialOrd, Copy, Clone)]
pub enum BinaryOp {
    // Sorted in order of precedence (low-priority to high-priority):
    // Keep this order in-sync with evaler.rs.  (Search for 'rtol' and 'ltor'.)
    EOR = 1, // Lowest Priority
    EAND = 2,
    ENE = 3,
    EEQ = 4,
    EGTE = 5,
    ELTE = 6,
    EGT = 7,
    ELT = 8,
    EAdd = 9,
    ESub = 10,
    EMul = 11,
    EDiv = 12,
    EMod = 13,
    EExp = 14, // Highest Priority
}
use BinaryOp::*;

macro_rules! peek {
    ($bs:ident) => {
        $bs.first().copied()
    };
}
macro_rules! peek_n {
    ($bs:ident, $skip:literal) => {
        $bs.get($skip).copied()
    };
    ($bs:ident, $skip:ident) => {
        $bs.get($skip).copied()
    };
    ($bs:ident, $skip:expr) => {
        $bs.get($skip).copied()
    };
}
macro_rules! peek_is {
    ($bs:ident, $skip:literal, $val:literal) => {
        peek_n!($bs, $skip) == Some($val)
    };
    ($bs:ident, $skip:expr, $val:literal) => {
        peek_n!($bs, $skip) == Some($val)
    };
}

macro_rules! read {
    ($bs:ident) => {
        match $bs.first() {
            Some(b) => {
                *$bs = &$bs[1..];
                Ok(*b)
            }
            None => Err(Error::EOF),
        }
    };
    ($bs:ident, $parsing:literal) => {
        match $bs.first() {
            Some(b) => {
                *$bs = &$bs[1..];
                Ok(*b)
            }
            None => Err(Error::EofWhileParsing($parsing.to_string())),
        }
    };
}

macro_rules! skip {
    ($bs:ident) => {
        *$bs = &$bs[1..];
    };
}
macro_rules! skip_n {
    ($bs:ident, $n:literal) => {
        *$bs = &$bs[$n..];
    };
    ($bs:ident, $n:ident) => {
        *$bs = &$bs[$n..];
    };
}

macro_rules! is_space {
    ($b:ident) => {
        if $b > b' ' {
            false
        } else {
            $b == b' ' || $b == b'\n' || $b == b'\t' || $b == b'\r'
        }
    };
}
macro_rules! spaces {
    ($bs:ident) => {
        while let Some(b) = peek!($bs) {
            if !is_space!(b) { break }
            skip!($bs);  // We normally don't have long strings of whitespace, so it is more efficient to put this single-skip inside this loop rather than a skip_n afterwards.
        }
    };
}

fn is_varname_byte(b: u8, i: usize) -> bool {
    (b'A' <= b && b <= b'Z')
        || (b'a' <= b && b <= b'z')
        || b == b'_'
        || (i > 0 && (b'0' <= b && b <= b'9'))
}
fn is_varname_byte_opt(bo: Option<u8>, i: usize) -> bool {
    match bo {
        Some(b) => is_varname_byte(b, i),
        None => false,
    }
}

/// Use this function to parse an expression String. The `Ast` will be cleared first.
#[inline]
pub fn parse<'a, S: AsRef<str>>(expr_str: S, ast: &'a mut Ast) -> Result<(), Error> {
    let expr_str = expr_str.as_ref();
    ast.clear();
    if expr_str.len() > DEFAULT_EXPR_LEN_LIMIT {
        return Err(Error::TooLong);
    } // Restrict length for safety
    let mut bs = expr_str.as_bytes();
    read_expr(ast, &mut bs, 0, true).map(|_| ())
}

fn read_expr(ast: &mut Ast, bs: &mut &[u8], depth: usize, expect_eof: bool) -> Result<I, Error> {
    if depth > DEFAULT_EXPR_DEPTH_LIMIT {
        return Err(Error::TooDeep);
    }

    let first = read_value(ast, bs, depth)?;

    let mut pairs = Vec::<ExprPair>::with_capacity(8);
    loop {
        match read_binaryop(bs)? {
            None => break,
            Some(bop) => {
                let val = read_value(ast, bs, depth)?;
                pairs.push((bop, val));
            }
        }
    }
    spaces!(bs);
    if expect_eof && !bs.is_empty() {
        let bs_str = match from_utf8(bs) {
            Ok(s) => s,
            Err(..) => "Utf8Error while handling UnparsedTokensRemaining error",
        };
        return Err(Error::UnparsedTokensRemaining(bs_str.to_string()));
    }
    Ok(ast.push_expr(Expr(first, pairs))?)
}

fn read_value(ast: &mut Ast, bs: &mut &[u8], depth: usize) -> Result<Value, Error> {
    if depth > DEFAULT_EXPR_DEPTH_LIMIT {
        return Err(Error::TooDeep);
    }
    if let Some(c) = read_const(ast, bs)? {
        return Ok(EConst(c));
    }
    if let Some(u) = read_unaryop(ast, bs, depth)? {
        return Ok(EUnaryOp(u));
    }
    if let Some(c) = read_callable(ast, bs, depth)? {
        return Ok(c);
    }
    // Improve the precision of this error case:
    if bs.is_empty() {
        return Err(Error::EofWhileParsing("value".to_string()));
    }

    Err(Error::InvalidValue)
}

fn read_const(ast: &mut Ast, bs: &mut &[u8]) -> Result<Option<f64>, Error> {
    spaces!(bs);

    let mut toklen = 0;
    let mut sign_ok = true;
    let mut specials_ok = true;
    let mut suffix_ok = true;
    let mut saw_val = false;
    loop {
        match peek_n!(bs, toklen) {
            None => break,
            Some(b) => {
                if b'0' <= b && b <= b'9' || b == b'.' {
                    saw_val = true;
                    sign_ok = false;
                    specials_ok = false;
                    toklen = toklen + 1;
                } else if sign_ok && (b == b'-' || b == b'+') {
                    sign_ok = false;
                    toklen = toklen + 1;
                } else if saw_val && (b == b'e' || b == b'E') {
                    suffix_ok = false;
                    sign_ok = true;
                    toklen = toklen + 1;
                } else if specials_ok
                    && (b == b'N'
                        && peek_is!(bs, toklen + 1, b'a')
                        && peek_is!(bs, toklen + 2, b'N')
                        || b == b'i'
                            && peek_is!(bs, toklen + 1, b'n')
                            && peek_is!(bs, toklen + 2, b'f'))
                {
                    #[cfg(feature = "alpha-keywords")]
                    {
                        saw_val = true;
                        suffix_ok = false;
                        toklen = toklen + 3;
                    }
                    break;
                } else {
                    break;
                }
            }
        }
    }

    if !saw_val {
        return Ok(None);
    }

    let mut tok = unsafe { from_utf8_unchecked(&bs[..toklen]) };
    if suffix_ok {
        match peek_n!(bs, toklen) {
            None => (),
            Some(b) => {
                let (exp, suffixlen) = match b {
                    b'k' | b'K' => (3, 1),
                    b'M' => (6, 1),
                    b'G' => (9, 1),
                    b'T' => (12, 1),
                    b'm' => (-3, 1),
                    b'u' | b'\xb5' => (-6, 1), // ASCII-encoded 'µ'
                    b'\xc2' if peek_is!(bs, toklen + 1, b'\xb5') => (-6, 2), // UTF8-encoded 'µ'
                    b'n' => (-9, 1),
                    b'p' => (-12, 1),
                    _ => (0, 0),
                };
                if exp != 0 {
                    ast.char_buf.clear();
                    ast.char_buf.push_str(tok);
                    ast.char_buf.push('e');
                    ast.char_buf.push_str(&exp.to_string());
                    tok = &ast.char_buf;

                    toklen = toklen + suffixlen;
                }
            }
        }
    }

    let val = tok
        .parse::<f64>()
        .map_err(|_| Error::ParseF64(tok.to_string()))?;
    skip_n!(bs, toklen);

    Ok(Some(val))
}

fn read_unaryop(ast: &mut Ast, bs: &mut &[u8], depth: usize) -> Result<Option<UnaryOp>, Error> {
    spaces!(bs);
    match peek!(bs) {
        None => Ok(None), // Err(KErr::new("EOF at UnaryOp position")), -- Instead of erroring, let the higher level decide what to do.
        Some(b) => match b {
            b'+' => {
                skip!(bs);
                let v = read_value(ast, bs, depth + 1)?;
                Ok(Some(EPos(ast.push_val(v)?)))
            }
            b'-' => {
                skip!(bs);
                let v = read_value(ast, bs, depth + 1)?;
                Ok(Some(ENeg(ast.push_val(v)?)))
            }
            b'(' => {
                skip!(bs);
                let xi = read_expr(ast, bs, depth + 1, false)?;
                spaces!(bs);
                if read!(bs, "parentheses")? != b')' {
                    return Err(Error::Expected(")".to_string()));
                }
                Ok(Some(EParen(xi)))
            }
            b'[' => {
                skip!(bs);
                let xi = read_expr(ast, bs, depth + 1, false)?;
                spaces!(bs);
                if read!(bs, "square brackets")? != b']' {
                    return Err(Error::Expected("]".to_string()));
                }
                Ok(Some(EParen(xi)))
            }
            b'!' => {
                skip!(bs);
                let v = read_value(ast, bs, depth + 1)?;
                Ok(Some(ENot(ast.push_val(v)?)))
            }
            _ => Ok(None),
        },
    }
}

fn read_binaryop(bs: &mut &[u8]) -> Result<Option<BinaryOp>, Error> {
    spaces!(bs);
    match peek!(bs) {
        None => Ok(None), // Err(KErr::new("EOF")), -- EOF is usually OK in a BinaryOp position.
        Some(b) => match b {
            b'+' => {
                skip!(bs);
                Ok(Some(EAdd))
            }
            b'-' => {
                skip!(bs);
                Ok(Some(ESub))
            }
            b'*' => {
                skip!(bs);
                Ok(Some(EMul))
            }
            b'/' => {
                skip!(bs);
                Ok(Some(EDiv))
            }
            b'%' => {
                skip!(bs);
                Ok(Some(EMod))
            }
            b'^' => {
                skip!(bs);
                Ok(Some(EExp))
            }
            b'<' => {
                skip!(bs);
                if peek_is!(bs, 0, b'=') {
                    skip!(bs);
                    Ok(Some(ELTE))
                } else {
                    Ok(Some(ELT))
                }
            }
            b'>' => {
                skip!(bs);
                if peek_is!(bs, 0, b'=') {
                    skip!(bs);
                    Ok(Some(EGTE))
                } else {
                    Ok(Some(EGT))
                }
            }
            b'=' if peek_is!(bs, 1, b'=') => {
                skip_n!(bs, 2);
                Ok(Some(EEQ))
            }
            b'!' if peek_is!(bs, 1, b'=') => {
                skip_n!(bs, 2);
                Ok(Some(ENE))
            }
            #[cfg(feature = "alpha-keywords")]
            b'o' if peek_is!(bs, 1, b'r') => {
                skip_n!(bs, 2);
                Ok(Some(EOR))
            }
            b'|' if peek_is!(bs, 1, b'|') => {
                skip_n!(bs, 2);
                Ok(Some(EOR))
            }
            #[cfg(feature = "alpha-keywords")]
            b'a' if peek_is!(bs, 1, b'n') && peek_is!(bs, 2, b'd') => {
                skip_n!(bs, 3);
                Ok(Some(EAND))
            }
            b'&' if peek_is!(bs, 1, b'&') => {
                skip_n!(bs, 2);
                Ok(Some(EAND))
            }
            _ => Ok(None),
        },
    }
}

fn read_callable(ast: &mut Ast, bs: &mut &[u8], depth: usize) -> Result<Option<Value>, Error> {
    match read_varname(bs)? {
        None => Ok(None),
        Some(varname) => {
            match read_open_parenthesis(bs)? {
                None => {
                    // VarNames without Parenthesis are always treated as custom 0-arg functions.

                    #[cfg(feature = "unsafe-vars")]
                    match ast.unsafe_vars.get(&varname) {
                        None => Ok(Some(EVar(varname))),
                        Some(&ptr) => Ok(Some(EUnsafeVar { name: varname, ptr })),
                    }

                    #[cfg(not(feature = "unsafe-vars"))]
                    Ok(Some(EVar(varname)))
                }
                Some(open_parenth) => {
                    // VarNames with Parenthesis are first matched against builtins, then custom.
                    Ok(Some(read_func(varname, ast, bs, depth, open_parenth)?))
                }
            }
        }
    }
}

fn read_varname(bs: &mut &[u8]) -> Result<Option<String>, Error> {
    spaces!(bs);

    let mut toklen = 0;
    while is_varname_byte_opt(peek_n!(bs, toklen), toklen) {
        toklen = toklen + 1;
    }

    if toklen == 0 {
        return Ok(None);
    }

    let out = unsafe { from_utf8_unchecked(&bs[..toklen]) }.to_string();
    skip_n!(bs, toklen);
    Ok(Some(out))
}

fn read_open_parenthesis(bs: &mut &[u8]) -> Result<Option<u8>, Error> {
    spaces!(bs);

    match peek!(bs) {
        Some(b'(') | Some(b'[') => Ok(Some(match read!(bs) {
            Ok(b) => b,
            Err(..) => return Err(Error::Unreachable),
        })),
        _ => Ok(None),
    }
}

fn read_func(
    fname: String,
    ast: &mut Ast,
    bs: &mut &[u8],
    depth: usize,
    open_parenth: u8,
) -> Result<Value, Error> {
    let close_parenth = match open_parenth {
        b'(' => b')',
        b'[' => b']',
        _ => return Err(Error::Expected("'(' or '['".to_string())),
    };
    let mut sargs = Vec::<String>::with_capacity(2);
    let mut args = Vec::<I>::with_capacity(4);

    loop {
        spaces!(bs);
        match peek!(bs) {
            Some(b) => {
                if b == close_parenth {
                    skip!(bs);
                    break;
                }
            }
            None => return Err(Error::EofWhileParsing(fname)),
        }
        if !args.is_empty() {
            match read!(bs) {
                Ok(b',') => {}
                _ => return Err(Error::Expected("','".to_string())),
            }
        } else {
            if let Some(s) = read_string(bs)? {
                sargs.push(s);
                println!("{:?}", sargs);
                match read!(bs) {
                    Ok(b',') => {}
                    _ => {
                        return Err(Error::Expected("','".to_string()));
                    }
                }
                continue;
            }
        }
        args.push(read_expr(ast, bs, depth + 1, false)?);
    }

    #[cfg(feature = "unsafe-vars")]
    match ast.unsafe_vars.get(&fname) {
        None => Ok(EFunc {
            name: fname,
            sargs,
            args,
        }),
        Some(&ptr) => Ok(EUnsafeVar { name: fname, ptr }),
    }

    #[cfg(not(feature = "unsafe-vars"))]
    Ok(EFunc {
        name: fname,
        sargs,
        args,
    })
}

fn read_string(bs: &mut &[u8]) -> Result<Option<String>, Error> {
    spaces!(bs);

    match peek!(bs) {
        None => {
            return Err(Error::EofWhileParsing(
                "opening quote of string".to_string(),
            ))
        }

        Some(b'"') => {
            skip!(bs);
        }
        Some(_) => return Ok(None),
    }

    let mut prev = b' ';
    let mut toklen = 0;
    while match peek_n!(bs, toklen) {
        None => false,
        Some(b'"') => prev == b'\\',
        Some(p) => {
            prev = p;
            true
        }
    } {
        toklen = toklen + 1;
    }

    let out =
        from_utf8(&bs[..toklen]).map_err(|_| Error::Utf8ErrorWhileParsing("string".to_string()))?;
    skip_n!(bs, toklen);
    match read!(bs) {
        Err(Error::EOF) => Err(Error::EofWhileParsing("string".to_string())),
        Err(_) => Err(Error::Unreachable),
        Ok(b'"') => Ok(Some(out.to_string())),
        Ok(_) => Err(Error::Unreachable),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::Ast;

    #[test]
    fn test_util() {
        match (|| -> Result<(), Error> {
            let bsarr = [1, 2, 3];
            let bs = &mut &bsarr[..];

            assert_eq!(peek!(bs), Some(1));
            assert_eq!(peek_n!(bs, 1), Some(2));
            assert_eq!(peek_n!(bs, 2), Some(3));
            assert_eq!(peek_n!(bs, 3), None);

            assert_eq!(read!(bs)?, 1);
            skip!(bs);
            assert_eq!(read!(bs)?, 3);
            match read!(bs).err() {
                Some(Error::EOF) => {}
                _ => panic!("I expected an EOF"),
            }

            Ok(())
        })() {
            Ok(_) => {}
            Err(_) => {
                unimplemented!();
            }
        }

        assert!((&[0u8; 0]).is_empty());
        assert!(!(&[1]).is_empty());
        assert!((b"").is_empty());
        assert!(!(b"x").is_empty());

        let b = b' ';
        assert!(is_space!(b));
        let b = b'\t';
        assert!(is_space!(b));
        let b = b'\r';
        assert!(is_space!(b));
        let b = b'\n';
        assert!(is_space!(b));
        let b = b'a';
        assert!(!is_space!(b));
        let b = b'1';
        assert!(!is_space!(b));
        let b = b'.';
        assert!(!is_space!(b));

        {
            let bsarr = b"  abc 123   ";
            let bs = &mut &bsarr[..];
            spaces!(bs);
            assert_eq!(bs, b"abc 123   ");
        }
    }

    #[test]
    fn test_priv_tests() {
        assert!(is_varname_byte_opt(Some(b'a'), 0));

        let mut ast = Ast::new();

        {
            let bsarr = b"12.34";
            let bs = &mut &bsarr[..];
            assert_eq!(read_value(&mut ast, bs, 0), Ok(EConst(12.34)));
        }
    }
}
