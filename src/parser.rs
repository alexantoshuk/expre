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
//! Func: VarName((String)*, (Expr,)*)?  ||  VarName[(Expr,)*]?
//!
//! PrintFunc: print(ExprOrString,*)
//!
//! String: ".*"
//! ```

use crate::error::Error;
use crate::write_indexed_list;
use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display};
use std::ops::Deref;
use std::str::{from_utf8, from_utf8_unchecked};

pub const DEFAULT_EXPR_LEN_LIMIT: usize = 1024 * 10;
pub const DEFAULT_EXPR_DEPTH_LIMIT: usize = 32;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct I(pub usize);

impl Debug for I {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, ":{}", self.0)
    }
}

impl Deref for I {
    type Target = usize;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<usize> for I {
    #[inline]
    fn from(value: usize) -> Self {
        I(value)
    }
}

impl From<I> for usize {
    #[inline]
    fn from(value: I) -> Self {
        value.0
    }
}

/// Use this function to parse an expression String. The `Ast` will be cleared first.
#[inline]
pub fn parse<S: AsRef<str>>(expr_str: S, ast: &mut Ast) -> Result<(), Error> {
    ast.parse(expr_str)
}

pub trait ParseExpr {
    fn parse_expr(&self, ast: &mut Ast) -> Result<(), Error>;
}

impl<S: AsRef<str>> ParseExpr for S {
    #[inline]
    fn parse_expr(&self, ast: &mut Ast) -> Result<(), Error> {
        ast.parse(self)
    }
}

pub struct Ast {
    pub(crate) exprs: Vec<Expr>,
    local_vars: BTreeMap<String, I>,
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
            local_vars: BTreeMap::new(),
        }
    }

    #[inline]
    pub fn from_str<S: AsRef<str>>(expr_str: S) -> Result<Ast, Error> {
        let mut ast = Self::new();
        ast.parse(expr_str).map(|_| ast)
    }

    /// Use this function to parse an expression String. The `Ast` will be cleared first.
    #[inline]
    pub fn parse<S: AsRef<str>>(&mut self, expr_str: S) -> Result<(), Error> {
        let expr_str = expr_str.as_ref();
        self.clear();
        if expr_str.len() > DEFAULT_EXPR_LEN_LIMIT {
            return Err(Error::TooLong);
        } // Restrict length for safety
        let mut bs = expr_str.as_bytes();
        loop {
            self.read_expr(&mut bs, 0, true).map(|_| ())?;
            if bs.is_empty() {
                break;
            }
            skip(&mut bs);
        }
        Ok(())
    }

    /// Clears all data from [`Ast`](struct.ParseAST.html) and [`Ast`](struct.CompileAST.html).
    #[inline]
    pub fn clear(&mut self) {
        self.exprs.clear();
        self.local_vars.clear();
    }

    /// Returns a reference to the [`Expr`](../parser/struct.Expr.html)
    /// located at `expr_i` within the `Ast.exprs'.
    ///
    #[inline]
    pub fn get_expr(&self, expr_i: I) -> &Expr {
        // I'm using this non-panic match structure to boost performance:
        self.exprs.get(expr_i.0).unwrap()
    }

    #[inline]
    pub fn last(&self) -> Option<&Expr> {
        self.exprs.last()
    }

    /// Returns a reference to the [`Value`](../parser/enum.Value.html)
    /// located at `val_i` within the `Ast.vals'.
    ///
    #[inline]
    pub fn get_val(&self, val_i: I) -> &Value {
        // self.vals.get(val_i).unwrap()
        &self.exprs.get(val_i.0).unwrap().0
    }

    /// Appends an `Expr` to `Ast.0`.
    ///
    #[inline]
    pub fn push_expr(&mut self, expr: Expr) -> I {
        let i = self.exprs.len();

        self.exprs.push(expr);
        i.into()
    }

    #[inline]
    pub fn push_val(&mut self, val: Value) -> I {
        let i = self.exprs.len();

        self.exprs.push(Expr(val, vec![]));
        i.into()
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
#[derive(PartialEq)]
pub enum Value {
    EConst(f64),
    EUnaryOp(UnaryOp),
    EVar(String),
    ERef(I),
    EAssignOp(String, AssignOp),
    EFunc {
        name: String,
        sargs: Vec<String>, // cap=2
        args: Vec<I>,       // cap=4
    },
    // Pass,
}
use Value::*;

impl Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            EConst(v) => write!(f, "EConst({:?})", v),
            EUnaryOp(uop) => write!(f, "{:?}", uop),
            EVar(s) => write!(f, "EVar({:?})", s),
            ERef(i) => write!(f, "ERef({:?})", i),
            EFunc {
                name,
                sargs, // cap=2
                args,  // cap=4
            } => write!(f, "EFunc({:?}, {:?}, {:?})", name, sargs, args),
            _ => Ok(()),
        }
    }
}

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
    // ESemi = 0,
    EOr = 1, // Lowest Priority
    EAnd = 2,
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

#[derive(Debug, PartialEq, PartialOrd, Copy, Clone)]
pub enum AssignOp {
    // Sorted in order of precedence (low-priority to high-priority):
    // Keep this order in-sync with evaler.rs.  (Search for 'rtol' and 'ltor'.)
    EAssign,
    EAddAssign,
    ESubAssign,
    EMulAssign,
    EDivAssign,
    EModAssign,
    EExpAssign,
}

impl Display for AssignOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            EAssign => write!(f, "="),
            EAddAssign => write!(f, "+="),
            ESubAssign => write!(f, "-="),
            EMulAssign => write!(f, "*="),
            EDivAssign => write!(f, "/="),
            EModAssign => write!(f, "%="),
            EExpAssign => write!(f, "^="),
        }
    }
}
use AssignOp::*;

/// Used by the `print()` function.  Can hold an `Expression` or a `String`.
#[derive(Debug, PartialEq)]
pub enum ExprOrString {
    EExpr(I),
    EStr(String), // cap=64
}
use ExprOrString::{EExpr, EStr};

impl Ast {
    #[inline]
    fn read_expr(&mut self, bs: &mut &[u8], depth: usize, expect_eof: bool) -> Result<I, Error> {
        if depth > DEFAULT_EXPR_DEPTH_LIMIT {
            return Err(Error::TooDeep);
        }

        let first = self.read_value(bs, depth)?;

        if let EAssignOp(varname, aop) = &first {
            if !expect_eof {
                return Err(Error::InvalidSyntax(aop.to_string()));
            }
            let i = self.read_expr(bs, depth, false)?;
            let e = if let Some(i) = self.local_vars.get(varname) {
                ERef(*i)
            } else {
                EVar(varname.into()) //TODO: assignop with no var exists? syntax error?
            };
            let i = match aop {
                EAddAssign => self.push_expr(Expr(e, vec![(EAdd, EUnaryOp(EParen(i)))])),
                ESubAssign => self.push_expr(Expr(e, vec![(ESub, EUnaryOp(EParen(i)))])),
                EMulAssign => self.push_expr(Expr(e, vec![(EMul, EUnaryOp(EParen(i)))])),
                EDivAssign => self.push_expr(Expr(e, vec![(EDiv, EUnaryOp(EParen(i)))])),
                EModAssign => self.push_expr(Expr(e, vec![(EMod, EUnaryOp(EParen(i)))])),
                EExpAssign => self.push_expr(Expr(e, vec![(EExp, EUnaryOp(EParen(i)))])),
                _ => i,
            };

            self.local_vars.insert(varname.clone(), i);
            return Ok(0.into());
        }

        let mut pairs = Vec::<ExprPair>::with_capacity(8);
        loop {
            match read_binaryop(bs)? {
                None => break,
                Some(bop) => {
                    let val = self.read_value(bs, depth)?;
                    pairs.push((bop, val));
                }
            }
        }

        spaces(bs);

        if expect_eof && !bs.is_empty() {
            let bs_str = match from_utf8(bs) {
                Ok(s) => s,
                Err(..) => "Utf8Error while handling UnparsedTokensRemaining error",
            };
            return Err(Error::UnparsedTokensRemaining(bs_str.to_string()));
        }
        let i = self.push_expr(Expr(first, pairs));

        Ok(i)
    }

    #[inline]
    fn read_expr_or_string(&mut self, bs: &mut &[u8], depth: usize) -> Result<ExprOrString, Error> {
        if let Some(s) = read_string(bs)? {
            Ok(EStr(s))
        } else {
            Ok(EExpr(self.read_expr(bs, depth + 1, false)?))
        }
    }

    #[inline]
    fn read_value(&mut self, bs: &mut &[u8], depth: usize) -> Result<Value, Error> {
        if depth > DEFAULT_EXPR_DEPTH_LIMIT {
            return Err(Error::TooDeep);
        }
        if let Some(c) = read_const(bs)? {
            return Ok(EConst(c));
        }
        if let Some(u) = self.read_unaryop(bs, depth)? {
            return Ok(EUnaryOp(u));
        }
        if let Some(c) = self.read_callable(bs, depth)? {
            return Ok(c);
        }
        // Improve the precision of this error case:
        if bs.is_empty() {
            return Err(Error::EofWhileParsing("value".to_string()));
        }

        Err(Error::InvalidValue)
    }

    #[inline]
    fn read_unaryop(&mut self, bs: &mut &[u8], depth: usize) -> Result<Option<UnaryOp>, Error> {
        spaces(bs);
        match peek(bs) {
            None => Ok(None), // Err(KErr::new("EOF at UnaryOp position")), -- Instead of erroring, let the higher level decide what to do.
            Some(b) => match b {
                b'+' => {
                    skip(bs);
                    let v = self.read_value(bs, depth + 1)?;
                    Ok(Some(EPos(self.push_val(v))))
                }
                b'-' => {
                    skip(bs);
                    let v = self.read_value(bs, depth + 1)?;
                    Ok(Some(ENeg(self.push_val(v))))
                }
                b'(' => {
                    skip(bs);
                    let xi = self.read_expr(bs, depth + 1, false)?;
                    spaces(bs);
                    if read(bs).ok_or(Error::EofWhileParsing("parentheses".into()))? != b')' {
                        return Err(Error::Expected(")".to_string()));
                    }
                    Ok(Some(EParen(xi)))
                }
                b'[' => {
                    skip(bs);
                    let xi = self.read_expr(bs, depth + 1, false)?;
                    spaces(bs);
                    if read(bs).ok_or(Error::EofWhileParsing("square brackets".into()))? != b']' {
                        return Err(Error::Expected("]".to_string()));
                    }
                    Ok(Some(EParen(xi)))
                }
                b'!' => {
                    skip(bs);
                    let v = self.read_value(bs, depth + 1)?;
                    Ok(Some(ENot(self.push_val(v))))
                }
                _ => Ok(None),
            },
        }
    }

    #[inline]
    fn read_callable(&mut self, bs: &mut &[u8], depth: usize) -> Result<Option<Value>, Error> {
        match read_varname(bs)? {
            None => Ok(None),
            Some(varname) => {
                if let Some(open_parenth) = read_open_parenthesis(bs)? {
                    Ok(Some(self.read_func(varname, bs, depth, open_parenth)?))
                } else if let Some(aop) = read_assignop(bs)? {
                    Ok(Some(EAssignOp(varname, aop)))
                } else if let Some(i) = self.local_vars.get(&varname) {
                    Ok(Some(ERef(*i)))
                } else {
                    Ok(Some(EVar(varname)))
                }
            }
        }
    }

    #[inline]
    fn read_func(
        &mut self,
        fname: String,
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
            spaces(bs);
            match peek(bs) {
                Some(b) => {
                    if b == close_parenth {
                        skip(bs);
                        break;
                    }
                }
                None => return Err(Error::EofWhileParsing(fname)),
            }
            if !args.is_empty() {
                match read(bs) {
                    Some(b',') => {}
                    _ => return Err(Error::Expected("','".to_string())),
                }
            } else {
                if let Some(s) = read_string(bs)? {
                    sargs.push(s);

                    match read(bs) {
                        Some(b',') => {}
                        _ => {
                            return Err(Error::Expected("','".to_string()));
                        }
                    }
                    continue;
                }
            }
            args.push(self.read_expr(bs, depth + 1, false)?);
        }

        Ok(EFunc {
            name: fname,
            sargs,
            args,
        })
    }
}

#[inline]
fn peek(bs: &[u8]) -> Option<u8> {
    bs.first().copied()
}

#[inline]
fn peek_n(bs: &[u8], n: usize) -> Option<u8> {
    bs.get(n).copied()
}

#[inline]
fn peek_is(bs: &[u8], n: usize, b: u8) -> bool {
    bs.get(n).copied() == Some(b)
}

#[inline]
fn skip(bs: &mut &[u8]) {
    *bs = &bs[1..];
}

#[inline]
fn skip_n(bs: &mut &[u8], n: usize) {
    *bs = &bs[n..];
}

#[inline]
fn is_space(b: u8) -> bool {
    if b > b' ' {
        false
    } else {
        b == b' ' || b == b'\n' || b == b'\t' || b == b'\r'
    }
}

#[inline]
fn spaces(bs: &mut &[u8]) {
    while let Some(b) = peek(bs) {
        if !is_space(b) {
            break;
        }
        skip(bs); // We normally don't have long strings of whitespace, so it is more efficient to put this single-skip inside this loop rather than a skip_n afterwards.
    }
}

#[inline]
fn read(bs: &mut &[u8]) -> Option<u8> {
    bs.first().map(|b| {
        *bs = &bs[1..];
        *b
    })
}

#[inline]
fn read_const(bs: &mut &[u8]) -> Result<Option<f64>, Error> {
    spaces(bs);

    let mut toklen = 0;
    let mut sign_ok = true;
    let mut saw_val = false;
    loop {
        match peek_n(bs, toklen) {
            None => break,
            Some(b) => {
                if b'0' <= b && b <= b'9' || b == b'.' {
                    saw_val = true;
                    sign_ok = false;
                    toklen = toklen + 1;
                } else if sign_ok && (b == b'-' || b == b'+') {
                    sign_ok = false;
                    toklen = toklen + 1;
                } else if saw_val && (b == b'e' || b == b'E') {
                    sign_ok = true;
                    toklen = toklen + 1;
                } else {
                    break;
                }
            }
        }
    }

    if !saw_val {
        return Ok(None);
    }

    let tok = unsafe { from_utf8_unchecked(&bs[..toklen]) };
    let val = tok
        .parse::<f64>()
        .map_err(|_| Error::ParseF64(tok.to_string()))?;
    skip_n(bs, toklen);

    Ok(Some(val))
}

#[inline]
fn read_binaryop(bs: &mut &[u8]) -> Result<Option<BinaryOp>, Error> {
    spaces(bs);
    match peek(bs) {
        None => Ok(None),
        Some(b) => match b {
            b'+' => {
                skip(bs);
                Ok(Some(EAdd))
            }
            b'-' => {
                skip(bs);
                Ok(Some(ESub))
            }
            b'*' => {
                skip(bs);
                Ok(Some(EMul))
            }
            b'/' => {
                skip(bs);
                Ok(Some(EDiv))
            }
            b'%' => {
                skip(bs);
                Ok(Some(EMod))
            }
            b'^' => {
                skip(bs);
                Ok(Some(EExp))
            }
            b'<' => {
                skip(bs);
                if peek_is(bs, 0, b'=') {
                    skip(bs);
                    Ok(Some(ELTE))
                } else {
                    Ok(Some(ELT))
                }
            }
            b'>' => {
                skip(bs);
                if peek_is(bs, 0, b'=') {
                    skip(bs);
                    Ok(Some(EGTE))
                } else {
                    Ok(Some(EGT))
                }
            }
            b'=' if peek_is(bs, 1, b'=') => {
                skip_n(bs, 2);
                Ok(Some(EEQ))
            }
            b'!' if peek_is(bs, 1, b'=') => {
                skip_n(bs, 2);
                Ok(Some(ENE))
            }
            b'|' if peek_is(bs, 1, b'|') => {
                skip_n(bs, 2);
                Ok(Some(EOr))
            }

            b'&' if peek_is(bs, 1, b'&') => {
                skip_n(bs, 2);
                Ok(Some(EAnd))
            }
            b';' | b')' | b',' => Ok(None),
            _ => Err(Error::InvalidSyntax(format!("{}", b as char))),
        },
    }
}

#[inline]
fn read_assignop(bs: &mut &[u8]) -> Result<Option<AssignOp>, Error> {
    spaces(bs);
    match peek(bs) {
        None => Ok(None), // Err(KErr::new("EOF")), -- EOF is usually OK in a BinaryOp position.
        Some(b) => match b {
            b'=' if !peek_is(bs, 1, b'=') => {
                skip(bs);
                Ok(Some(EAssign))
            }

            b'+' if peek_is(bs, 1, b'=') => {
                skip_n(bs, 2);
                Ok(Some(EAddAssign))
            }
            _ => Ok(None),
        },
    }
}

#[inline]
fn read_varname(bs: &mut &[u8]) -> Result<Option<String>, Error> {
    spaces(bs);

    let mut toklen = 0;
    while is_varname_byte_opt(peek_n(bs, toklen), toklen) {
        toklen = toklen + 1;
    }

    if toklen == 0 {
        return Ok(None);
    }

    let out = unsafe { from_utf8_unchecked(&bs[..toklen]) }.to_string();
    skip_n(bs, toklen);
    Ok(Some(out))
}

#[inline]
fn read_open_parenthesis(bs: &mut &[u8]) -> Result<Option<u8>, Error> {
    spaces(bs);

    match peek(bs) {
        Some(b'(') | Some(b'[') => Ok(Some(read(bs).ok_or(Error::Unreachable)?)),
        _ => Ok(None),
    }
}

#[inline]
fn read_string(bs: &mut &[u8]) -> Result<Option<String>, Error> {
    spaces(bs);

    match peek(bs) {
        None => {
            return Err(Error::EofWhileParsing(
                "opening quote of string".to_string(),
            ))
        }

        Some(b'"') => {
            skip(bs);
        }
        Some(_) => return Ok(None),
    }

    let mut prev = b' ';
    let mut toklen = 0;
    while match peek_n(bs, toklen) {
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

    skip_n(bs, toklen);
    match read(bs) {
        None => Err(Error::EofWhileParsing("string".to_string())),
        Some(b'"') => Ok(Some(out.to_string())),
        Some(_) => Err(Error::Unreachable),
    }
}

#[inline]
fn is_varname_byte(b: u8, i: usize) -> bool {
    (b'A' <= b && b <= b'Z')
        || (b'a' <= b && b <= b'z')
        || b == b'_'
        || (i > 0 && (b'0' <= b && b <= b'9'))
}

#[inline]
fn is_varname_byte_opt(bo: Option<u8>, i: usize) -> bool {
    match bo {
        Some(b) => is_varname_byte(b, i),
        None => false,
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

            assert_eq!(peek(bs), Some(1));
            assert_eq!(peek_n(bs, 1), Some(2));
            assert_eq!(peek_n(bs, 2), Some(3));
            assert_eq!(peek_n(bs, 3), None);

            assert_eq!(read(bs).unwrap(), 1);
            skip(bs);
            assert_eq!(read(bs).unwrap(), 3);
            match read(bs) {
                None => {}
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
        assert!(is_space(b));
        let b = b'\t';
        assert!(is_space(b));
        let b = b'\r';
        assert!(is_space(b));
        let b = b'\n';
        assert!(is_space(b));
        let b = b'a';
        assert!(!is_space(b));
        let b = b'1';
        assert!(!is_space(b));
        let b = b'.';
        assert!(!is_space(b));

        {
            let bsarr = b"  abc 123   ";
            let bs = &mut &bsarr[..];
            spaces(bs);
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
            assert_eq!(ast.read_value(bs, 0), Ok(EConst(12.34)));
        }
    }
}
