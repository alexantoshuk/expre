use crate::display_indexed_list;
use crate::error::Error;
use crate::tokens::*;
use core::str;
use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display};
use std::str::{from_utf8, from_utf8_unchecked};
pub const DEFAULT_EXPR_LEN_LIMIT: usize = 1024 * 10;
pub const DEFAULT_EXPR_DEPTH_LIMIT: usize = 32;

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
    local_vars: BTreeMap<String, ECV>,
}

impl Ast {
    /// Creates a new default-sized `Ast`.
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(8)
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
    pub fn get_expr(&self, expr_i: usize) -> &Expr {
        // F'm using this non-panic match structure to boost performance:
        self.exprs.get(expr_i).unwrap()
    }

    #[inline]
    pub fn last(&self) -> Option<&Expr> {
        self.exprs.last()
    }

    /// Returns a reference to the [`Value`](../parser/enum.Value.html)
    /// located at `val_i` within the `Ast.vals'.
    ///
    #[inline]
    pub fn get_val(&self, val_i: usize) -> &Value {
        &self.exprs.get(val_i).unwrap().0
    }

    /// Appends an `Expr` to `Ast.0`.
    ///
    #[inline]
    pub fn push_expr(&mut self, expr: Expr) -> usize {
        let i = self.exprs.len();

        self.exprs.push(expr);
        i
    }

    #[inline]
    pub fn push_val(&mut self, val: Value) -> usize {
        let i = self.exprs.len();
        self.exprs.push(Expr(val, vec![]));
        i
    }
}

impl Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:?}", self.exprs)
    }
}
impl Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        display_indexed_list(f, &self.exprs)?;
        Ok(())
    }
}

pub(crate) type ExprPair = (BinaryOp, Value);

/// An `Expr` is the top node of a parsed Ast.
///
/// It can be `compile()`d or `eval()`d.
#[derive(PartialEq, Debug)]
pub struct Expr(
    pub Value,
    pub Vec<ExprPair>, // cap=8
);

impl Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let Expr(val, pairs) = self;
        if pairs.is_empty() {
            write!(f, "{val}")
        } else {
            write!(f, "{val}")?;
            for (op, val) in pairs {
                write!(f, " {op} {val}")?;
            }
            Ok(())
        }
    }
}

impl Ast {
    #[inline]
    fn read_expr(&mut self, bs: &mut &[u8], depth: usize, expect_eof: bool) -> Result<ECV, Error> {
        if depth > DEFAULT_EXPR_DEPTH_LIMIT {
            return Err(Error::TooDeep);
        }

        let first = self.read_value(bs, depth)?;

        if let AssignOp(varname, aop) = &first {
            if !expect_eof {
                return Err(Error::InvalidSyntax(format!(
                    "{}",
                    str::from_utf8(bs).unwrap()
                )));
            }

            let ecv = self.read_expr(bs, depth, false)?;
            if aop == &EAssign {
                self.local_vars.insert(varname.clone(), ecv.clone());
                return Ok(ecv);
            }

            let e = if let Some(ecv) = self.local_vars.get(varname) {
                ECV(ecv.clone())
            } else {
                ECV(Var(varname.into()))
            };

            let i = match aop {
                EAddAssign => self.push_expr(Expr(e, vec![(Add, Value::ECV(ecv))])),
                ESubAssign => self.push_expr(Expr(e, vec![(Sub, Value::ECV(ecv))])),
                EMulAssign => self.push_expr(Expr(e, vec![(Mul, Value::ECV(ecv))])),
                EDivAssign => self.push_expr(Expr(e, vec![(Div, Value::ECV(ecv))])),
                EModAssign => self.push_expr(Expr(e, vec![(Rem, Value::ECV(ecv))])),
                EExpAssign => self.push_expr(Expr(e, vec![(Exp, Value::ECV(ecv))])),
                _ => unreachable!(),
            };
            let ecv = E(i);
            self.local_vars.insert(varname.clone(), ecv.clone());
            return Ok(ecv);
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

        match first {
            ECV(ecv) if (!expect_eof && pairs.len() == 0) => Ok(ecv),
            _ => {
                let i = self.push_expr(Expr(first, pairs));
                Ok(E(i))
            }
        }
    }

    // #[inline]
    // fn read_expr_or_string(&mut self, bs: &mut &[u8], depth: usize) -> Result<ExprOrString, Error> {
    //     if let Some(s) = read_string(bs)? {
    //         Ok(EStr(s))
    //     } else {
    //         Ok(EExpr(self.read_expr(bs, depth + 1, false)?))
    //     }
    // }

    #[inline]
    fn read_value(&mut self, bs: &mut &[u8], depth: usize) -> Result<Value, Error> {
        if depth > DEFAULT_EXPR_DEPTH_LIMIT {
            return Err(Error::TooDeep);
        }

        if let Some(c) = read_const(bs)? {
            return Ok(ECV(Const(c)));
        }
        if let Some(u) = self.read_unaryop(bs, depth)? {
            return Ok(UnaryOp(u));
        }
        if let Some(p) = self.read_parentheses(bs, depth)? {
            return Ok(p);
        }
        if let Some(c) = self.read_callable(bs, depth)? {
            return Ok(c);
        }
        if let Some(v) = self.read_vector(bs, depth)? {
            return Ok(v);
        }

        // Improve the precision of this error case:
        if bs.is_empty() {
            return Err(Error::EofWhileParsing("value".to_string()));
        }

        Err(Error::InvalidSyntax(format!(
            "{}",
            str::from_utf8(bs).unwrap()
        )))
    }

    #[inline]
    fn value_to_icv(&mut self, v: Value) -> ECV {
        if let Value::ECV(ecv) = v {
            ecv
        } else {
            let i = self.push_val(v);
            E(i)
        }
    }

    #[inline]
    fn read_unaryop(&mut self, bs: &mut &[u8], depth: usize) -> Result<Option<UnaryOp>, Error> {
        spaces(bs);
        match peek(bs) {
            None => Ok(None), // Err(KErr::new("EOF at UnaryOp position")), -- Instead of erroring, let the higher level decide what to do.
            Some(b) => match b {
                b'-' => {
                    skip(bs);
                    let v = self.read_value(bs, depth + 1)?;
                    let ecv = self.value_to_icv(v);
                    Ok(Some(Neg(ecv)))
                }

                b'!' => {
                    skip(bs);
                    let v = self.read_value(bs, depth + 1)?;
                    let ecv = self.value_to_icv(v);
                    Ok(Some(Not(ecv)))
                }
                _ => Ok(None),
            },
        }
    }

    #[inline]
    fn read_parentheses(&mut self, bs: &mut &[u8], depth: usize) -> Result<Option<Value>, Error> {
        spaces(bs);
        match peek(bs) {
            None => Ok(None), // Err(KErr::new("EOF at UnaryOp position")), -- Instead of erroring, let the higher level decide what to do.
            Some(b) => match b {
                b'(' => {
                    skip(bs);
                    let xi = self.read_expr(bs, depth + 1, false)?;
                    spaces(bs);
                    if read(bs).ok_or(Error::EofWhileParsing(")".into()))? != b')' {
                        return Err(Error::ExpectedClosingParen(format!(
                            "{}",
                            str::from_utf8(bs).unwrap()
                        )));
                    }
                    Ok(Some(Value::ECV(xi)))
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
                if let Some(b'(') = read_open_parenthesis(bs)? {
                    Ok(Some(self.read_func(varname, bs, depth)?))
                } else if let Some(aop) = read_assignop(bs)? {
                    Ok(Some(AssignOp(varname, aop)))
                } else if let Some(ecv) = self.local_vars.get(&varname) {
                    Ok(Some(ECV(ecv.clone())))
                } else {
                    Ok(Some(ECV(Var(varname))))
                }
            }
        }
    }

    #[inline]
    fn read_func(&mut self, fname: String, bs: &mut &[u8], depth: usize) -> Result<Value, Error> {
        let mut args = Vec::with_capacity(2);
        let sarg = read_string(bs)?;

        loop {
            spaces(bs);
            match peek(bs) {
                Some(b) => {
                    if b == b')' {
                        skip(bs);
                        break;
                    }
                }
                None => return Err(Error::EofWhileParsing(fname)),
            }
            if sarg.is_some() || !args.is_empty() {
                match read(bs) {
                    Some(b',') => {}
                    _ => {
                        return Err(Error::ExpectedComma(format!(
                            "{}",
                            str::from_utf8(bs).unwrap()
                        )))
                    }
                }
            }

            args.push(self.read_expr(bs, depth + 1, false)?);
        }

        Ok(Func(fname, sarg, args))
    }

    #[inline]
    fn read_vector(&mut self, bs: &mut &[u8], depth: usize) -> Result<Option<Value>, Error> {
        if let Some(b'[') = peek(bs) {
            skip(bs);

            let mut args = Vec::with_capacity(3);

            loop {
                spaces(bs);
                match peek(bs) {
                    Some(b) => {
                        if b == b']' {
                            skip(bs);
                            break;
                        }
                    }
                    None => {
                        return Err(Error::EofWhileParsing("vector".to_owned()));
                    }
                }
                if !args.is_empty() {
                    match read(bs) {
                        Some(b',') => {}
                        _ => {
                            return Err(Error::ExpectedComma(format!(
                                "{}",
                                str::from_utf8(bs).unwrap()
                            )))
                        }
                    }
                }

                args.push(self.read_expr(bs, depth + 1, false)?);
            }

            Ok(Some(List(args)))
        } else {
            Ok(None)
        }
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
        .map_err(|_| Error::InvalidNumericLiteral(format!("{}", str::from_utf8(bs).unwrap())))?;
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
                Ok(Some(Add))
            }
            b'-' => {
                skip(bs);
                Ok(Some(Sub))
            }
            b'*' => {
                skip(bs);
                Ok(Some(Mul))
            }
            b'/' => {
                skip(bs);
                Ok(Some(Div))
            }
            b'%' => {
                skip(bs);
                Ok(Some(Rem))
            }
            b'^' => {
                skip(bs);
                Ok(Some(Exp))
            }
            b'<' => {
                skip(bs);
                if peek_is(bs, 0, b'=') {
                    skip(bs);
                    Ok(Some(LTE))
                } else {
                    Ok(Some(LT))
                }
            }
            b'>' => {
                skip(bs);
                if peek_is(bs, 0, b'=') {
                    skip(bs);
                    Ok(Some(GTE))
                } else {
                    Ok(Some(GT))
                }
            }
            b'=' if peek_is(bs, 1, b'=') => {
                skip_n(bs, 2);
                Ok(Some(EQ))
            }
            b'!' if peek_is(bs, 1, b'=') => {
                skip_n(bs, 2);
                Ok(Some(NE))
            }
            b'|' if peek_is(bs, 1, b'|') => {
                skip_n(bs, 2);
                Ok(Some(Or))
            }

            b'&' if peek_is(bs, 1, b'&') => {
                skip_n(bs, 2);
                Ok(Some(And))
            }

            b';' | b')' | b']' | b',' => Ok(None),
            _ => Err(Error::InvalidSyntax(format!(
                "{}",
                str::from_utf8(bs).unwrap()
            ))),
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
            b'-' if peek_is(bs, 1, b'=') => {
                skip_n(bs, 2);
                Ok(Some(ESubAssign))
            }
            b'*' if peek_is(bs, 1, b'=') => {
                skip_n(bs, 2);
                Ok(Some(EMulAssign))
            }
            b'/' if peek_is(bs, 1, b'=') => {
                skip_n(bs, 2);
                Ok(Some(EDivAssign))
            }
            b'%' if peek_is(bs, 1, b'=') => {
                skip_n(bs, 2);
                Ok(Some(EModAssign))
            }
            b'^' if peek_is(bs, 1, b'=') => {
                skip_n(bs, 2);
                Ok(Some(EExpAssign))
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
                _ => panic!("F expected an EOF"),
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
            assert_eq!(ast.read_value(bs, 0), Ok(ECV(Const(12.34))));
        }
    }
}
