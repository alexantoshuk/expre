use std::fmt::{self, Debug, Display};

/// This enumeration boosts performance because it eliminates expensive function calls and redirection for constant values and vars.
#[derive(PartialEq, Clone, Debug)]
pub enum ECV {
    E(usize),
    Const(f64),
    Var(String),
}

pub(crate) use crate::tokens::ECV::*;

impl Display for ECV {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::E(i) => write!(f, "@{i}"),
            Self::Const(v) => write!(f, "Const({v})"),
            Self::Var(s) => write!(f, "Var(\"{s}\")"),
        }
    }
}

#[derive(PartialEq, Debug)]
pub enum Value {
    ECV(ECV),
    UnaryOp(UnaryOp),
    Func(String, Option<String>, Vec<ECV>),
    List(Vec<ECV>),
    Index(ECV, ECV),
}
pub(crate) use crate::tokens::Value::*;

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::ECV(ecv) => write!(f, "{}", ecv),
            Self::UnaryOp(uop) => write!(f, "{uop}"),
            Self::Func(name, sarg, args) => {
                if let Some(sarg) = sarg {
                    write!(f, "Func(\"{name}\", \"{sarg}\"")?;
                    for arg in args {
                        write!(f, ", {arg}")?;
                    }
                    write!(f, ")")
                } else {
                    write!(f, "Func(\"{name}\"")?;
                    for arg in args {
                        write!(f, ", {arg}")?;
                    }
                    write!(f, ")")
                }
            }
            Self::List(args) => write!(f, "List({args:?})"),
            Self::Index(src, index) => write!(f, "{src}[{index}])"),
        }
    }
}

/// Unary Operators
#[derive(Debug, PartialEq)]
pub enum UnaryOp {
    Neg(ECV),
    Not(ECV),
}
pub(crate) use crate::tokens::UnaryOp::*;

impl Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Neg(ecv) => write!(f, "-{ecv}"),
            Self::Not(ecv) => write!(f, "!{ecv}"),
        }
    }
}

/// Binary Operators
#[derive(Debug, PartialEq, PartialOrd, Copy, Clone)]
pub enum BinaryOp {
    // Sorted in order of precedence (low-priority to high-priority):
    // Keep this order in-sync with evaler.rs.  (Search for 'rtol' and 'ltor'.)
    // ESemi = 0,
    Or = 1, // Lowest Priority
    And = 2,
    NE = 3,
    EQ = 4,
    GE = 5,
    LE = 6,
    GT = 7,
    LT = 8,
    Add = 9,
    Sub = 10,
    Mul = 11,
    Div = 12,
    Rem = 13,
    Pow = 14, // Highest Priority
}
pub(crate) use crate::tokens::BinaryOp::*;

impl Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Or => write!(f, "||"),
            And => write!(f, "&&"),
            NE => write!(f, "!="),
            EQ => write!(f, "=="),
            GE => write!(f, ">="),
            LE => write!(f, "<="),
            GT => write!(f, ">"),
            LT => write!(f, "<"),
            Add => write!(f, "+"),
            Sub => write!(f, "-"),
            Mul => write!(f, "*"),
            Div => write!(f, "/"),
            Rem => write!(f, "%"),
            Pow => write!(f, "^"),
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd, Copy, Clone)]
pub enum AssignOp {
    // Sorted in order of precedence (low-priority to high-priority):
    // Keep this order in-sync with evaler.rs.  (Search for 'rtol' and 'ltor'.)
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    RemAssign,
    PowAssign,
}

impl From<AssignOp> for BinaryOp {
    fn from(value: AssignOp) -> Self {
        match value {
            AddAssign => Add,
            SubAssign => Sub,
            MulAssign => Mul,
            DivAssign => Div,
            RemAssign => Rem,
            PowAssign => Pow,
            _ => unreachable!(),
        }
    }
}

impl Display for AssignOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Assign => write!(f, "="),
            AddAssign => write!(f, "+="),
            SubAssign => write!(f, "-="),
            MulAssign => write!(f, "*="),
            DivAssign => write!(f, "/="),
            RemAssign => write!(f, "%="),
            PowAssign => write!(f, "^="),
        }
    }
}
pub(crate) use crate::tokens::AssignOp::*;
