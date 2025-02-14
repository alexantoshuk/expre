// use bytemuck::*;
use crate::builtins::*;
use crate::error::Error;
use discriminant::Enum;
use gxhash::GxHasher;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    B = 0,
    F = 1,
    F2 = 2,
    F3 = 3,
}

// #[derive(Debug, Copy, Clone)]
// pub enum Adress {
//     F(usize),
//     F2(usize),
//     F3(usize),
// }

// impl From<Adress> for OP {
//     #[inline]
//     fn from(value: Adress) -> Self {
//         match value {
//             Adress::F(i) => FOP(FOP::VAR(LOCAL(i))),
//             Adress::F2(i) => FOP2(FOP2::VAR(LOCAL(i))),
//             Adress::F3(i) => FOP3(FOP3::VAR(LOCAL(i))),
//         }
//     }
// }

#[derive(Debug, Clone)]
pub enum ARG {
    F(F),
    F2(F2),
    F3(F3),
    B(B),
}

impl ARG {
    #[inline]
    pub fn optype(&self) -> Type {
        match self {
            Self::B(_) => Type::B,
            Self::F(_) => Type::F,
            Self::F2(_) => Type::F2,
            Self::F3(_) => Type::F3,
        }
    }

    #[inline]
    pub fn name(&self) -> &'static str {
        match self {
            Self::F(_) => "F",
            Self::F2(_) => "F2",
            Self::F3(_) => "F3",
            Self::B(_) => "B",
        }
    }

    #[inline]
    pub(crate) fn convert_bool(self) -> Self {
        match self {
            Self::B(b) => Self::F(b.into()),
            _ => self,
        }
    }
}

pub(crate) use crate::op::ARG::*;

impl From<ARG> for OP {
    fn from(value: ARG) -> Self {
        match value {
            F(F::CONST(c)) => FOP(FOP::CONST(c)),
            F(F::VAR(v)) => FOP(FOP::VAR(v)),
            F(F::I(i)) => FOP(FOP::I(i)),

            F2(F2::CONST(c)) => FOP2(FOP2::CONST(c)),
            F2(F2::VAR(v)) => FOP2(FOP2::VAR(v)),
            F2(F2::I(i)) => FOP2(FOP2::I(i)),

            F3(F3::CONST(c)) => FOP3(FOP3::CONST(c)),
            F3(F3::VAR(v)) => FOP3(FOP3::VAR(v)),
            F3(F3::I(i)) => FOP3(FOP3::I(i)),

            B(B::CONST(c)) => BOP(BOP::CONST(c)),
            B(B::VAR(v)) => FOP(FOP::VAR(v)),
            B(B::I(i)) => FOP(FOP::I(i)),

            _ => unreachable!(),
        }
    }
}
impl TryFrom<ARG> for F {
    type Error = Error;
    #[inline]
    fn try_from(value: ARG) -> Result<Self, Self::Error> {
        match value {
            ARG::F(f) => Ok(f),
            ARG::B(b) => Ok(b.into()),
            _ => Err(Error::Undefined("!!!!".into())),
        }
    }
}

impl TryFrom<&ARG> for F {
    type Error = Error;
    #[inline]
    fn try_from(value: &ARG) -> Result<Self, Self::Error> {
        match value {
            ARG::F(f) => Ok(*f),
            ARG::B(b) => Ok((*b).into()),
            _ => Err(Error::Undefined("!!!!".into())),
        }
    }
}

impl TryFrom<ARG> for B {
    type Error = Error;
    #[inline]
    fn try_from(value: ARG) -> Result<Self, Self::Error> {
        match value {
            ARG::B(b) => Ok(b),
            ARG::F(f) => Ok(f.into()),
            _ => Err(Error::Undefined("!!!!".into())),
        }
    }
}
impl TryFrom<&ARG> for B {
    type Error = Error;
    #[inline]
    fn try_from(value: &ARG) -> Result<Self, Self::Error> {
        match value {
            ARG::B(b) => Ok(*b),
            ARG::F(f) => Ok((*f).into()),
            _ => Err(Error::Undefined("!!!!".into())),
        }
    }
}

impl From<B> for ARG {
    #[inline]
    fn from(value: B) -> Self {
        Self::B(value)
    }
}

impl From<F> for ARG {
    #[inline]
    fn from(value: F) -> Self {
        Self::F(value)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VAR {
    LOCAL(usize),
    GLOBAL(usize),
}
pub(crate) use crate::op::VAR::*;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum B {
    I(usize),
    CONST(bool),
    VAR(VAR),
}

impl Default for B {
    fn default() -> Self {
        Self::CONST(false)
    }
}

impl From<F> for B {
    fn from(value: F) -> Self {
        match value {
            F::CONST(c) => B::CONST(c != 0.0),
            F::VAR(i) => B::VAR(i),
            F::I(i) => B::I(i),
        }
    }
}

impl Debug for B {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::I(i) => write!(f, "@{}", i),
            Self::CONST(c) => write!(f, "CONST({:?})", c),
            Self::VAR(i) => write!(f, "VAR({:?})", i),
        }
    }
}

#[derive(Clone, Copy, Enum)]
pub enum F {
    I(usize),
    CONST(f64),
    VAR(VAR),
}

impl From<B> for F {
    fn from(value: B) -> Self {
        match value {
            B::CONST(c) => F::CONST(c.into()),
            B::VAR(i) => F::VAR(i),
            B::I(i) => F::I(i),
        }
    }
}

impl PartialEq for F {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::CONST(s), Self::CONST(o)) => s.to_bits() == o.to_bits(),
            (Self::VAR(s), Self::VAR(o)) => s == o,
            (Self::I(s), Self::I(o)) => s == o,
            _ => false,
        }
    }
}

impl Eq for F {}
impl Ord for F {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::CONST(s), Self::CONST(o)) => s.to_bits().cmp(&o.to_bits()),
            (Self::VAR(s), Self::VAR(o)) => s.cmp(o),
            (Self::I(s), Self::I(o)) => s.cmp(o),
            _ => self.discriminant().cmp(&other.discriminant()),
        }
    }
}

impl PartialOrd for F {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for F {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.discriminant().hash(state);
        match self {
            Self::CONST(c) => c.to_bits().hash(state),
            Self::VAR(v) => v.hash(state),
            Self::I(i) => i.hash(state),
        }
    }
}

impl Default for F {
    fn default() -> Self {
        Self::CONST(Default::default())
    }
}

impl Debug for F {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::I(i) => write!(f, "@{}", i),
            Self::CONST(c) => write!(f, "CONST({:?})", c),
            Self::VAR(u) => write!(f, "VAR({:?})", u),
        }
    }
}

#[derive(Debug, Clone)]
pub enum OP {
    BOP(BOP),
    FOP(FOP),
    FOP2(FOP2),
    FOP3(FOP3),
}

pub(crate) use crate::op::OP::*;

impl Default for OP {
    fn default() -> Self {
        FOP(FOP::default())
    }
}

impl OP {
    #[inline]
    pub fn optype(&self) -> Type {
        match self {
            Self::BOP(_) => Type::B,
            Self::FOP(_) => Type::F,
            Self::FOP2(_) => Type::F2,
            Self::FOP3(_) => Type::F3,
        }
    }

    #[inline]
    fn order_with_const(&self) -> u32 {
        match self {
            Self::BOP(BOP::CONST(_)) => 0,
            Self::FOP(FOP::CONST(_)) => 1,
            Self::FOP2(FOP2::CONST(_)) => 2,
            Self::FOP3(FOP3::CONST(_)) => 3,

            Self::BOP(_) => 10,
            Self::FOP(_) => 11,
            Self::FOP2(_) => 12,
            Self::FOP3(_) => 13,
        }
    }

    // #[inline]
    // fn update_i(&mut self, f: FN)
    // where
    //     FN: FnOnce(usize) -> usize + Copy,
    // {
    //     match self {
    //         Self::FOP(instr) => {
    //             instr.update_i(f);
    //         }
    //         Self::FOP2(instr) => {
    //             instr.update_i(f);
    //         }
    //     }
    // }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return bool type aka BOP
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub enum BOP {
    I(usize),
    //---- Primitive Value Types:
    CONST(bool),
    STORE(usize, usize),
    //---- Unary Ops:
    NOT(B),

    //---- Binary Logic Ops:
    OR(B, B),
    AND(B, B),

    //---- Equality Ops:
    EQ(F, F),
    NE(F, F),
    EQ2(F2, F2),
    NE2(F2, F2),
    EQ3(F3, F3),
    NE3(F3, F3),

    //---- Comparison Ops:
    LT(F, F),
    LE(F, F),
    GE(F, F),
    GT(F, F),

    IF(B, B, B),
}

impl Default for BOP {
    fn default() -> Self {
        Self::CONST(false)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return scalar T type aka FOP
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq)]
pub enum FOP {
    I(usize),
    //---- Primitive Value Types:
    CONST(f64),
    VAR(VAR),
    STORE(usize, usize),

    // F2COMP(F2, F),
    // F3COMP(F3, F),

    //---- Unary Ops:
    NEG(F),
    INV(F),

    //---- Binary Math Ops:
    ADD(F, F),
    // A Sub(x) is converted to an FADD(FNEG(x)).
    MUL(F, F),
    // A Div(n,d) is converted to a FMUL(n,FINV(d)).
    REM(F, F),
    POW(F, F),

    //---- Functions:
    IF(B, F, F),
    STDFN(STDFN),
}

impl Default for FOP {
    fn default() -> Self {
        Self::CONST(Default::default())
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return [T;2] type aka FOP2
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

macro_rules! make_array_FOP {
    ($N: literal, $ARG: ident, $OP: ident, $FN: ident) => {
        #[derive(Clone, Copy, Enum)]
        pub enum $ARG {
            I(usize),
            CONST([f64; $N]),
            VAR(VAR),
            F(F),
        }

        impl PartialEq for $ARG {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                match (self, other) {
                    (Self::CONST(s), Self::CONST(o)) => as_bytes(s) == as_bytes(o),
                    (Self::VAR(s), Self::VAR(o)) => s == o,
                    (Self::I(s), Self::I(o)) => s == o,
                    (Self::F(s), Self::F(o)) => s == o,
                    _ => false,
                }
            }
        }
        impl Eq for $ARG {}
        impl Ord for $ARG {
            #[inline]
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                match (self, other) {
                    (Self::CONST(s), Self::CONST(o)) => as_bytes(s).cmp(as_bytes(o)),
                    (Self::VAR(s), Self::VAR(o)) => s.cmp(o),
                    (Self::I(s), Self::I(o)) => s.cmp(o),
                    (Self::F(s), Self::F(o)) => s.cmp(o),
                    _ => self.discriminant().cmp(&other.discriminant()),
                }
            }
        }

        impl PartialOrd for $ARG {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Hash for $ARG {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.discriminant().hash(state);
                match self {
                    Self::CONST(c) => as_bytes(c).hash(state),
                    Self::VAR(v) => v.hash(state),
                    Self::I(i) => i.hash(state),
                    Self::F(f) => f.hash(state),
                }
            }
        }

        impl Default for $ARG {
            fn default() -> Self {
                Self::CONST(Default::default())
            }
        }

        impl From<[f64; $N]> for $ARG {
            #[inline]
            fn from(value: [f64; $N]) -> Self {
                Self::CONST(value)
            }
        }

        impl From<f64> for $ARG {
            #[inline]
            fn from(value: f64) -> Self {
                Self::CONST([value; $N])
            }
        }

        impl From<F> for $ARG {
            #[inline]
            fn from(value: F) -> Self {
                match value {
                    F::CONST(c) => Self::CONST([c; $N]),
                    _ => Self::F(value),
                }
            }
        }

        impl From<B> for $ARG {
            #[inline]
            fn from(value: B) -> Self {
                F::from(value).into()
            }
        }

        impl From<$ARG> for ARG {
            #[inline]
            fn from(value: $ARG) -> Self {
                Self::$ARG(value)
            }
        }

        impl TryFrom<ARG> for $ARG {
            type Error = Error;
            #[inline]
            fn try_from(value: ARG) -> Result<Self, Self::Error> {
                match value {
                    ARG::$ARG(ff) => Ok(ff),
                    ARG::F(f) => Ok(f.into()),
                    ARG::B(b) => Ok(b.into()),
                    _ => Err(Error::Undefined("!!!!".into())),
                }
            }
        }
        impl TryFrom<&ARG> for $ARG {
            type Error = Error;
            #[inline]
            fn try_from(value: &ARG) -> Result<Self, Self::Error> {
                match value {
                    ARG::$ARG(ff) => Ok(*ff),
                    ARG::F(f) => Ok((*f).into()),
                    ARG::B(b) => Ok((*b).into()),
                    _ => Err(Error::Undefined("!!!!".into())),
                }
            }
        }

        impl Debug for $ARG {
            fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                match self {
                    Self::I(i) => write!(f, "@{}", i),
                    Self::CONST(c) => write!(f, "CONST({:?})", c),
                    Self::VAR(v) => write!(f, "VAR({:?})", v),
                    Self::F(f_) => write!(f, "{:?}", f_),
                }
            }
        }

        #[derive(Debug, Clone)]
        pub enum $OP {
            I(usize),
            //---- Primitive Value Types:
            CONST([f64; $N]),
            VAR(VAR),
            NEW([F; $N]),
            STORE(usize, usize),

            //---- Unary Ops:
            NEG($ARG),
            INV($ARG),

            //---- Binary Math Ops:
            ADD($ARG, $ARG),

            // A Sub(x) is converted to an FADD(FNEG(x)).
            MUL($ARG, $ARG),
            // A Div(n,d) is converted to a FMUL(n,FINV(d)).
            REM($ARG, $ARG),
            POW($ARG, $ARG),

            //---- Functions:
            IF(B, $ARG, $ARG),
            STDFN($FN),
        }

        impl Default for $OP {
            fn default() -> Self {
                Self::CONST([0.0; $N])
            }
        }
    };
}

make_array_FOP!(2, F2, FOP2, STDFN2);
make_array_FOP!(3, F3, FOP3, STDFN3);

#[inline(always)]
fn _hash<T: Hash>(obj: T) -> u64 {
    let mut hasher = GxHasher::with_seed(1411);
    obj.hash(&mut hasher);
    hasher.finish()
}

#[inline]
pub(crate) fn sort(ops: &mut [OP]) {
    ops.sort_by(|a, b| a.order_with_const().cmp(&b.order_with_const()))
}

#[inline]
fn as_bytes<T: Copy, const N: usize>(array: &[T; N]) -> &[u8] {
    // Get a pointer to the first element of the array
    let ptr = array as *const [T; N] as *const u8;

    // Calculate the length in bytes
    let len = std::mem::size_of::<[T; N]>();

    // Create a slice from the pointer and length
    unsafe { std::slice::from_raw_parts(ptr, len) }
}
