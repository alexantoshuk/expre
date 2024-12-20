use crate::error::Error;

// use bytemuck::bytes_of;
use gxhash::GxHasher;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};

impl From<f64> for F {
    fn from(value: f64) -> Self {
        Self::CONST(value)
    }
}

impl From<[f64; 2]> for U {
    fn from(value: [f64; 2]) -> Self {
        Self::CONST(value)
    }
}
impl From<f64> for U {
    fn from(value: f64) -> Self {
        Self::CONST([value; 2])
    }
}

pub fn fvar(id: usize) -> F {
    F::VAR(id)
}

pub fn uvar(id: usize) -> U {
    U::VAR(id)
}

#[derive(Debug, Clone)]
pub enum ICV {
    F(F),
    U(U),
    S(String),
}

pub(crate) use crate::ops::ICV::*;

impl From<F> for ICV {
    #[inline]
    fn from(value: F) -> Self {
        Self::F(value)
    }
}

impl From<U> for ICV {
    #[inline]
    fn from(value: U) -> Self {
        Self::U(value)
    }
}

impl From<String> for ICV {
    #[inline]
    fn from(value: String) -> Self {
        Self::S(value)
    }
}

impl TryFrom<ICV> for f64 {
    type Error = Error;
    #[inline]
    fn try_from(value: ICV) -> Result<Self, Self::Error> {
        match value {
            F(F::CONST(c)) => Ok(c),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

impl TryFrom<ICV> for [f64; 2] {
    type Error = Error;
    #[inline]
    fn try_from(value: ICV) -> Result<Self, Self::Error> {
        match value {
            F(F::CONST(c)) => Ok([c; 2]),
            U(U::CONST(c)) => Ok(c),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OP<FFN, UFN> {
    FO(FO<FFN>),
    UO(UO<UFN>),
}

pub(crate) use crate::ops::OP::*;

impl<FFN, UFN> From<FO<FFN>> for OP<FFN, UFN> {
    fn from(value: FO<FFN>) -> Self {
        Self::FO(value)
    }
}

impl<FFN, UFN> From<UO<UFN>> for OP<FFN, UFN> {
    fn from(value: UO<UFN>) -> Self {
        Self::UO(value)
    }
}

impl<FFN, UFN> OP<FFN, UFN> {
    #[inline]
    fn order(&self) -> u32 {
        match self {
            Self::FO(FO::CONST(_)) => 1,
            Self::UO(UO::CONST(_)) => 2,

            Self::FO(_) => 10,
            Self::UO(_) => 11,
        }
    }

    // #[inline]
    // fn update_i<FN>(&mut self, f: FN)
    // where
    //     FN: FnOnce(usize) -> usize + Copy,
    // {
    //     match self {
    //         Self::FOP(instr) => {
    //             instr.update_i(f);
    //         }
    //         Self::UOP(instr) => {
    //             instr.update_i(f);
    //         }
    //     }
    // }
}

// impl<M: Module> Hash for OP<M> {
//     #[inline]
//     fn hash<H: Hasher>(&self, state: &mut H) {
//         match self {
//             Self::FO(op) => {
//                 state.write_u8(1);
//                 op.hash(state);
//             }
//             Self::UO(op) => {
//                 state.write_u8(2);
//                 op.hash(state);
//             }
//         }
//     }
// }

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return scalar T type aka FO
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub type FCONST = f64;

#[derive(Clone, Copy)]
pub enum F {
    I(usize),
    CONST(FCONST),
    VAR(usize),
}

impl TryFrom<ICV> for F {
    type Error = Error;
    #[inline]
    fn try_from(value: ICV) -> Result<Self, Self::Error> {
        match value {
            F(ficv) => Ok(ficv),
            U(U::F(ficv)) => Ok(ficv),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

impl TryFrom<U> for F {
    type Error = Error;
    #[inline]
    fn try_from(value: U) -> Result<Self, Self::Error> {
        match value {
            U::F(ficv) => Ok(ficv),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

// impl From<U> for F {
//     fn from(value: U) -> Self {
//         match value {
//             U::CONST([x,y]) => Self::CONST(x),
//             U::FROM(ficv) => ficv,
//             U::VAR(id) => Self::VAR(id),
//             _ => Self::FROM(value),
//         }
//     }
// }

impl Debug for F {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::I(i) => write!(f, "@{:?}", i),
            Self::CONST(c) => write!(f, "CONST({:?})", c),
            Self::VAR(s) => write!(f, "VAR({:?})", s),
        }
    }
}

impl Hash for F {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::I(u) => {
                state.write_u8(1);
                state.write_usize(*u);
            }
            Self::CONST(c) => {
                state.write_u8(2);
                state.write_u64(c.to_bits());
            }
            Self::VAR(u) => {
                state.write_u8(3);
                state.write_usize(*u);
            }
        }
    }
}

impl PartialEq for F {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::I(s), Self::I(o)) => s == o,
            (Self::CONST(s), Self::CONST(o)) => s.to_bits() == o.to_bits(),
            (Self::VAR(s), Self::VAR(o)) => s == o,
            _ => false,
        }
    }
}

impl Eq for F {}

// #[derive(Debug, Clone)]
// pub enum OPP {
//     //---- Primitive Value Types:
//     CONST(FCONST),
//     VAR(usize),

//     //---- Unary Ops:
//     NEG(Type, ICV),
//     NOT(Type, ICV),
//     INV(Type, ICV),

//     //---- Binary Math Ops:
//     ADD(Type, ICV, ICV),
// }
#[derive(Debug, Clone)]
pub enum FO<FFN> {
    //---- Primitive Value Types:
    CONST(FCONST),
    VAR(usize),

    //---- Unary Ops:
    NEG(F),
    NOT(F),
    INV(F),

    //---- Binary Math Ops:
    ADD(F, F),
    // A Sub(x) is converted to an FADD(FNEG(x)).
    MUL(F, F),
    // A Div(n,d) is converted to a FMUL(n,FINV(d)).
    REM(F, F),
    EXP(F, F),

    //---- Equality Ops:
    EQ(F, F),
    NE(F, F),

    //---- Comparison Ops:
    LT(F, F),
    LTE(F, F),
    GTE(F, F),
    GT(F, F),

    //---- Binary Logic Ops:
    OR(F, F),
    AND(F, F),
    //---- Functions:
    FN(FFN),
}

impl<FFN, UFN> TryFrom<OP<FFN, UFN>> for FO<FFN> {
    type Error = Error;
    #[inline]
    fn try_from(value: OP<FFN, UFN>) -> Result<Self, Self::Error> {
        match value {
            OP::FO(fop) => Ok(fop),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

impl<FFN: PartialEq> PartialEq for FO<FFN> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::CONST(s), Self::CONST(o)) => s.to_bits() == o.to_bits(),
            (Self::VAR(s), Self::VAR(o)) => s == o,
            (Self::ADD(s0, s1), Self::ADD(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::MUL(s0, s1), Self::MUL(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::NEG(s), Self::NEG(o)) => s == o,
            (Self::NOT(s), Self::NOT(o)) => s == o,
            (Self::INV(s), Self::INV(o)) => s == o,
            (Self::REM(s0, s1), Self::REM(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::EXP(s0, s1), Self::EXP(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::LT(s0, s1), Self::LT(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::LTE(s0, s1), Self::LTE(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::EQ(s0, s1), Self::EQ(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::NE(s0, s1), Self::NE(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::GT(s0, s1), Self::GT(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::GTE(s0, s1), Self::GTE(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::OR(s0, s1), Self::OR(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::AND(s0, s1), Self::AND(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::FN(s), Self::FN(o)) => s == o,
            _ => false,
        }
    }
}

impl<FFN: PartialEq> Eq for FO<FFN> {}

impl<FFN: Hash> Hash for FO<FFN> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::CONST(c) => {
                state.write_u8(1);
                state.write_u64(c.to_bits());
            }
            Self::VAR(u) => {
                state.write_u8(2);
                state.write_usize(*u);
            }
            Self::NEG(a) => {
                state.write_u8(4);
                a.hash(state);
            }
            Self::NOT(a) => {
                state.write_u8(5);
                a.hash(state);
            }
            Self::INV(a) => {
                state.write_u8(6);
                a.hash(state);
            }
            Self::ADD(a0, a1) => {
                state.write_u8(7);
                state.write_u64(_hash(a0) ^ _hash(a1));
            }
            Self::MUL(a0, a1) => {
                state.write_u8(8);
                state.write_u64(_hash(a0) ^ _hash(a1));
            }
            Self::REM(a0, a1) => {
                state.write_u8(9);
                a0.hash(state);
                a1.hash(state);
            }
            Self::EXP(a0, a1) => {
                state.write_u8(10);
                a0.hash(state);
                a1.hash(state);
            }
            Self::LT(a0, a1) => {
                state.write_u8(11);
                a0.hash(state);
                a1.hash(state);
            }
            Self::LTE(a0, a1) => {
                state.write_u8(12);
                a0.hash(state);
                a1.hash(state);
            }
            Self::EQ(a0, a1) => {
                state.write_u8(13);
                state.write_u64(_hash(a0) ^ _hash(a1));
            }
            Self::NE(a0, a1) => {
                state.write_u8(14);
                state.write_u64(_hash(a0) ^ _hash(a1));
            }
            Self::GTE(a0, a1) => {
                state.write_u8(15);
                a0.hash(state);
                a1.hash(state);
            }
            Self::GT(a0, a1) => {
                state.write_u8(16);
                a0.hash(state);
                a1.hash(state);
            }
            Self::OR(a0, a1) => {
                state.write_u8(17);
                state.write_u64(_hash(a0) ^ _hash(a1));
            }
            Self::AND(a0, a1) => {
                state.write_u8(18);
                state.write_u64(_hash(a0) ^ _hash(a1));
            }
            Self::FN(ffn) => {
                state.write_u8(20);
                ffn.hash(state);
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return [T;2] type aka UO
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

pub type UCONST = [f64; 2];

#[derive(Clone, Copy)]
pub enum U {
    I(usize),
    CONST(UCONST),
    VAR(usize),
    F(F),
}

impl TryFrom<ICV> for U {
    type Error = Error;
    #[inline]
    fn try_from(value: ICV) -> Result<Self, Self::Error> {
        match value {
            U(uicv) => Ok(uicv),
            F(ficv) => Ok(U::F(ficv)),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

impl From<F> for U {
    fn from(value: F) -> Self {
        match value {
            F::CONST(c) => Self::CONST([c; 2]),
            _ => Self::F(value),
        }
    }
}

impl Debug for U {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::I(i) => write!(f, "@{:?}", i),
            Self::CONST(c) => write!(f, "CONST({:?})", c),
            Self::VAR(s) => write!(f, "VAR({:?})", s),
            Self::F(s) => write!(f, "{:?}", s),
        }
    }
}

impl Hash for U {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::I(u) => {
                state.write_u8(1);
                state.write_usize(*u);
            }
            Self::CONST([x, y]) => {
                state.write_u8(2);
                state.write_u64(x.to_bits());
                state.write_u64(y.to_bits());
            }
            Self::VAR(u) => {
                state.write_u8(3);
                state.write_usize(*u);
            }
            Self::F(ficv) => {
                state.write_u8(4);
                ficv.hash(state);
            }
        }
    }
}

impl PartialEq for U {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::I(s), Self::I(o)) => s == o,
            (Self::CONST([sx, sy]), Self::CONST([ox, oy])) => {
                (sx.to_bits(), sy.to_bits()) == (ox.to_bits(), oy.to_bits())
            }
            (Self::VAR(s), Self::VAR(o)) => s == o,
            (Self::F(s), Self::F(o)) => s == o,
            _ => false,
        }
    }
}

impl Eq for U {}

#[derive(Debug, Clone)]
pub enum UO<UFN> {
    //---- Primitive Value Types:
    CONST(UCONST),
    VAR(usize),
    SET(F, F),

    //---- Unary Ops:
    NEG(U),
    NOT(U),
    INV(U),

    //---- Binary Math Ops:
    ADD(U, U),

    // A Sub(x) is converted to an FADD(FNEG(x)).
    MUL(U, U),
    // A Div(n,d) is converted to a FMUL(n,FINV(d)).
    REM(U, U),

    EXP(U, U),

    //---- Equality Ops:
    EQ(U, U),
    NE(U, U),

    //---- Functions:
    FN(UFN),
}

impl<FFN, UFN> TryFrom<OP<FFN, UFN>> for UO<UFN> {
    type Error = Error;
    #[inline]
    fn try_from(value: OP<FFN, UFN>) -> Result<Self, Self::Error> {
        match value {
            OP::UO(uop) => Ok(uop),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

impl<UFN: PartialEq> PartialEq for UO<UFN> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::CONST([sx, sy]), Self::CONST([ox, oy])) => {
                (sx.to_bits(), sy.to_bits()) == (ox.to_bits(), oy.to_bits())
            }
            (Self::VAR(s), Self::VAR(o)) => s == o,
            (Self::SET(sx, sy), Self::SET(ox, oy)) => (sx, sy) == (ox, oy),

            (Self::ADD(s0, s1), Self::ADD(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::MUL(s0, s1), Self::MUL(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::NEG(s), Self::NEG(o)) => s == o,
            (Self::NOT(s), Self::NOT(o)) => s == o,
            (Self::INV(s), Self::INV(o)) => s == o,
            (Self::REM(s0, s1), Self::REM(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::EXP(s0, s1), Self::EXP(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::EQ(s0, s1), Self::EQ(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::NE(s0, s1), Self::NE(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::FN(s), Self::FN(o)) => s == o,
            _ => false,
        }
    }
}
impl<UFN: Eq> Eq for UO<UFN> {}

impl<UFN: Hash> Hash for UO<UFN> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::CONST([x, y]) => {
                state.write_u8(1);
                state.write_u64(x.to_bits());
                state.write_u64(y.to_bits());
            }
            Self::VAR(u) => {
                state.write_u8(2);
                state.write_usize(*u);
            }
            Self::SET(x, y) => {
                state.write_u8(3);
                x.hash(state);
                y.hash(state);
            }
            Self::NEG(a) => {
                state.write_u8(4);
                a.hash(state);
            }
            Self::NOT(a) => {
                state.write_u8(5);
                a.hash(state);
            }
            Self::INV(a) => {
                state.write_u8(6);
                a.hash(state);
            }
            Self::ADD(a0, a1) => {
                state.write_u8(7);
                state.write_u64(_hash(a0) ^ _hash(a1));
            }
            Self::MUL(a0, a1) => {
                state.write_u8(8);
                state.write_u64(_hash(a0) ^ _hash(a1));
            }
            Self::REM(a0, a1) => {
                state.write_u8(9);
                a0.hash(state);
                a1.hash(state);
            }
            Self::EXP(a0, a1) => {
                state.write_u8(10);
                a0.hash(state);
                a1.hash(state);
            }
            Self::EQ(a0, a1) => {
                state.write_u8(13);
                state.write_u64(_hash(a0) ^ _hash(a1));
            }
            Self::NE(a0, a1) => {
                state.write_u8(14);
                state.write_u64(_hash(a0) ^ _hash(a1));
            }

            Self::FN(ufn) => {
                state.write_u8(15);
                ufn.hash(state);
            }
        }
    }
}

#[inline(always)]
fn _hash<T: Hash>(obj: T) -> u64 {
    let mut hasher = GxHasher::with_seed(1411);
    obj.hash(&mut hasher);
    hasher.finish()
}

#[inline]
pub(crate) fn sort<FFN, UFN>(ops: &mut [OP<FFN, UFN>]) {
    ops.sort_by(|a, b| a.order().cmp(&b.order()))
}
