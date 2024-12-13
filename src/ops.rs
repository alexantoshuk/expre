use crate::error::Error;
use crate::map;

// use bytemuck::bytes_of;
use gxhash::GxHasher;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone)]
pub enum ICV {
    FICV(FICV),
    UICV(UICV),
}

pub(crate) use crate::ops::ICV::*;

impl From<FICV> for ICV {
    #[inline]
    fn from(value: FICV) -> Self {
        Self::FICV(value)
    }
}

impl From<UICV> for ICV {
    #[inline]
    fn from(value: UICV) -> Self {
        Self::UICV(value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OP<FFN, UFN> {
    F(F<FFN>),
    U(U<UFN>),
}

pub(crate) use crate::ops::OP::*;

impl<FFN, UFN> From<F<FFN>> for OP<FFN, UFN> {
    fn from(value: F<FFN>) -> Self {
        Self::F(value)
    }
}

impl<FFN, UFN> From<U<UFN>> for OP<FFN, UFN> {
    fn from(value: U<UFN>) -> Self {
        Self::U(value)
    }
}

impl<FFN, UFN> TryFrom<OP<FFN, UFN>> for F<FFN> {
    type Error = Error;
    #[inline]
    fn try_from(value: OP<FFN, UFN>) -> Result<Self, Self::Error> {
        match value {
            OP::F(fop) => Ok(fop),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

impl<FFN, UFN> TryFrom<OP<FFN, UFN>> for U<UFN> {
    type Error = Error;
    #[inline]
    fn try_from(value: OP<FFN, UFN>) -> Result<Self, Self::Error> {
        match value {
            OP::U(uop) => Ok(uop),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}
impl<FFN, UFN> OP<FFN, UFN> {
    #[inline]
    fn order(&self) -> u32 {
        match self {
            Self::F(F::CONST(_)) => 1,
            Self::U(U::CONST(_)) => 2,

            Self::F(_) => 10,
            Self::U(_) => 11,
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
//             Self::F(op) => {
//                 state.write_u8(1);
//                 op.hash(state);
//             }
//             Self::U(op) => {
//                 state.write_u8(2);
//                 op.hash(state);
//             }
//         }
//     }
// }

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return scalar T type aka F
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub type FCONST = f64;

#[derive(Clone, Copy)]
pub enum FICV {
    I(usize),
    CONST(FCONST),
    VAR(usize),
}

// impl From<UICV> for FICV {
//     fn from(value: UICV) -> Self {
//         match value {
//             UICV::CONST([x,y]) => Self::CONST(x),
//             UICV::FROM(ficv) => ficv,
//             UICV::VAR(id) => Self::VAR(id),
//             _ => Self::FROM(value),
//         }
//     }
// }

impl Debug for FICV {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::I(i) => write!(f, "@{:?}", i),
            Self::CONST(c) => write!(f, "CONST({:?})", c),
            Self::VAR(s) => write!(f, "VAR({:?})", s),
        }
    }
}

impl Hash for FICV {
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

impl PartialEq for FICV {
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

impl Eq for FICV {}

#[derive(Debug, Clone)]
pub enum F<FFN> {
    //---- Primitive Value Types:
    CONST(FCONST),
    VAR(usize),

    //---- Unary Ops:
    NEG(FICV),
    NOT(FICV),
    INV(FICV),

    //---- Binary Math Ops:
    ADD(FICV, FICV),

    // A Sub(x) is converted to an FADD(FNEG(x)).
    MUL(FICV, FICV),
    // A Div(n,d) is converted to a FMUL(n,FINV(d)).
    MOD(FICV, FICV),

    EXP(FICV, FICV),

    //---- Equality Ops:
    EQ(FICV, FICV),
    NE(FICV, FICV),

    //---- Comparison Ops:
    LT(FICV, FICV),
    LTE(FICV, FICV),
    GTE(FICV, FICV),
    GT(FICV, FICV),

    //---- Binary Logic Ops:
    OR(FICV, FICV),
    AND(FICV, FICV),
    //---- Functions:
    // STDFN(FFN),
    FN(FFN),
}

impl<FFN: PartialEq> PartialEq for F<FFN> {
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
            (Self::MOD(s0, s1), Self::MOD(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::EXP(s0, s1), Self::EXP(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::LT(s0, s1), Self::LT(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::LTE(s0, s1), Self::LTE(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::EQ(s0, s1), Self::EQ(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::NE(s0, s1), Self::NE(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::GT(s0, s1), Self::GT(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::GTE(s0, s1), Self::GTE(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::OR(s0, s1), Self::OR(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::AND(s0, s1), Self::AND(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            // (Self::STDFN(s), Self::STDFN(o)) => s == o,
            (Self::FN(s), Self::FN(o)) => s == o,
            _ => false,
        }
    }
}

impl<FFN: PartialEq> Eq for F<FFN> {}

impl<FFN: Hash> Hash for F<FFN> {
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
            Self::MOD(a0, a1) => {
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
            // Self::STDFN(ffn) => {
            //     state.write_u8(19);
            //     ffn.hash(state);
            // }
            Self::FN(ffn) => {
                state.write_u8(20);
                ffn.hash(state);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum STDFN {
    ABS(FICV),
    SIN(FICV),
    COS(FICV),
    MIN(FICV, FICV),
    MAX(FICV, FICV),
}
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return [T;2] type aka U
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

pub type UCONST = [f64; 2];

#[derive(Clone, Copy)]
pub enum UICV {
    I(usize),
    CONST(UCONST),
    VAR(usize),
    // FROM(FICV),
}

// impl From<FICV> for UICV {
//     fn from(value: FICV) -> Self {
//         match value {
//             FICV::CONST(c) => Self::CONST([c; 2]),
//             _ => Self::FROM(value),
//         }
//     }
// }

impl Debug for UICV {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::I(i) => write!(f, "@{:?}", i),
            Self::CONST(c) => write!(f, "CONST({:?})", c),
            Self::VAR(s) => write!(f, "VAR({:?})", s),
            // Self::FROM(s) => write!(f, "{:?}", s),
        }
    }
}

impl Hash for UICV {
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
            } // Self::FROM(icv) => {
              //     state.write_u8(4);
              //     icv.hash(state);
              // }
        }
    }
}

impl PartialEq for UICV {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::I(s), Self::I(o)) => s == o,
            (Self::CONST([sx, sy]), Self::CONST([ox, oy])) => {
                (sx.to_bits(), sy.to_bits()) == (ox.to_bits(), oy.to_bits())
            }
            (Self::VAR(s), Self::VAR(o)) => s == o,
            // (Self::FROM(s), Self::FROM(o)) => s == o,
            _ => false,
        }
    }
}

impl Eq for UICV {}

#[derive(Debug, Clone)]
pub enum U<UFN> {
    //---- Primitive Value Types:
    CONST(UCONST),
    VAR(usize),
    SET(FICV, FICV),

    //---- Unary Ops:
    NEG(UICV),
    NOT(UICV),
    INV(UICV),

    //---- Binary Math Ops:
    ADD(UICV, UICV),

    // A Sub(x) is converted to an FADD(FNEG(x)).
    MUL(UICV, UICV),
    // A Div(n,d) is converted to a FMUL(n,FINV(d)).
    MOD(UICV, UICV),

    EXP(UICV, UICV),

    //---- Equality Ops:
    EQ(UICV, UICV),
    NE(UICV, UICV),

    //---- Functions:
    FN(UFN),
}

impl<UFN: PartialEq> PartialEq for U<UFN> {
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
            (Self::MOD(s0, s1), Self::MOD(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::EXP(s0, s1), Self::EXP(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::EQ(s0, s1), Self::EQ(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::NE(s0, s1), Self::NE(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::FN(s), Self::FN(o)) => s == o,
            _ => false,
        }
    }
}
impl<UFN: Eq> Eq for U<UFN> {}

impl<UFN: Hash> Hash for U<UFN> {
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
            Self::MOD(a0, a1) => {
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

// Builtins functions
