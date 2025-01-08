use crate::compiler::*;
use crate::context::*;
use crate::error::Error;
use crate::evaler::*;
use crate::float::*;
// use bytemuck::bytes_of;
use gxhash::GxHasher;
use num_traits::Zero;
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

#[derive(Debug, Clone)]
pub enum ARG {
    F(F),
    U(U),
    // S(String),
}

pub(crate) use crate::ops::ARG::*;

// impl From<B> for ARG {
//     #[inline]
//     fn from(value: B) -> Self {
//         Self::B(value)
//     }
// }

impl From<F> for ARG {
    #[inline]
    fn from(value: F) -> Self {
        Self::F(value)
    }
}

impl From<U> for ARG {
    #[inline]
    fn from(value: U) -> Self {
        Self::U(value)
    }
}

// impl From<String> for ARG {
//     #[inline]
//     fn from(value: String) -> Self {
//         Self::S(value)
//     }
// }

impl TryFrom<ARG> for f64 {
    type Error = Error;
    #[inline]
    fn try_from(value: ARG) -> Result<Self, Self::Error> {
        match value {
            F(F::CONST(c)) => Ok(c),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

impl TryFrom<ARG> for [f64; 2] {
    type Error = Error;
    #[inline]
    fn try_from(value: ARG) -> Result<Self, Self::Error> {
        match value {
            F(F::CONST(c)) => Ok([c; 2]),
            U(U::CONST(c)) => Ok(c),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum B {
    I(usize),
    CONST(bool),
    VAR(usize),
}

impl Debug for B {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::I(i) => write!(f, "b@{:?}", i),
            Self::CONST(c) => write!(f, "CONST({:?})", c),
            Self::VAR(u) => write!(f, "VAR({:?})", u),
        }
    }
}

#[derive(Clone, Copy)]
pub enum F {
    I(usize),
    CONST(f64),
    VAR(usize),
}

impl From<U> for F {
    fn from(value: U) -> Self {
        match value {
            U::CONST(c) => Self::CONST(c[0]),
            U::I(i) => Self::I(i),
            U::VAR(u) => Self::VAR(u),
        }
    }
}

impl Debug for F {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::I(i) => write!(f, "f@{:?}", i),
            Self::CONST(c) => write!(f, "CONST({:?})", c),
            Self::VAR(u) => write!(f, "VAR({:?})", u),
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

#[derive(Clone, Copy)]
pub enum U {
    I(usize),
    CONST([f64; 2]),
    VAR(usize),
}

impl From<F> for U {
    fn from(value: F) -> Self {
        match value {
            F::CONST(c) => Self::CONST([c; 2]),
            F::I(i) => Self::I(i),
            F::VAR(u) => Self::VAR(u),
        }
    }
}

impl Debug for U {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::I(i) => write!(f, "u@{:?}", i),
            Self::CONST(c) => write!(f, "CONST({:?})", c),
            Self::VAR(u) => write!(f, "VAR({:?})", u),
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

            _ => false,
        }
    }
}

impl Eq for U {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OP<FFN, UFN> {
    BOP(BOP),
    FOP(FOP<FFN>),
    UOP(UOP<UFN>),
}

pub(crate) use crate::ops::OP::*;

impl<FFN, UFN> From<FOP<FFN>> for OP<FFN, UFN> {
    fn from(value: FOP<FFN>) -> Self {
        Self::FOP(value)
    }
}

impl<FFN, UFN> From<UOP<UFN>> for OP<FFN, UFN> {
    fn from(value: UOP<UFN>) -> Self {
        Self::UOP(value)
    }
}

impl<FFN, UFN> OP<FFN, UFN> {
    #[inline]
    fn order(&self) -> u32 {
        match self {
            Self::BOP(BOP::CONST(_)) => 0,
            Self::FOP(FOP::CONST(_)) => 1,
            Self::UOP(UOP::CONST(_)) => 2,

            Self::BOP(_) => 10,
            Self::FOP(_) => 11,
            Self::UOP(_) => 12,
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

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return bool type aka BOP
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum BOP {
    //---- Primitive Value Types:
    CONST(bool),

    //---- Unary Ops:
    NOT(B),

    //---- Binary Logic Ops:
    OR(B, B),
    AND(B, B),

    //---- Equality Ops:
    EQ(F, F),
    NE(F, F),
    EQU(U, U),
    NEU(U, U),

    //---- Comparison Ops:
    LT(F, F),
    LE(F, F),
    GE(F, F),
    GT(F, F),
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return scalar T type aka FOP
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub enum FOP<FFN> {
    //---- Primitive Value Types:
    CONST(f64),
    VAR(usize),

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

    // STD(FSTD),
    //---- Functions:
    FN(FFN),
}

impl<FFN: PartialEq> PartialEq for FOP<FFN> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::CONST(s), Self::CONST(o)) => s.to_bits() == o.to_bits(),
            (Self::VAR(s), Self::VAR(o)) => s == o,
            (Self::ADD(s0, s1), Self::ADD(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::MUL(s0, s1), Self::MUL(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::NEG(s), Self::NEG(o)) => s == o,
            (Self::INV(s), Self::INV(o)) => s == o,
            (Self::REM(s0, s1), Self::REM(o0, o1)) => (s0, s1) == (o0, o1),

            (Self::FN(s), Self::FN(o)) => s == o,
            _ => false,
        }
    }
}

impl<FFN: PartialEq> Eq for FOP<FFN> {}

impl<FFN: Hash> Hash for FOP<FFN> {
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
            Self::POW(a0, a1) => {
                state.write_u8(10);
                a0.hash(state);
                a1.hash(state);
            }

            Self::FN(ffn) => {
                state.write_u8(21);
                ffn.hash(state);
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return [T;2] type aka UOP
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub enum UOP<UFN> {
    //---- Primitive Value Types:
    CONST([f64; 2]),
    VAR(usize),
    SET(F, F),

    //---- Unary Ops:
    NEG(U),
    INV(U),

    //---- Binary Math Ops:
    ADD(U, U),

    // A Sub(x) is converted to an FADD(FNEG(x)).
    MUL(U, U),
    // A Div(n,d) is converted to a FMUL(n,FINV(d)).
    REM(U, U),
    POW(U, U),

    //---- Functions:
    // STD(USTD),
    FN(UFN),
}

impl<FFN, UFN> TryFrom<OP<FFN, UFN>> for UOP<UFN> {
    type Error = Error;
    #[inline]
    fn try_from(value: OP<FFN, UFN>) -> Result<Self, Self::Error> {
        match value {
            OP::UOP(uop) => Ok(uop),
            _ => Err(Error::InvalidType("Ivalid type".into())),
        }
    }
}

impl<UFN: PartialEq> PartialEq for UOP<UFN> {
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

            (Self::INV(s), Self::INV(o)) => s == o,
            (Self::REM(s0, s1), Self::REM(o0, o1)) => (s0, s1) == (o0, o1),
            (Self::POW(s0, s1), Self::POW(o0, o1)) => (s0, s1) == (o0, o1),

            (Self::FN(s), Self::FN(o)) => s == o,
            _ => false,
        }
    }
}
impl<UFN: Eq> Eq for UOP<UFN> {}

impl<UFN: Hash> Hash for UOP<UFN> {
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
                state.write_u8(4);
                x.hash(state);
                y.hash(state);
            }
            Self::NEG(a) => {
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
            Self::POW(a0, a1) => {
                state.write_u8(10);
                a0.hash(state);
                a1.hash(state);
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

// macro_rules! impl_std_fn {
//     (
//         $($fname:ident($($fargname:ident),*),)*
//     ) => {
//         use paste::paste;
//         macro_rules! _type {
//             ($name:ident, $T: ty)=>{
//                 $T
//             }
//         }
//         paste!{
//             #[derive(Eq, PartialEq, Hash, Clone, Debug)]
//             enum FSTD {
//                 $($fname($(_type!($fargname, F)),*)),*
//             }

//             #[derive(Eq, PartialEq, Hash, Clone, Debug)]
//             enum USTD {
//                 $($fname($(_type!($fargname, U)),*)),*
//             }

//             #[inline]
//             fn dispatch_stdfn<FFN, UFN>(name: &str, args: &[ARG]) -> Option<OP<FFN, UFN>>{
//                 match (name, args) {
//                     $((stringify!($fname), &[$(F(F::CONST($fargname))),*]) => {Some(FOP(FOP::CONST(f64::$fname($($fargname),*))))})*
//                     $((stringify!($fname), &[$(F($fargname)),*]) => {Some(FOP(FOP::STD(FSTD::$fname($($fargname),*))))})*

//                     $((stringify!($fname), &[$(ref $fargname @ (F(F::CONST(_)) | U(U::CONST(_)))),*]) => {Some(UOP(UOP::CONST(<[f64;2]>::$fname($($fargname.clone().try_into().unwrap()),*))))})*
//                     $((stringify!($fname), &[$(U($fargname)),*]) => {Some(UOP(UOP::STD(USTD::$fname($($fargname),*))))})*

//                     _ => None,
//                 }
//             }

//             impl<M, T, CTX> FEvaler<M, T, CTX> for FSTD
//             where
//             M: Module,
//             T: Float,
//                 CTX: Context<T>,
//             {
//                 #[inline]
//                 fn eval(&self, en: &Expression<M>, ctx: &CTX) -> T {
//                     match self {
//                         $(Self::$fname($($fargname),*) => {T::$fname($($fargname.eval(en, ctx)),*)})*
//                         _=> unreachable!(),
//                     }
//                 }
//             }

//             impl<M, T, CTX> UEvaler<M, T, CTX> for USTD
//             where
//             M: Module<FFN: FEvaler<>>,
//             T: Float,
//                 CTX: Context<T>,
//             {
//                 #[inline]
//                 fn eval(&self, en: &Expression<M>, ctx: &CTX) -> [T;2] {
//                     match self {
//                         $(Self::$fname($($fargname),*) => {<[T;2]>::$fname($($fargname.eval(en, ctx)),*)})*
//                         _=> unreachable!(),
//                     }
//                 }
//             }
//         }
//     };
// }

// impl_std_fn!(
//     floor(x),
//     ceil(x),
//     round(x),
//     recip(x),
//     abs(x),
//     ln(x),
//     min(x, y),
//     max(x, y),
//     pow(x, n),
//     sqrt(x),
//     cbrt(x),
//     hypot(x, y),
//     sin(x),
//     cos(x),
//     bias(x, b),
//     fit(x, oldmin, oldmax, newmin, newmax),
//     fit01(x, newmin, newmax),
//     clamp(x, min, max),
//     clamp01(x),
// );
