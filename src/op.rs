// use bytemuck::*;
use crate::builtins::*;
use crate::error::Error;
use gxhash::GxHasher;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
impl From<f64> for F {
    fn from(value: f64) -> Self {
        Self::CONST(value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ARG {
    F(F),
    F2(F2),
    F3(F3),
    B(B),
}
impl ARG {
    #[inline]
    pub fn name(&self) -> &'static str {
        match self {
            Self::B(_) => "B",
            Self::F(_) => "F",
            Self::F2(_) => "F2",
            Self::F3(_) => "F3",
        }
    }

    #[inline]
    fn order(&self) -> u32 {
        match self {
            Self::B(_) => 1,
            Self::F(_) => 2,
            Self::F2(_) => 3,
            Self::F3(_) => 4,
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
impl Ord for ARG {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.order().cmp(&other.order())
    }
}

impl PartialOrd for ARG {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OP {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.order().cmp(&other.order())
    }
}

impl PartialOrd for OP {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub(crate) use crate::op::ARG::*;

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

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum B {
    I(usize),
    CONST(bool),
    VAR(usize),
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

#[derive(Clone, Copy)]
pub enum F {
    I(usize),
    CONST(f64),
    VAR(usize),
}

impl Default for F {
    fn default() -> Self {
        Self::CONST(0.0)
    }
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

impl Debug for F {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::I(i) => write!(f, "@{}", i),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    fn order(&self) -> u32 {
        match self {
            Self::BOP(_) => 1,
            Self::FOP(_) => 2,
            Self::FOP2(_) => 3,
            Self::FOP3(_) => 4,
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

#[derive(Debug, Clone)]
pub enum FOP {
    //---- Primitive Value Types:
    CONST(f64),
    VAR(usize),

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
        Self::CONST(0.0)
    }
}

impl PartialEq for FOP {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::CONST(s), Self::CONST(o)) => s.to_bits() == o.to_bits(),
            (Self::VAR(s), Self::VAR(o)) => s == o,
            // (Self::FROM_B(s), Self::FROM_B(o)) => s == o,
            (Self::ADD(s0, s1), Self::ADD(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::MUL(s0, s1), Self::MUL(o0, o1)) => (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0),
            (Self::NEG(s), Self::NEG(o)) => s == o,
            (Self::INV(s), Self::INV(o)) => s == o,
            (Self::REM(s0, s1), Self::REM(o0, o1)) => (s0, s1) == (o0, o1),

            (Self::IF(s0, s1, s2), Self::IF(o0, o1, o2)) => (s0, s1, s2) == (o0, o1, o2),
            (Self::STDFN(s), Self::STDFN(o)) => s == o,
            _ => false,
        }
    }
}

impl Eq for FOP {}

impl Hash for FOP {
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
            // Self::FROM_B(b) => {
            //     state.write_u8(3);
            //     b.hash(state);
            // }
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
            Self::IF(b, a0, a1) => {
                state.write_u8(12);
                b.hash(state);
                a0.hash(state);
                a1.hash(state);
            }
            Self::STDFN(ffn) => {
                state.write_u8(21);
                ffn.hash(state);
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return [T;2] type aka FOP2
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

macro_rules! make_array_FOP {
    ($N: literal, $ARG: ident, $OP: ident, $FN: ident) => {
        #[derive(Clone, Copy)]
        pub enum $ARG {
            I(usize),
            CONST([f64; $N]),
            VAR(usize),
            F(F),
        }

        impl Default for $ARG {
            fn default() -> Self {
                Self::CONST([0.0; $N])
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
                    Self::VAR(i) => write!(f, "VAR({:?})", i),
                    Self::F(f_) => write!(f, "{:?}", f_),
                }
            }
        }

        impl Hash for $ARG {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                match self {
                    Self::I(u) => {
                        state.write_u8(1);
                        state.write_usize(*u);
                    }
                    Self::CONST(c) => {
                        state.write_u8(2);
                        for i in c {
                            state.write_u64(i.to_bits());
                        }
                    }
                    Self::VAR(u) => {
                        state.write_u8(3);
                        state.write_usize(*u);
                    }
                    Self::F(f) => {
                        state.write_u8(4);
                        f.hash(state);
                    }
                }
            }
        }

        impl PartialEq for $ARG {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                match (self, other) {
                    (Self::I(s), Self::I(o)) => s == o,
                    (Self::CONST(s), Self::CONST(o)) => as_bytes(s) == as_bytes(o),
                    (Self::VAR(s), Self::VAR(o)) => s == o,
                    (Self::F(s), Self::F(o)) => s == o,
                    _ => false,
                }
            }
        }

        impl Eq for $ARG {}

        #[derive(Debug, Clone)]
        pub enum $OP {
            //---- Primitive Value Types:
            CONST([f64; $N]),
            VAR(usize),
            NEW([F; $N]),

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

        impl PartialEq for $OP {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                match (self, other) {
                    (Self::CONST(s), Self::CONST(o)) => as_bytes(s) == as_bytes(o),
                    (Self::VAR(s), Self::VAR(o)) => s == o,
                    // (Self::FROM_F(s), Self::FROM_F(o)) => s == o,
                    // (Self::FROM_B(s), Self::FROM_B(o)) => s == o,
                    (Self::NEW(s), Self::NEW(o)) => s == o,

                    (Self::ADD(s0, s1), Self::ADD(o0, o1)) => {
                        (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0)
                    }
                    (Self::MUL(s0, s1), Self::MUL(o0, o1)) => {
                        (s0, s1) == (o0, o1) || (s0, s1) == (o1, o0)
                    }
                    (Self::NEG(s), Self::NEG(o)) => s == o,

                    (Self::INV(s), Self::INV(o)) => s == o,
                    (Self::REM(s0, s1), Self::REM(o0, o1)) => (s0, s1) == (o0, o1),
                    (Self::POW(s0, s1), Self::POW(o0, o1)) => (s0, s1) == (o0, o1),

                    (Self::IF(s0, s1, s2), Self::IF(o0, o1, o2)) => (s0, s1, s2) == (o0, o1, o2),
                    (Self::STDFN(s), Self::STDFN(o)) => s == o,
                    _ => false,
                }
            }
        }
        impl Eq for $OP {}

        impl Hash for $OP {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                match self {
                    Self::CONST(c) => {
                        state.write_u8(1);
                        for i in c {
                            state.write_u64(i.to_bits());
                        }
                    }
                    Self::VAR(u) => {
                        state.write_u8(2);
                        state.write_usize(*u);
                    }
                    // Self::FROM_F(f) => {
                    //     state.write_u8(3);
                    //     f.hash(state);
                    // }
                    // Self::FROM_B(b) => {
                    //     state.write_u8(4);
                    //     b.hash(state);
                    // }
                    Self::NEW(a) => {
                        state.write_u8(5);
                        a.hash(state);
                    }
                    Self::NEG(a) => {
                        state.write_u8(6);
                        a.hash(state);
                    }
                    Self::INV(a) => {
                        state.write_u8(7);
                        a.hash(state);
                    }
                    Self::ADD(a0, a1) => {
                        state.write_u8(8);
                        state.write_u64(_hash(a0) ^ _hash(a1));
                    }
                    Self::MUL(a0, a1) => {
                        state.write_u8(9);
                        state.write_u64(_hash(a0) ^ _hash(a1));
                    }
                    Self::REM(a0, a1) => {
                        state.write_u8(10);
                        a0.hash(state);
                        a1.hash(state);
                    }
                    Self::POW(a0, a1) => {
                        state.write_u8(11);
                        a0.hash(state);
                        a1.hash(state);
                    }
                    Self::IF(b, a0, a1) => {
                        state.write_u8(12);
                        b.hash(state);
                        a0.hash(state);
                        a1.hash(state);
                    }
                    Self::STDFN(f) => {
                        state.write_u8(13);
                        f.hash(state);
                    }
                }
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
