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
//             Adress::F(i) => Fop(Fop::VAR(LOCAL(i))),
//             Adress::F2(i) => F2op(F2op::VAR(LOCAL(i))),
//             Adress::F3(i) => F3op(F3op::VAR(LOCAL(i))),
//         }
//     }
// }

#[derive(Debug, Clone)]
pub enum ICV {
    F(F),
    F2(F2),
    F3(F3),
    B(B),
}

impl ICV {
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

pub(crate) use crate::op::ICV::*;

impl From<ICV> for OP {
    fn from(value: ICV) -> Self {
        match value {
            F(F::CONST(c)) => Fop(Fop::CONST(c)),
            F(F::VAR(v)) => Fop(Fop::VAR(v)),
            F(F::I(i)) => Fop(Fop::I(i)),

            F2(F2::CONST(c)) => F2op(F2op::CONST(c)),
            F2(F2::VAR(v)) => F2op(F2op::VAR(v)),
            F2(F2::I(i)) => F2op(F2op::I(i)),

            F3(F3::CONST(c)) => F3op(F3op::CONST(c)),
            F3(F3::VAR(v)) => F3op(F3op::VAR(v)),
            F3(F3::I(i)) => F3op(F3op::I(i)),

            B(B::CONST(c)) => Bop(Bop::CONST(c)),
            B(B::VAR(v)) => Fop(Fop::VAR(v)),
            B(B::I(i)) => Fop(Fop::I(i)),

            _ => unreachable!(),
        }
    }
}
impl TryFrom<ICV> for F {
    type Error = Error;
    #[inline]
    fn try_from(value: ICV) -> Result<Self, Self::Error> {
        match value {
            ICV::F(f) => Ok(f),
            ICV::B(b) => Ok(b.into()),
            _ => Err(Error::Undefined("!!!!".into())),
        }
    }
}

impl TryFrom<&ICV> for F {
    type Error = Error;
    #[inline]
    fn try_from(value: &ICV) -> Result<Self, Self::Error> {
        match value {
            ICV::F(f) => Ok(*f),
            ICV::B(b) => Ok((*b).into()),
            _ => Err(Error::Undefined("!!!!".into())),
        }
    }
}

impl TryFrom<ICV> for B {
    type Error = Error;
    #[inline]
    fn try_from(value: ICV) -> Result<Self, Self::Error> {
        match value {
            ICV::B(b) => Ok(b),
            ICV::F(f) => Ok(f.into()),
            _ => Err(Error::Undefined("!!!!".into())),
        }
    }
}
impl TryFrom<&ICV> for B {
    type Error = Error;
    #[inline]
    fn try_from(value: &ICV) -> Result<Self, Self::Error> {
        match value {
            ICV::B(b) => Ok(*b),
            ICV::F(f) => Ok((*f).into()),
            _ => Err(Error::Undefined("!!!!".into())),
        }
    }
}

impl From<B> for ICV {
    #[inline]
    fn from(value: B) -> Self {
        Self::B(value)
    }
}

impl From<F> for ICV {
    #[inline]
    fn from(value: F) -> Self {
        Self::F(value)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Clone, Copy, Enum)]
pub enum F {
    I(usize),
    CONST(f64),
    VAR(usize),
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
    Bop(Bop),
    Fop(Fop),
    F2op(F2op),
    F3op(F3op),
}

pub(crate) use crate::op::OP::*;

impl Default for OP {
    fn default() -> Self {
        Fop(Fop::default())
    }
}

impl OP {
    #[inline]
    pub fn optype(&self) -> Type {
        match self {
            Self::Bop(_) => Type::B,
            Self::Fop(_) => Type::F,
            Self::F2op(_) => Type::F2,
            Self::F3op(_) => Type::F3,
        }
    }

    #[inline]
    fn order_with_const(&self) -> u32 {
        match self {
            Self::Bop(Bop::CONST(_)) => 0,
            Self::Fop(Fop::CONST(_)) => 1,
            Self::F2op(F2op::CONST(_)) => 2,
            Self::F3op(F3op::CONST(_)) => 3,

            Self::Bop(_) => 10,
            Self::Fop(_) => 11,
            Self::F2op(_) => 12,
            Self::F3op(_) => 13,
        }
    }

    // #[inline]
    // fn update_i(&mut self, f: FN)
    // where
    //     FN: FnOnce(usize) -> usize + Copy,
    // {
    //     match self {
    //         Self::Fop(instr) => {
    //             instr.update_i(f);
    //         }
    //         Self::F2op(instr) => {
    //             instr.update_i(f);
    //         }
    //     }
    // }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return bool type aka Bop
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub enum Bop {
    I(usize),
    //---- Primitive Value Types:
    CONST(bool),
    // STORE(usize, usize),
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

impl Default for Bop {
    fn default() -> Self {
        Self::CONST(false)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return scalar T type aka Fop
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq)]
pub enum Fop {
    I(usize),
    //---- Primitive Value Types:
    CONST(f64),
    VAR(usize),
    // STORE(usize, usize),

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
    FN(Ffn),
}

impl Default for Fop {
    fn default() -> Self {
        Self::CONST(Default::default())
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// OPS that return [T;2] type aka F2op
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

macro_rules! make_array_FOP {
    ($N: literal, $ICV: ident, $OP: ident, $FN: ident) => {
        #[derive(Clone, Copy, Enum)]
        pub enum $ICV {
            I(usize),
            CONST([f64; $N]),
            VAR(usize),
            F(F),
        }

        impl PartialEq for $ICV {
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
        impl Eq for $ICV {}
        impl Ord for $ICV {
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

        impl PartialOrd for $ICV {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Hash for $ICV {
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

        impl Default for $ICV {
            fn default() -> Self {
                Self::CONST(Default::default())
            }
        }

        impl From<[f64; $N]> for $ICV {
            #[inline]
            fn from(value: [f64; $N]) -> Self {
                Self::CONST(value)
            }
        }

        impl From<f64> for $ICV {
            #[inline]
            fn from(value: f64) -> Self {
                Self::CONST([value; $N])
            }
        }

        impl From<F> for $ICV {
            #[inline]
            fn from(value: F) -> Self {
                match value {
                    F::CONST(c) => Self::CONST([c; $N]),
                    _ => Self::F(value),
                }
            }
        }

        impl From<B> for $ICV {
            #[inline]
            fn from(value: B) -> Self {
                F::from(value).into()
            }
        }

        impl From<$ICV> for ICV {
            #[inline]
            fn from(value: $ICV) -> Self {
                Self::$ICV(value)
            }
        }

        impl TryFrom<ICV> for $ICV {
            type Error = Error;
            #[inline]
            fn try_from(value: ICV) -> Result<Self, Self::Error> {
                match value {
                    ICV::$ICV(ff) => Ok(ff),
                    ICV::F(f) => Ok(f.into()),
                    ICV::B(b) => Ok(b.into()),
                    _ => Err(Error::Undefined("!!!!".into())),
                }
            }
        }
        impl TryFrom<&ICV> for $ICV {
            type Error = Error;
            #[inline]
            fn try_from(value: &ICV) -> Result<Self, Self::Error> {
                match value {
                    ICV::$ICV(ff) => Ok(*ff),
                    ICV::F(f) => Ok((*f).into()),
                    ICV::B(b) => Ok((*b).into()),
                    _ => Err(Error::Undefined("!!!!".into())),
                }
            }
        }

        impl Debug for $ICV {
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
            VAR(usize),
            NEW([F; $N]),
            // STORE(usize, usize),

            //---- Unary Ops:
            NEG($ICV),
            INV($ICV),

            //---- Binary Math Ops:
            ADD($ICV, $ICV),

            // A Sub(x) is converted to an FADD(FNEG(x)).
            MUL($ICV, $ICV),
            // A Div(n,d) is converted to a FMUL(n,FINV(d)).
            REM($ICV, $ICV),
            POW($ICV, $ICV),

            //---- Functions:
            IF(B, $ICV, $ICV),
            FN($FN),
        }

        impl Default for $OP {
            fn default() -> Self {
                Self::CONST([0.0; $N])
            }
        }
    };
}

make_array_FOP!(2, F2, F2op, F2fn);
make_array_FOP!(3, F3, F3op, F3fn);

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
