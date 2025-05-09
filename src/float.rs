use crate::{and, map, map8, map_n, max, min};
use array_init;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Add, Div, Index, Mul, Neg, Sub};
use wide::*;

pub trait Mask: Copy + Clone + PartialEq + Default {
    const FALSE: Self;
    const TRUE: Self;
    const ZERO: Self = Self::FALSE;
    const ONE: Self = Self::TRUE;

    fn from_bool(b: bool) -> Self;
    fn not(self) -> Self;
    fn or(self, other: Self) -> Self;
    fn and(self, other: Self) -> Self;

    fn if_(cond: Self, then: Self, else_: Self) -> Self;
}

pub trait Float:
    Copy
    + Clone
    + PartialEq
    + Default
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
{
    type Mask: Mask;

    const ZERO: Self;
    const ONE: Self;
    const HALF: Self;
    const E: Self;
    const PI: Self;

    // fn add(self, other: Self) -> Self;
    // fn sub(self, other: Self) -> Self;
    // fn mul(self, other: Self) -> Self;
    // fn div(self, other: Self) -> Self;
    fn rem(self, other: Self) -> Self;
    fn pow(self, n: Self) -> Self;
    // fn neg(self) -> Self;

    fn floor(self) -> Self;
    fn ceil(self) -> Self;
    fn round(self) -> Self;
    fn recip(self) -> Self;
    fn abs(self) -> Self;
    fn ln(self) -> Self;
    fn min(self, other: Self) -> Self;
    fn max(self, other: Self) -> Self;
    fn sqrt(self) -> Self;
    fn cbrt(self) -> Self;
    fn hypot(self, other: Self) -> Self;
    fn sin(self) -> Self;
    fn cos(self) -> Self;
    fn deg(self) -> Self;
    fn rad(self) -> Self;

    #[inline(always)]
    fn lerp(self, other: Self, t: Self) -> Self {
        self * (Self::ONE - t) + other * t
        // self.mul(Self::ONE.sub(t)).sub(other.mul(t))
    }

    #[inline(always)]
    fn bias(self, b: Self) -> Self {
        self.pow(b.ln() / Self::HALF.ln())
        // self.pow(b.ln().div(Self::HALF.ln()))
    }

    #[inline(always)]
    fn fit(self, oldmin: Self, oldmax: Self, newmin: Self, newmax: Self) -> Self {
        newmin + (self - oldmin) * (newmax - newmin) / (oldmax - oldmin)
        // newmin.add(
        //     self.sub(oldmin)
        //         .mul(newmax.sub(newmin))
        //         .div(oldmax.sub(oldmin)),
        // )
    }
    #[inline(always)]
    fn fit01(self, newmin: Self, newmax: Self) -> Self {
        newmin + self * (newmax - newmin)
        // newmin.add(self.mul(newmax.sub(newmin)))
    }
    #[inline(always)]
    fn clamp(self, min: Self, max: Self) -> Self {
        self.max(min).min(max)
    }
    #[inline(always)]
    fn clamp01(self) -> Self {
        self.max(Self::ZERO).min(Self::ONE)
    }

    fn eq(self, other: Self) -> Self::Mask;
    #[inline(always)]
    fn ne(self, other: Self) -> Self::Mask {
        self.eq(other).not()
    }

    fn lt(self, other: Self) -> Self::Mask;
    fn le(self, other: Self) -> Self::Mask;
    fn gt(self, other: Self) -> Self::Mask;
    fn ge(self, other: Self) -> Self::Mask;

    fn from_f64(f: f64) -> Self;
    fn from_mask(b: Self::Mask) -> Self;

    #[inline(always)]
    fn to_mask(self) -> Self::Mask {
        self.ne(Self::ZERO)
    }

    fn if_(cond: Self::Mask, then: Self, else_: Self) -> Self;
}

pub trait Float2<T: Float>:
    Copy + Clone + PartialEq + Default + Index<usize, Output = T> + From<[T; 2]> + Into<[T; 2]>
{
    #[inline(always)]
    fn if_(cond: T::Mask, then: Self, else_: Self) -> Self {
        [
            T::if_(cond, then[0], else_[0]),
            T::if_(cond, then[1], else_[1]),
        ]
        .into()
    }

    #[inline(always)]
    fn mincomp(self) -> T {
        self[0].min(self[1])
    }

    #[inline(always)]
    fn maxcomp(self) -> T {
        self[0].max(self[1])
    }

    fn eq(self, other: Self) -> T::Mask {
        self[0].eq(other[0]).and(self[1].eq(other[1]))
    }

    #[inline(always)]
    fn ne(self, other: Self) -> T::Mask {
        self[0].ne(other[0]).and(self[1].ne(other[1]))
    }
}

pub trait Float3<T: Float>:
    Copy + Clone + PartialEq + Default + Index<usize, Output = T> + From<[T; 3]> + Into<[T; 3]>
{
    #[inline(always)]
    fn if_(cond: T::Mask, then: Self, else_: Self) -> Self {
        [
            T::if_(cond, then[0], else_[0]),
            T::if_(cond, then[1], else_[1]),
            T::if_(cond, then[2], else_[2]),
        ]
        .into()
    }

    #[inline(always)]
    fn mincomp(self) -> T {
        self[0].min(self[1]).min(self[2])
    }

    #[inline(always)]
    fn maxcomp(self) -> T {
        self[0].max(self[1]).max(self[2])
    }

    fn eq(self, other: Self) -> T::Mask {
        self[0]
            .eq(other[0])
            .and(self[1].eq(other[1]))
            .and(self[2].eq(other[2]))
    }

    #[inline(always)]
    fn ne(self, other: Self) -> T::Mask {
        self[0]
            .ne(other[0])
            .and(self[1].ne(other[1]))
            .and(self[2].ne(other[2]))
    }
}

impl Mask for bool {
    const FALSE: Self = false;
    const TRUE: Self = true;

    #[inline(always)]
    fn from_bool(b: bool) -> Self {
        b
    }
    #[inline(always)]
    fn not(self) -> Self {
        !self
    }
    #[inline(always)]
    fn or(self, other: Self) -> Self {
        self || other
    }
    #[inline(always)]
    fn and(self, other: Self) -> Self {
        self && other
    }
    #[inline(always)]
    fn if_(cond: Self, then: Self, else_: Self) -> Self {
        if cond {
            then
        } else {
            else_
        }
    }
}

macro_rules! impl_float {
    ($T:ident) => {
        impl Float for $T {
            type Mask = bool;

            const ZERO: Self = 0.0;
            const ONE: Self = 1.0;
            const HALF: Self = 0.5;
            const E: Self = std::$T::consts::E;
            const PI: Self = std::$T::consts::PI;

            #[inline(always)]
            fn eq(self, other: Self) -> Self::Mask {
                self == other
            }
            #[inline(always)]
            fn ne(self, other: Self) -> Self::Mask {
                self != other
            }

            #[inline(always)]
            fn lt(self, other: Self) -> Self::Mask {
                self < other
            }
            #[inline(always)]
            fn le(self, other: Self) -> Self::Mask {
                self <= other
            }
            #[inline(always)]
            fn gt(self, other: Self) -> Self::Mask {
                (self > other).into()
            }
            #[inline(always)]
            fn ge(self, other: Self) -> Self::Mask {
                self >= other
            }

            // #[inline(always)]
            // fn add(self, other: Self) -> Self {
            //     self + other
            // }
            // #[inline(always)]
            // fn sub(self, other: Self) -> Self {
            //     self - other
            // }
            // #[inline(always)]
            // fn mul(self, other: Self) -> Self {
            //     self * other
            // }
            // #[inline(always)]
            // fn div(self, other: Self) -> Self {
            //     self / other
            // }
            // #[inline(always)]
            // fn neg(self) -> Self {
            //     -self
            // }
            #[inline(always)]
            fn rem(self, other: Self) -> Self {
                ((self % other) + other) % other
            }
            #[inline(always)]
            fn floor(self) -> Self {
                self.floor()
            }
            #[inline(always)]
            fn ceil(self) -> Self {
                self.ceil()
            }
            #[inline(always)]
            fn round(self) -> Self {
                self.round()
            }
            #[inline(always)]
            fn recip(self) -> Self {
                self.recip()
            }
            #[inline(always)]
            fn abs(self) -> Self {
                self.abs()
            }
            #[inline(always)]
            fn ln(self) -> Self {
                self.ln()
            }
            #[inline(always)]
            fn min(self, other: Self) -> Self {
                self.min(other)
            }
            #[inline(always)]
            fn max(self, other: Self) -> Self {
                self.max(other)
            }
            #[inline(always)]
            fn pow(self, n: Self) -> Self {
                self.powf(n)
            }
            #[inline(always)]
            fn sqrt(self) -> Self {
                self.sqrt()
            }
            #[inline(always)]
            fn cbrt(self) -> Self {
                self.cbrt()
            }
            #[inline(always)]
            fn hypot(self, other: Self) -> Self {
                self.hypot(other)
            }
            #[inline(always)]
            fn sin(self) -> Self {
                self.sin()
            }
            #[inline(always)]
            fn cos(self) -> Self {
                self.cos()
            }
            #[inline(always)]
            fn deg(self) -> Self {
                self.to_degrees()
            }
            #[inline(always)]
            fn rad(self) -> Self {
                self.to_radians()
            }

            #[inline(always)]
            fn from_f64(f: f64) -> Self {
                f as $T
            }
            #[inline(always)]
            fn from_mask(b: Self::Mask) -> Self {
                b.into()
            }

            #[inline(always)]
            fn if_(cond: Self::Mask, then: Self, else_: Self) -> Self {
                if cond {
                    then
                } else {
                    else_
                }
            }
        }
    };
}

impl_float!(f32);
impl_float!(f64);

impl Mask for f32x8 {
    const FALSE: Self = Self::ZERO;
    const TRUE: Self = unsafe { std::mem::transmute([u32::MAX; 8]) };

    #[inline(always)]
    fn from_bool(b: bool) -> Self {
        if b {
            Self::TRUE
        } else {
            Self::FALSE
        }
    }
    #[inline(always)]
    fn not(self) -> Self {
        !self
    }
    #[inline(always)]
    fn or(self, other: Self) -> Self {
        self | other
    }
    #[inline(always)]
    fn and(self, other: Self) -> Self {
        self & other
    }

    #[inline(always)]
    fn if_(cond: Self, then: Self, else_: Self) -> Self {
        cond.blend(else_, then)
    }
}

impl Float for f32x8 {
    type Mask = Self;

    const ZERO: Self = f32x8::ZERO;
    const ONE: Self = f32x8::ONE;
    const HALF: Self = f32x8::HALF;
    const E: Self = f32x8::E;
    const PI: Self = f32x8::PI;

    #[inline(always)]
    fn eq(self, other: Self) -> Self::Mask {
        self.cmp_eq(other)
    }
    #[inline(always)]
    fn ne(self, other: Self) -> Self::Mask {
        self.cmp_ne(other)
    }

    #[inline(always)]
    fn lt(self, other: Self) -> Self::Mask {
        self.cmp_lt(other)
    }
    #[inline(always)]
    fn le(self, other: Self) -> Self::Mask {
        self.cmp_le(other)
    }
    #[inline(always)]
    fn gt(self, other: Self) -> Self::Mask {
        self.cmp_gt(other)
    }
    #[inline(always)]
    fn ge(self, other: Self) -> Self::Mask {
        self.cmp_ge(other)
    }

    // #[inline(always)]
    // fn add(self, other: Self) -> Self {
    //     self + other
    // }
    // #[inline(always)]
    // fn sub(self, other: Self) -> Self {
    //     self - other
    // }
    // #[inline(always)]
    // fn mul(self, other: Self) -> Self {
    //     self * other
    // }
    // #[inline(always)]
    // fn div(self, other: Self) -> Self {
    //     self / other
    // }
    // #[inline(always)]
    // fn neg(self) -> Self {
    //     -self
    // }
    #[inline(always)]
    fn rem(self, other: Self) -> Self {
        map8!(Float::rem, self.to_array(), other.to_array()).into()
    }

    #[inline(always)]
    fn floor(self) -> Self {
        map8!(Float::floor, self.to_array()).into()
    }
    #[inline(always)]
    fn ceil(self) -> Self {
        map8!(Float::ceil, self.to_array()).into()
    }
    #[inline(always)]
    fn round(self) -> Self {
        self.round()
    }
    #[inline(always)]
    fn recip(self) -> Self {
        self.recip()
    }
    #[inline(always)]
    fn abs(self) -> Self {
        self.abs()
    }
    #[inline(always)]
    fn ln(self) -> Self {
        self.ln()
    }
    #[inline(always)]
    fn min(self, other: Self) -> Self {
        self.fast_min(other)
    }
    #[inline(always)]
    fn max(self, other: Self) -> Self {
        self.fast_max(other)
    }
    #[inline(always)]
    fn pow(self, n: Self) -> Self {
        self.pow_f32x8(n)
    }
    #[inline(always)]
    fn sqrt(self) -> Self {
        self.sqrt()
    }
    #[inline(always)]
    fn cbrt(self) -> Self {
        map8!(Float::cbrt, self.to_array()).into()
    }
    #[inline(always)]
    fn hypot(self, other: Self) -> Self {
        map8!(Float::hypot, self.to_array(), other.to_array()).into()
    }
    #[inline(always)]
    fn sin(self) -> Self {
        self.sin()
    }
    #[inline(always)]
    fn cos(self) -> Self {
        self.cos()
    }
    #[inline(always)]
    fn deg(self) -> Self {
        self.to_degrees()
    }
    #[inline(always)]
    fn rad(self) -> Self {
        self.to_radians()
    }

    #[inline(always)]
    fn from_f64(f: f64) -> Self {
        (f as f32).into()
    }
    #[inline(always)]
    fn from_mask(b: Self::Mask) -> Self {
        Self::blend(b, Self::ZERO, Self::ONE)
    }
    #[inline(always)]
    fn if_(cond: Self::Mask, then: Self, else_: Self) -> Self {
        cond.blend(else_, then)
    }
}

impl<T: Float> Float2<T> for [T; 2] {}
impl<T: Float> Float3<T> for [T; 3] {}

// macro_rules! _impl_FloatMath_for_array {

// macro_rules! _impl_FloatMath_for_array {
//     ($N:tt, $($f:ident(self $(, $a:ident)*),)*) => {
//         impl<T: FloatConst> FloatConst for [T; $N] {
//             const ZERO: Self = [T::ZERO; $N];
//             const ONE: Self = [T::ONE; $N];
//             const HALF: Self = [T::HALF; $N];
//             const E: Self = [T::E; $N];
//             const PI: Self = [T::PI; $N];
//         }
//         impl<T: Float> Float for [T; $N] {
//             $(
//                 #[inline(always)]
//                 fn $f(self $(, $a:Self)*) -> Self {
//                     map_n!($N, T::$f, self $(, $a)*)
//                 }
//             )*
//         }
//     };
// }

// macro_rules! impl_FloatMath_for_array {
//     ($N: tt) => {
//         _impl_FloatMath_for_array!(
//             $N,
//             add(self, other),
//             sub(self, other),
//             mul(self, other),
//             div(self, other),
//             rem(self, other),
//             pow(self, n),
//             neg(self),
//             deg(self),
//             rad(self),
//             floor(self),
//             ceil(self),
//             round(self),
//             recip(self),
//             abs(self),
//             ln(self),
//             min(self, other),
//             max(self, other),
//             sqrt(self),
//             cbrt(self),
//             hypot(self, other),
//             sin(self),
//             cos(self),
//             bias(self, b),
//             fit(self, oldmin, oldmax, newmin, newmax),
//             clamp(self, min, max),
//         );
//     };
// }
// impl_FloatMath_for_array!(2);
// impl_FloatMath_for_array!(3);

// macro_rules! impl_Eq_for_array {
//     ($N:literal, $($i:literal),+) => {
//         impl<T: Eq + Copy> Eq for [T; $N] {
//             type Mask = T::Mask;

//             #[inline(always)]
//             fn eq(self, other: Self) -> Self::Mask {
//                 and!(
//                     $(self[$i].eq(other[$i])),+
//                 )
//             }

//             #[inline(always)]
//             fn ne(self, other: Self) -> Self::Mask {
//                 and!(
//                     $(self[$i].ne(other[$i])),+
//                 )
//             }
//         }
//     };
// }

// impl_Eq_for_array!(2, 0, 1);
// impl_Eq_for_array!(3, 0, 1, 2);

#[cfg(test)]
mod tests {
    use super::*;
}
