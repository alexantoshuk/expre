use bytemuck::*;
use std::hash::{Hash, Hasher};
use std::ops::{Add, Div, Mul, Neg, Sub};
use wide::f32x8;

pub trait Float:
    Pod
    + PartialEq
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
{
    const ZERO: Self;
    const ONE: Self;
    const HALF: Self;
    const E: Self;
    const PI: Self;

    fn from_f64(f: f64) -> Self;
    // fn eq(self, other: Self) -> Self;
    // fn ne(self, other: Self) -> Self;
    // fn lt(self, other: Self) -> Self;
    // fn lte(self, other: Self) -> Self;
    // fn gt(self, other: Self) -> Self;
    // fn gte(self, other: Self) -> Self;

    fn select(self, then: Self, else_: Self) -> Self;

    fn rem(self, other: Self) -> Self;
    fn floor(self) -> Self;
    fn ceil(self) -> Self;
    fn round(self) -> Self;
    fn clamp(self, min: Self, max: Self) -> Self;
    fn recip(self) -> Self;
    fn abs(self) -> Self;
    fn min(self, other: Self) -> Self;
    fn max(self, other: Self) -> Self;
    fn pow(self, n: Self) -> Self;
    fn sqrt(self) -> Self;
    fn cbrt(self) -> Self;
    fn hypot(self, other: Self) -> Self;
}

// pub trait CastFrom<T>: Sized {
//     fn cast_from(value: T) -> Self;
// }

// pub trait CastInto<T>: Sized {
//     fn cast_into(self) -> T;
// }

// impl<T> CastFrom<T> for T {
//     #[inline(always)]
//     fn cast_from(value: T) -> Self {
//         value
//     }
// }

// impl<T, U> CastInto<U> for T
// where
//     U: CastFrom<T>,
// {
//     #[inline(always)]
//     fn cast_into(self) -> U {
//         U::cast_from(self)
//     }
// }

// impl CastFrom<f64> for f32 {
//     #[inline(always)]
//     fn cast_from(value: f64) -> Self {
//         value as f32
//     }
// }
// impl CastFrom<f64> for f64 {
//     #[inline(always)]
//     fn cast_from(value: f64) -> Self {
//         value
//     }
// }

// impl CastFrom<f64> for f32x8 {
//     #[inline(always)]
//     fn cast_from(value: f64) -> Self {
//         f32x8::splat(value as f32)
//     }
// }

// impl CastFrom<f32> for f32x8 {
//     #[inline(always)]
//     fn cast_from(value: f32) -> Self {
//         f32x8::splat(value)
//     }
// }

// impl<const N: usize> CastFrom<f32> for [f32; N] {
//     #[inline(always)]
//     fn cast_from(value: f32) -> Self {
//         [value; N]
//     }
// }

// impl<const N: usize> CastFrom<f64> for [f32; N] {
//     #[inline(always)]
//     fn cast_from(value: f64) -> Self {
//         [value as f32; N]
//     }
// }

// impl<U: CastFrom<T>, T: Copy> CastFrom<[T; 2]> for [U; 2] {
//     #[inline(always)]
//     fn cast_from([x, y]: [T; 2]) -> Self {
//         [x.cast_into(), y.cast_into()]
//     }
// }

// impl<U: CastFrom<T>, T: Copy> CastFrom<[T; 3]> for [U; 3] {
//     #[inline(always)]
//     fn cast_from([x, y, z]: [T; 3]) -> Self {
//         [x.cast_into(), y.cast_into(), z.cast_into()]
//     }
// }

// impl<U: CastFrom<T>, T: Copy> CastFrom<[T; 4]> for [U; 4] {
//     #[inline(always)]
//     fn cast_from([x, y, z, w]: [T; 4]) -> Self {
//         [x.cast_into(), y.cast_into(), z.cast_into(), w.cast_into()]
//     }
// }

macro_rules! impl_float {
    ($T:ident) => {
        impl Float for $T {
            const ZERO: Self = 0.0;
            const ONE: Self = 1.0;
            const HALF: Self = 0.5;
            const E: Self = std::$T::consts::E;
            const PI: Self = std::$T::consts::PI;

            #[inline(always)]
            fn from_f64(f: f64) -> Self {
                f as $T
            }
            // fn eq(self, other: Self) -> Self;
            // fn ne(self, other: Self) -> Self;
            // fn lt(self, other: Self) -> Self;
            // fn lte(self, other: Self) -> Self;
            // fn gt(self, other: Self) -> Self;
            // fn gte(self, other: Self) -> Self;

            #[inline(always)]
            fn select(self, then: Self, else_: Self) -> Self {
                if self != 0.0 {
                    then
                } else {
                    else_
                }
            }

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
            fn clamp(self, min: Self, max: Self) -> Self {
                self.max(min).min(max)
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
        }
    };
}

impl_float!(f32);
impl_float!(f64);

macro_rules! apply {
    ( $f:ident, $a:expr, $($i:literal),+) => {
        [
            $($a[$i].$f()),+
        ]
    };
    ( $f:ident, $a:expr, $b:expr, $($i:literal),+) => {
        [
            $($a[$i].$f($b[$i])),+
        ]
    };
    ( $f:ident, $a:expr, $b:expr, $c:expr, $($i:literal),+) => {
        [
            $($a[$i].$f($b[$i], $c[$i])),+
        ]
    };
}
macro_rules! apply_x8 {
    ( $f:ident, $a:expr) => {
        apply!($f, $a, 0, 1, 2, 3, 4, 5, 6, 7)
    };
    ( $f:ident, $a:expr, $b:expr) => {
        apply!($f, $a, $b, 0, 1, 2, 3, 4, 5, 6, 7)
    };
    ( $f:ident, $a:expr, $b:expr, $c:expr) => {
        apply!($f, $a, $b, $c, 0, 1, 2, 3, 4, 5, 6, 7)
    };
}
impl Float for f32x8 {
    const ZERO: Self = f32x8::ZERO;
    const ONE: Self = f32x8::ONE;
    const HALF: Self = f32x8::HALF;
    const E: Self = f32x8::E;
    const PI: Self = f32x8::PI;

    #[inline(always)]
    fn from_f64(f: f64) -> Self {
        (f as f32).into()
    }

    #[inline(always)]
    fn select(self, then: Self, else_: Self) -> Self {
        self.blend(else_, then)
    }

    #[inline(always)]
    fn rem(self, other: Self) -> Self {
        apply_x8!(rem, self.to_array(), other.to_array()).into()
    }
    #[inline(always)]
    fn floor(self) -> Self {
        apply_x8!(floor, self.to_array()).into()
    }
    #[inline(always)]
    fn ceil(self) -> Self {
        apply_x8!(ceil, self.to_array()).into()
    }
    #[inline(always)]
    fn round(self) -> Self {
        self.round()
    }
    #[inline(always)]
    fn clamp(self, min: Self, max: Self) -> Self {
        self.max(min).min(max)
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
    fn min(self, other: Self) -> Self {
        self.min(other)
    }
    #[inline(always)]
    fn max(self, other: Self) -> Self {
        self.max(other)
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
        apply_x8!(cbrt, self.to_array()).into()
    }
    #[inline(always)]
    fn hypot(self, other: Self) -> Self {
        apply_x8!(hypot, self.to_array(), other.to_array()).into()
    }
}

// macro_rules! impl_float_array {
//     ( $N:literal, $($i:literal),+) => {
//         impl<T: Float> Float for [T; $N] {
//             type CONST = [f64;$N];
//             const ZERO: Self = [T::ZERO; $N];
//             const ONE: Self = [T::ONE; $N];
//             const HALF: Self = [T::HALF; $N];
//             const E: Self = [T::E; $N];
//             const PI: Self = [T::PI; $N];

//             #[inline(always)]
//             fn select(self, then:Self, else_:Self) -> Self {
//                 [
//                     $(self[$i].select(then[$i], else_[$i])),+
//                 ]
//             }

//             #[inline(always)]
//             fn add(self, other: Self) -> Self {
//                 [
//                     $(self[$i].add(other[$i])),+
//                 ]
//             }
//             #[inline(always)]
//             fn sub(self, other: Self) -> Self {
//                 [
//                     $(self[$i].sub(other[$i])),+
//                 ]
//             }
//             #[inline(always)]
//             fn mul(self, other: Self) -> Self {
//                 [
//                     $(self[$i].mul(other[$i])),+
//                 ]
//             }
//             #[inline(always)]
//             fn div(self, other: Self) -> Self {
//                 [
//                     $(self[$i].div(other[$i])),+
//                 ]
//             }
//             #[inline(always)]
//             fn neg(self) -> Self {
//                 [
//                     $(self[$i].neg()),+
//                 ]
//             }
//             #[inline(always)]
//             fn rem(self, other:Self) -> Self {
//                 [
//                     $(self[$i].rem(other[$i])),+
//                 ]
//             }
//             #[inline(always)]
//             fn floor(self) -> Self {
//                 [
//                     $(self[$i].floor()),+
//                 ]
//             }
//             #[inline(always)]
//             fn ceil(self) -> Self {
//                 [
//                     $(self[$i].ceil()),+
//                 ]
//             }
//             #[inline(always)]
//             fn clamp(self, min:Self, max:Self) -> Self {
//                 [
//                     $(self[$i].clamp(min[$i], max[$i])),+
//                 ]
//             }
//             #[inline(always)]
//             fn recip(self) -> Self {
//                 [
//                     $(self[$i].recip()),+
//                 ]
//             }
//             #[inline(always)]
//             fn abs(self) -> Self {
//                 [
//                     $(self[$i].abs()),+
//                 ]
//             }
//             #[inline(always)]
//             fn min(self, other: Self) -> Self {
//                 [
//                     $(self[$i].min(other[$i])),+
//                 ]
//             }
//             #[inline(always)]
//             fn max(self, other: Self) -> Self {
//                 [
//                     $(self[$i].max(other[$i])),+
//                 ]
//             }
//             #[inline(always)]
//             fn pow(self, n: Self) -> Self {
//                 [
//                     $(self[$i].pow(n[$i])),+
//                 ]
//             }
//             #[inline(always)]
//             fn sqrt(self) -> Self {
//                 [
//                     $(self[$i].sqrt()),+
//                 ]
//             }
//             #[inline(always)]
//             fn cbrt(self) -> Self {
//                 [
//                     $(self[$i].cbrt()),+
//                 ]
//             }
//             #[inline(always)]
//             fn hypot(self, other: Self) -> Self {
//                 [
//                     $(self[$i].hypot(other[$i])),+
//                 ]
//             }
//         }
//     };
// }

// impl_float_array!(2, 0, 1);
// impl_float_array!(3, 0, 1, 2);
// impl_float_array!(4, 0, 1, 2, 3);

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // fn test_add_float_arrays() {
    //     let a = [1.0, 3.0f32];
    //     let b = [1.0, 4.0];
    //     let result = a.add(b);
    //     assert_eq!(result, [2.0, 7.0]);

    //     let a = [1.0, 2.0, 3.0f32];
    //     let b = [1.0, 2.0, 4.0];
    //     let result = a.add(b);
    //     assert_eq!(result, [2.0, 4.0, 7.0]);

    //     let a = [1.0, 2.0, 3.0, 5.0f32];
    //     let b = [1.0, 2.0, 4.0, 2.0];
    //     let result = a.add(b);
    //     assert_eq!(result, [2.0, 4.0, 7.0, 7.0]);

    //     let a = [1.0, 3.0f64];
    //     let b = [1.0, 4.0];
    //     let result = a.add(b);
    //     assert_eq!(result, [2.0, 7.0]);

    //     let a = [1.0, 2.0, 3.0f64];
    //     let b = [1.0, 2.0, 4.0];
    //     let result = a.add(b);
    //     assert_eq!(result, [2.0, 4.0, 7.0]);

    //     let a = [1.0, 2.0, 3.0, 5.0f64];
    //     let b = [1.0, 2.0, 4.0, 2.0];
    //     let result = a.add(b);
    //     assert_eq!(result, [2.0, 4.0, 7.0, 7.0]);
    // }

    // #[test]
    // fn test_add_f32x8_arrays() {
    //     let a = [f32x8::cast_from(1.0), f32x8::cast_from(3.0)];
    //     let b = [f32x8::cast_from(1.0), f32x8::cast_from(4.0)];
    //     let result: [f32x8; 2] = a.add(b);
    //     assert_eq!(result, [2.0.cast_into(), 7.0.cast_into()]);

    //     let a = [
    //         f32x8::cast_from(1.0),
    //         f32x8::cast_from(3.0),
    //         f32x8::cast_from(5.0),
    //     ];
    //     let b = [
    //         f32x8::cast_from(1.0),
    //         f32x8::cast_from(4.0),
    //         f32x8::cast_from(1.0),
    //     ];
    //     let result = a.add(b);
    //     assert_eq!(result, <[f32x8; 3]>::cast_from([2.0f32, 7.0, 6.0]));
    // }
}
