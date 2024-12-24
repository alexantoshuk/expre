use bytemuck::*;
use std::hash::{Hash, Hasher};
use wide::f32x8;

pub trait FromF64 {
    fn from_f64(f: f64) -> Self;
}

impl FromF64 for f32 {
    #[inline(always)]
    fn from_f64(f: f64) -> Self {
        f as f32
    }
}

pub trait Float: Pod + PartialEq {
    const ZERO: Self;
    const ONE: Self;
    const HALF: Self;
    const E: Self;
    const PI: Self;

    fn from_f64(f: f64) -> Self;

    fn add(self, other: Self) -> Self;
    fn sub(self, other: Self) -> Self;
    fn mul(self, other: Self) -> Self;
    fn div(self, other: Self) -> Self;
    fn rem(self, other: Self) -> Self;
    fn neg(self) -> Self;
    fn select(self, then: Self, else_: Self) -> Self;

    // fn eq(self, other: Self) -> Self;
    // fn ne(self, other: Self) -> Self;
    // fn lt(self, other: Self) -> Self;
    // fn lte(self, other: Self) -> Self;
    // fn gt(self, other: Self) -> Self;
    // fn gte(self, other: Self) -> Self;

    fn floor(self) -> Self;
    fn ceil(self) -> Self;
    fn round(self) -> Self;
    fn recip(self) -> Self;
    fn abs(self) -> Self;
    fn ln(self) -> Self;
    fn min(self, other: Self) -> Self;
    fn max(self, other: Self) -> Self;
    fn pow(self, n: Self) -> Self;
    fn sqrt(self) -> Self;
    fn cbrt(self) -> Self;
    fn hypot(self, other: Self) -> Self;
    fn sin(self) -> Self;
    fn cos(self) -> Self;

    #[inline(always)]
    fn bias(self, b: Self) -> Self {
        self.pow(b.ln().div(Self::HALF.ln()))
    }
    #[inline(always)]
    fn fit(self, oldmin: Self, oldmax: Self, newmin: Self, newmax: Self) -> Self {
        // newmin + (self-oldmin)*(newmax-newmin)/(oldmax-oldmin)
        newmin.add(
            self.sub(oldmin)
                .mul(newmax.sub(newmin))
                .div(oldmax.sub(oldmin)),
        )
    }
    #[inline(always)]
    fn fit01(self, newmin: Self, newmax: Self) -> Self {
        //newmin + self*(newmax-newmin)
        newmin.add(self.mul(newmax.sub(newmin)))
    }
    #[inline(always)]
    fn clamp(self, min: Self, max: Self) -> Self {
        self.max(min).min(max)
    }
    #[inline(always)]
    fn clamp01(self) -> Self {
        self.max(Self::ZERO).min(Self::ONE)
    }
}

macro_rules! impl_float {
    ($T:ident) => {
        impl Float for $T {
            const ZERO: Self = 0.0;
            const ONE: Self = 1.0;
            const HALF: Self = 0.5;
            const E: Self = std::$T::consts::E;
            const PI: Self = std::$T::consts::PI;

            #[inline(always)]
            fn add(self, other: Self) -> Self {
                self + other
            }
            #[inline(always)]
            fn sub(self, other: Self) -> Self {
                self - other
            }
            #[inline(always)]
            fn mul(self, other: Self) -> Self {
                self * other
            }
            #[inline(always)]
            fn div(self, other: Self) -> Self {
                self / other
            }
            #[inline(always)]
            fn rem(self, other: Self) -> Self {
                ((self % other) + other) % other
            }
            #[inline(always)]
            fn neg(self) -> Self {
                -self
            }
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
    fn add(self, other: Self) -> Self {
        self + other
    }
    #[inline(always)]
    fn sub(self, other: Self) -> Self {
        self - other
    }
    #[inline(always)]
    fn mul(self, other: Self) -> Self {
        self * other
    }
    #[inline(always)]
    fn div(self, other: Self) -> Self {
        self / other
    }
    #[inline(always)]
    fn neg(self) -> Self {
        -self
    }

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
        apply_x8!(cbrt, self.to_array()).into()
    }
    #[inline(always)]
    fn hypot(self, other: Self) -> Self {
        apply_x8!(hypot, self.to_array(), other.to_array()).into()
    }
    #[inline(always)]
    fn sin(self) -> Self {
        self.sin()
    }
    #[inline(always)]
    fn cos(self) -> Self {
        self.cos()
    }
}

macro_rules! map {
    (1, $f:expr, $($a:expr),+) => {
        $f($($a),+)
    };
    (2, $f:expr, $($a:expr),+) => {
        [
            $f($($a[0]),+),
            $f($($a[1]),+),
        ]
    };
    (3, $f:expr, $($a:expr),+) => {
        [
            $f($($a[0]),+),
            $f($($a[1]),+),
            $f($($a[2]),+),
        ]
    };
    (4, $f:expr, $($a:expr),+) => {
        [
            $f($($a[0]),+),
            $f($($a[1]),+),
            $f($($a[2]),+),
            $f($($a[3]),+),
        ]
    };
}

macro_rules! impl_for_float_array {
    ( $N:tt, $($f:ident(self $(, $a:ident)*),)*) => {
        impl<T: Float> Float for [T; $N] {
            const ZERO: Self = [T::ZERO; $N];
            const ONE: Self = [T::ONE; $N];
            const HALF: Self = [T::HALF; $N];
            const E: Self = [T::E; $N];
            const PI: Self = [T::PI; $N];

            #[inline(always)]
            fn from_f64(f:f64) -> Self {
                [T::from_f64(f); $N]
            }

            $(
                #[inline(always)]
                fn $f(self $(, $a:Self)*) -> Self {
                    map!($N, T::$f, self $(, $a)*)
                }
            )*

        }
    };
}

macro_rules! impl_for_float_array_n {
    ($N:tt) => {
        impl_for_float_array!(
            $N,
            add(self, other),
            sub(self, other),
            mul(self, other),
            div(self, other),
            rem(self, other),
            neg(self),
            select(self, then, else_),
            floor(self),
            ceil(self),
            round(self),
            recip(self),
            abs(self),
            ln(self),
            min(self, other),
            max(self, other),
            pow(self, n),
            sqrt(self),
            cbrt(self),
            hypot(self, other),
            sin(self),
            cos(self),
            bias(self, b),
            fit(self, oldmin, oldmax, newmin, newmax),
            clamp(self, min, max),
        );
    };
}

impl_for_float_array_n!(2);
impl_for_float_array_n!(3);
impl_for_float_array_n!(4);

#[cfg(test)]
mod tests {
    use super::*;
}
