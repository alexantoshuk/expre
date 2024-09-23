use dyn_fmt::*;
use indexmap::IndexSet;
use num_traits::{self, FloatConst};
use std::fmt::{Debug, Display};
pub trait Float: num_traits::Float + From<f32> + Display + FloatConst {
    #[inline(always)]
    fn round_to(x: Self, n: Self) -> Self {
        let n = Self::powf(10_f32.into(), n);
        (x * n).round() / n
    }

    #[inline(always)]
    fn bias(x: Self, b: Self) -> Self {
        x.powf(b.ln() / Self::ln(0.5_f32.into()))
    }

    ///Fits a value from oldminval-oldmaxval to the newminval-newmaxval range.
    #[inline(always)]
    fn fit(x: Self, oldmin: Self, oldmax: Self, newmin: Self, newmax: Self) -> Self {
        newmin + (x - oldmin) * (newmax - newmin) / (oldmax - oldmin)
    }

    ///Fits a value from minval-maxval to the 0-1 range.
    #[inline(always)]
    fn fit01(x: Self, min: Self, max: Self) -> Self {
        (x - min) / (max - min)
    }

    #[inline(always)]
    fn linear(a: Self, b: Self, t: Self) -> Self {
        a * (Self::one() - t) + b * t
    }

    #[inline(always)]
    fn clamp(x: Self, min: Self, max: Self) -> Self {
        x.min(max).max(min)
    }

    #[inline(always)]
    fn clamp01(x: Self) -> Self {
        x.min(Self::one()).max(Self::zero())
    }

    /// Uses [`EPSILON`](https://doc.rust-lang.org/core/f64/constant.EPSILON.html) to determine equality of two `f64`s.
    #[inline(always)]
    fn float_eq(l: Self, r: Self) -> bool {
        (l - r).abs() <= Self::epsilon() * 8_f32.into()
    }

    /// Uses [`EPSILON`](https://doc.rust-lang.org/core/f64/constant.EPSILON.html) to determine inequality of two `f64`s.
    #[inline(always)]
    fn float_ne(l: Self, r: Self) -> bool {
        (l - r).abs() > Self::epsilon() * 8_f32.into()
    }

    #[inline(always)]
    fn print(fmt: &str, v: &[Self]) -> Self {
        fmt.format(v);
        *v.last().unwrap_or(&Self::nan())
    }
}
impl Float for f32 {}
impl Float for f64 {}

pub trait Module<F: Float> {
    fn constant(name: &str) -> Option<F> {
        None
    }

    fn func_f(&self, name: &str) -> Option<fn() -> F> {
        None
    }
    fn func_f_f(name: &str) -> Option<fn(F) -> F> {
        None
    }
    fn func_ff_f(name: &str) -> Option<fn(F, F) -> F> {
        None
    }
    fn func_fff_f(name: &str) -> Option<fn(F, F, F) -> F> {
        None
    }
    fn func_ffff_f(name: &str) -> Option<fn(F, F, F, F) -> F> {
        None
    }
    fn func_fffff_f(name: &str) -> Option<fn(F, F, F, F, F) -> F> {
        None
    }
    fn func_nf(name: &str) -> Option<fn(&[F]) -> F> {
        None
    }

    fn func_1s_nf(name: &str) -> Option<fn(&str, &[F]) -> F> {
        None
    }

    fn func_2s_nf(name: &str) -> Option<fn(&str, &str, &[F]) -> F> {
        None
    }

    fn func_ns_nf(name: &str) -> Option<fn(&[&str], &[F]) -> F> {
        None
    }
}

pub struct Vars {
    pub float: IndexSet<String>, //float
    pub vec2: IndexSet<String>,  //vec2
    pub vec3: IndexSet<String>,  //vec3
}

pub struct Builtins {}

impl<F: Float> Module<F> for Builtins {
    /// Get the const associated with the given `name`
    #[inline(always)]
    fn constant(name: &str) -> Option<F> {
        match name {
            "PI" => Some(F::PI()),
            "E" => Some(F::E()),
            "EPS" => Some(F::epsilon()),
            // "NAN" => Some(F::nan()),
            // "INF" => Some(F::infinity()),
            // "NEG_INF" => Some(F::neg_infinity()),
            _ => None,
        }
    }

    /// Get the math function associated with the given `name`
    #[inline(always)]
    fn func_f_f(name: &str) -> Option<fn(F) -> F> {
        match name {
            "sqrt" => Some(F::sqrt),
            "round" => Some(F::round),
            "floor" => Some(F::floor),
            "ceil" => Some(F::ceil),
            "abs" => Some(F::abs),
            "sin" => Some(F::sin),
            "cos" => Some(F::cos),
            "tan" => Some(F::tan),
            "exp" => Some(F::exp),
            "ln" => Some(F::ln),
            "log2" => Some(F::log2),
            "log10" => Some(F::log10),
            "trunc" => Some(F::trunc),
            "fract" => Some(F::fract),
            "cbrt" => Some(F::cbrt),
            "asin" => Some(F::asin),
            "acos" => Some(F::acos),
            "atan" => Some(F::atan),
            "sinh" => Some(F::sinh),
            "cosh" => Some(F::cosh),
            "tanh" => Some(F::tanh),
            "asinh" => Some(F::asinh),
            "acosh" => Some(F::acosh),
            "atanh" => Some(F::atanh),
            "clamp01" => Some(F::clamp01),
            _ => None,
        }
    }

    #[inline(always)]
    fn func_ff_f(name: &str) -> Option<fn(F, F) -> F> {
        match name {
            "pow" => Some(F::powf),
            "log" => Some(F::log),
            "round" => Some(F::round_to),
            "hypot" => Some(F::hypot),
            "atan2" => Some(F::atan2),
            "bias" => Some(F::bias),
            _ => None,
        }
    }

    #[inline(always)]
    fn func_fff_f(name: &str) -> Option<fn(F, F, F) -> F> {
        match name {
            "clamp" => Some(<F as crate::module::Float>::clamp),
            "linear" => Some(F::linear),
            "fit01" => Some(F::fit01),
            _ => None,
        }
    }

    #[inline(always)]
    fn func_ffff_f(name: &str) -> Option<fn(F, F, F, F) -> F> {
        match name {
            _ => None,
        }
    }

    #[inline(always)]
    fn func_fffff_f(name: &str) -> Option<fn(F, F, F, F, F) -> F> {
        match name {
            "fit" => Some(F::fit),
            _ => None,
        }
    }

    #[inline(always)]
    fn func_1s_nf(name: &str) -> Option<fn(&str, &[F]) -> F> {
        match name {
            "print" => Some(F::print),
            _ => None,
        }
    }
}

#[derive(Copy, Clone)]
struct Globals {
    a: f32,
    b: f32,
}
// pub struct UserModuleExample<'a> {
//     globals: &'a Globals,
// }
// impl Module<f32> for UserModuleExample<'_> {
//     /// Get the const associated with the given `name`
//     #[inline(always)]
//     fn constant(name: &str) -> Option<f32> {
//         match name {
//             "SUPERNUMBER" => Some(42_f32.into()),
//             _ => Builtins::constant(name),
//         }
//     }

//     fn func_f(&self, name: &str) -> Option<fn(&G,F) -> f32> {
//         match name {
//             "rand" => {
//                 let id = self.globals.a;
//                 Some(|globals| globals.id + 1.0f32)
//             }
//             // "round" => Some(F::round),
//             _ => None,
//         }
//     }
// }
