use dyn_fmt;
use num_traits::{self, FloatConst};
use std::fmt::{Debug, Display};

pub trait Float: num_traits::Float + From<f32> + Display + FloatConst {}
impl Float for f32 {}
impl Float for f64 {}

/// Get the const associated with the given `name`
#[inline(always)]
pub(crate) fn constant<F: Float + FloatConst>(name: &str) -> Option<F> {
    match name {
        "PI" => Some(F::PI()),
        "E" => Some(F::E()),
        "EPS" => Some(F::epsilon()),
        "NAN" => Some(F::nan()),
        "INF" => Some(F::infinity()),
        "NEG_INF" => Some(F::neg_infinity()),
        _ => None,
    }
}

/// Get the math function associated with the given `name`
#[inline(always)]
pub(crate) fn func_1f<F: Float>(name: &str) -> Option<fn(F) -> F> {
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
        "clamp01" => Some(clamp01),
        _ => None,
    }
}

#[inline(always)]
pub(crate) fn func_2f<F: Float>(name: &str) -> Option<fn(F, F) -> F> {
    match name {
        "pow" => Some(F::powf),
        "log" => Some(F::log),
        "round" => Some(round_to),
        "hypot" => Some(F::hypot),
        "atan2" => Some(F::atan2),
        "bias" => Some(bias),
        _ => None,
    }
}

#[inline(always)]
pub(crate) fn func_3f<F: Float>(name: &str) -> Option<fn(F, F, F) -> F> {
    match name {
        "clamp" => Some(clamp),
        "lerp" => Some(lerp),
        "fit01" => Some(fit01),
        _ => None,
    }
}

#[inline(always)]
pub(crate) fn func_4f<F: Float>(name: &str) -> Option<fn(F, F, F, F) -> F> {
    match name {
        _ => None,
    }
}

#[inline(always)]
pub(crate) fn func_5f<F: Float>(name: &str) -> Option<fn(F, F, F, F, F) -> F> {
    match name {
        "fit" => Some(fit),
        _ => None,
    }
}

#[inline(always)]
pub(crate) fn func_1s_nf<F: Float>(name: &str) -> Option<fn(&str, &[F]) -> F> {
    match name {
        "print" => Some(|s, v: &[F]| {
            eprintln!("{}", dyn_fmt::Arguments::new(s, v));
            *v.last().unwrap_or(&F::nan())
        }),
        _ => None,
    }
}

#[inline(always)]
pub fn round_to<F: Float>(x: F, n: F) -> F {
    let n = F::powf(10_f32.into(), n);
    (x * n).round() / n
}

#[inline(always)]
pub fn bias<F: Float>(x: F, b: F) -> F {
    x.powf(b.ln() / F::ln(0.5_f32.into()))
}

///Fits a value from oldminval-oldmaxval to the newminval-newmaxval range.
#[inline(always)]
pub fn fit<F: Float>(x: F, oldmin: F, oldmax: F, newmin: F, newmax: F) -> F {
    newmin + (x - oldmin) * (newmax - newmin) / (oldmax - oldmin)
}

///Fits a value from minval-maxval to the 0-1 range.
#[inline(always)]
pub fn fit01<F: Float>(x: F, min: F, max: F) -> F {
    (x - min) / (max - min)
}

#[inline(always)]
pub fn lerp<F: Float>(a: F, b: F, t: F) -> F {
    a * (F::one() - t) + b * t
}

#[inline(always)]
pub fn clamp<F: Float>(x: F, min: F, max: F) -> F {
    x.min(max).max(min)
}

#[inline(always)]
pub fn clamp01<F: Float>(x: F) -> F {
    x.min(F::one()).max(F::zero())
}

/// Uses [`EPSILON`](https://doc.rust-lang.org/core/f64/constant.EPSILON.html) to determine equality of two `f64`s.
#[inline(always)]
pub fn float_eq<F: Float>(l: F, r: F) -> bool {
    (l - r).abs() <= F::epsilon() * 8_f32.into()
}

/// Uses [`EPSILON`](https://doc.rust-lang.org/core/f64/constant.EPSILON.html) to determine inequality of two `f64`s.
#[inline(always)]
pub fn float_ne<F: Float>(l: F, r: F) -> bool {
    (l - r).abs() > F::epsilon() * 8_f32.into()
}
