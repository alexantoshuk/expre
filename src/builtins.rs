use crate::compiler::Expression;
use crate::context::*;
use crate::evaler::*;
use crate::float::*;
use crate::op::*;
use crate::{compile_stdfn, map2, map3};

#[inline]
pub(crate) fn dispatch_const(name: &str) -> Option<OP> {
    match name {
        "PI" => Some(FOP(FOP::CONST(f64::PI))),
        "E" => Some(FOP(FOP::CONST(f64::E))),
        "EPS" => Some(FOP(FOP::CONST(f64::EPSILON))),
        _ => None,
    }
}

macro_rules! impl_std_fn {
    (
        $($fname:ident($($arg:ident),*),)*
    ) => {
        use paste::paste;
        macro_rules! _type {
            ($name:ident, $T: ty)=>{
                $T
            }
        }
        paste!{
            #[allow(non_camel_case_types)]
            #[derive(Clone, Debug)]
            pub enum STDFN {
                $([<$fname:upper>]($(_type!($arg, F)),*)),*
            }

            #[allow(non_camel_case_types)]
            #[derive(Clone, Debug)]
            pub enum STDFN2 {
                $([<$fname:upper>]($(_type!($arg, F2)),*)),*
            }

            #[allow(non_camel_case_types)]
            #[derive(Clone, Debug)]
            pub enum STDFN3 {
                $([<$fname:upper>]($(_type!($arg, F3)),*)),*
            }

            #[inline]
            pub(crate) fn dispatch_func(name: &str, string: Option<&str>, args: &[ARG]) -> Option<OP>{
                match (name, string, args) {
                    $((stringify!($fname), None, [$($arg),*]) => {Some(compile_stdfn!([<$fname:upper>], $fname, ($($arg),*)))})*
                    _ => None,
                }
            }

            impl<M, CTX> Eval<M,CTX> for STDFN
            where
                M: Module,
                CTX: Context,
            {
                type Output = CTX::T;
                #[inline]
                fn eval(&self, en: &Expression<M>, ctx: &CTX) -> Self::Output {
                    match self {
                        $(Self::[<$fname:upper>]($($arg),*) => {CTX::T::$fname($($arg.eval(en, ctx)),*)})*

                    }
                }
            }

            impl<M, CTX> Eval<M,CTX> for STDFN2
            where
                M: Module,
                CTX: Context,
            {
                type Output = [CTX::T;2];
                #[inline]
                fn eval(&self, en: &Expression<M>, ctx: &CTX) -> Self::Output {
                    match self {
                        $(Self::[<$fname:upper>]($($arg),*) => {map2!(CTX::T::$fname, $($arg.eval(en, ctx)),+)})*

                    }
                }
            }

            impl<M, CTX> Eval<M,CTX> for STDFN3
            where
                M: Module,
                CTX: Context,
            {
                type Output = [CTX::T;3];
                #[inline]
                fn eval(&self, en: &Expression<M>, ctx: &CTX) -> Self::Output {
                    match self {
                        $(Self::[<$fname:upper>]($($arg),*) => {map3!(CTX::T::$fname, $($arg.eval(en, ctx)),+)})*

                    }
                }
            }
        }
    };
}

impl_std_fn!(
    floor(x),
    ceil(x),
    round(x),
    recip(x),
    abs(x),
    ln(x),
    min(x, y),
    max(x, y),
    pow(x, n),
    sqrt(x),
    cbrt(x),
    hypot(x, y),
    sin(x),
    cos(x),
    deg(x),
    rad(x),
    bias(x, b),
    lerp(a, b, t),
    fit(x, oldmin, oldmax, newmin, newmax),
    fit01(x, newmin, newmax),
    clamp(x, min, max),
    clamp01(x),
);
