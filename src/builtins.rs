use crate::compiler::Expression;
use crate::context::*;
use crate::evaler::*;
use crate::float::*;
use crate::op::*;
use crate::{compile_stdfn, map2, map3};
use indexmap::IndexMap;

#[derive(Clone, Debug)]
pub struct Builtins {
    pub vars: IndexMap<String, ARG>,
}

impl Module for Builtins {
    #[inline]
    fn dispatch_ident(&self, name: &str) -> Option<OP> {
        match self.vars.get(name)? {
            F(F::CONST(c)) => Some(FOP(FOP::CONST(*c))),
            F(F::VAR(i)) => Some(FOP(FOP::VAR(*i))),

            F2(F2::CONST(c)) => Some(FOP2(FOP2::CONST(*c))),
            F2(F2::VAR(i)) => Some(FOP2(FOP2::VAR(*i))),

            F3(F3::CONST(c)) => Some(FOP3(FOP3::CONST(*c))),
            F3(F3::VAR(i)) => Some(FOP3(FOP3::VAR(*i))),

            B(B::CONST(c)) => Some(BOP(BOP::CONST(*c))),
            B(B::VAR(i)) => Some(FOP(FOP::VAR(*i))),

            _ => None,
        }
    }
}

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
            #[derive(PartialEq, Eq, Hash, Clone, Debug)]
            pub enum STDFN {
                $([<$fname:upper>]($(_type!($arg, F)),*)),*
            }

            #[allow(non_camel_case_types)]
            #[derive(Eq, PartialEq, Hash, Clone, Debug)]
            pub enum STDFN2 {
                $([<$fname:upper>]($(_type!($arg, F2)),*)),*
            }

            #[allow(non_camel_case_types)]
            #[derive(Eq, PartialEq, Hash, Clone, Debug)]
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
