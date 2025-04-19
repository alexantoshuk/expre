use crate::compiler::Expression;
use crate::context::*;
use crate::error::Error;
use crate::evaler::*;
use crate::float::*;
use crate::op::*;
use crate::{map2, map3};
use paste::paste;

macro_rules! compile_fn {

    (:: $ename:ident ($($a:ident ),+ ), $fname:expr) => {
        match crate::max!($($a.optype()),+) {
            Type::F | Type::B => {
                compile_fn!(F:: $ename ($($a : F),+ ), $fname)
                // match ($($a.try_into()?),+) {
                //     ($(F::CONST($a)),+) => Fop(Fop::CONST($fname($($a),+))),
                //     ($($a),+) => Fop(Fop::FN(Ffn::$ename($($a),+))),
                // }
            }
            Type::F2 => {
                // compile_fn!(F:: $ename ($($a : F),+ ), $fname)
                match ($($a.try_into()?),+) {
                    ($(F2::CONST($a)),+) => F2op(F2op::CONST(map2!($fname, $($a),+))),
                    ($($a),+) => F2op(F2op::FN(F2fn::$ename($($a),+))),
                }
            }
            Type::F3=> {
                match ($($a.try_into()?),+) {
                    ($(F3::CONST($a)),+) => F3op(F3op::CONST(map3!($fname, $($a),+))),
                    ($($a),+) => F3op(F3op::FN(F3fn::$ename($($a),+))),
                }
            }
        }
    };
    ($T:ident :: $ename:ident ($($a:ident : $atype:ident),+ ), $fname:expr) => {

        paste! {
            match ($($a.try_into()?),+) {
                ($($atype::CONST($a)),+) => [<$T op>]([<$T op>]::CONST($fname($($a),+))),
                ($($a),+) => [<$T op>]([<$T op>]::FN([<$T fn>]::$ename($($a),+))),
            }
        }
    };
}

macro_rules! module {
    (
        Functions {
            $(:: $ename:ident ($($a:ident),+ ) => $fname:expr,)*
            $(Fop :: $f_ename:ident ($($f_a:ident : $f_atype:ident $(= $f_val:expr)?),+ ) => $f_fname:expr,)*
            $(F2op :: $f2_ename:ident ($($f2_a:ident : $f2_atype:ident $(= $f2_val:expr)?),+ ) => $f2_fname:expr,)*
            $(F3op :: $f3_ename:ident ($($f3_a:ident : $f3_atype:ident $(= $f3_val:expr)?),+ ) => $f3_fname:expr,)*
        }
        Overloads {
            // $(Fop :: $f_ename:ident ($($f_a:ident : $f_atype:ident $(= $f_val:expr)?),+ ) => $f_fname:expr,)*
        }
        Constants {

        }

    ) => {
        macro_rules! _type {
            ($name: ident, $T: ty)=>{
                $T
            }
        }
        macro_rules! _arg {
            ($var:tt) => {
                $var
            };
            ($var:tt $val:tt) => {
            };
        }

        paste! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub enum Ffn {
                $([<$ename:upper>]($(_type!($a, F)),*),)*
                $([<$f_ename:upper>]($(_type!($f_a, $f_atype)),*),)*
            }
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub enum F2fn {
                $([<$ename:upper>]($(_type!($a, F2)),*)),*
                $([<$f2_ename:upper>]($(_type!($f2_a, $f2_atype)),*),)*
            }
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub enum F3fn {
                $([<$ename:upper>]($(_type!($a, F3)),*)),*
                $([<$f3_ename:upper>]($(_type!($f3_a, $f3_atype)),*),)*
            }

            #[inline]
            pub fn dispatch_func(name: &str, str_arg: Option<&str>, args: &[ICV]) -> Result<OP,Error>{

                match (name, str_arg, args) {
                    $((stringify!($ename), None, [$($a),*]) => { Ok(compile_fn!(:: [<$ename:upper>] ($($a),*), $fname)) })*
                    $((stringify!($f_ename), None, [$($f_a),*]) => { Ok(compile_fn!(F :: [<$f_ename:upper>] ($($f_a: $f_atype),*), $f_fname)) })*
                    $((stringify!($f2_ename), None, [$($f2_a),*]) => { Ok(compile_fn!(F2 :: [<$f2_ename:upper>] ($($f2_a: $f2_atype),*), $f2_fname)) })*
                    $((stringify!($f3_ename), None, [$($f3_a),*]) => { Ok(compile_fn!(F3 :: [<$f3_ename:upper>] ($($f3_a: $f3_atype),*), $f3_fname)) })*

                    _ => Err(Error::Undefined("".into())),
                }
            }
        }
    };
}

module!(
    Functions {
        ::sin(x) => Float::sin,
        Fop::cos(x:F) => Float::cos,
        // Fop::rand(seed:F, min:F=0, max:F=1) => Float::rand,
        // Fop::COS(x:F) => Fop::COS(x:F, y: F::VAR("uv"))
    }
    Overloads {
        // Fop::rand(seed:F) => Fop::rand(seed, F::CONST(0), F::CONST(1)),
    }
    Constants {

    }

);

#[inline]
pub(crate) fn dispatch_const(name: &str) -> Option<OP> {
    match name {
        "PI" => Some(Fop(Fop::CONST(f64::PI))),
        "E" => Some(Fop(Fop::CONST(f64::E))),
        "EPS" => Some(Fop(Fop::CONST(f64::EPSILON))),
        _ => None,
    }
}

// macro_rules! impl_std_fn {
//     (
//         $($fname:ident($($arg:ident),*),)*
//     ) => {
//         use paste::paste;
//         macro_rules! _type {
//             ($name:ident, $T: ty)=>{
//                 $T
//             }
//         }
//         paste!{
//             #[allow(non_camel_case_types)]
//             #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
//             pub enum FN {
//                 // MINCOMP2(F2),
//                 // MAXCOMP2(F2),
//                 // MINCOMP3(F3),
//                 // MAXCOMP3(F3),
//                 $([<$fname:upper>]($(_type!($arg, F)),*)),*
//             }

//             #[allow(non_camel_case_types)]
//             #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
//             pub enum FN2 {
//                 $([<$fname:upper>]($(_type!($arg, F2)),*)),*
//             }

//             #[allow(non_camel_case_types)]
//             #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
//             pub enum FN3 {
//                 $([<$fname:upper>]($(_type!($arg, F3)),*)),*
//             }

//             #[inline]
//             pub(crate) fn dispatch_func(name: &str, string: Option<&str>, args: &[ICV]) -> Option<OP>{
//                 match (name, string, args) {
//                     $((stringify!($fname), None, [$($arg),*]) => {Some(compile_stdfn!([<$fname:upper>], $fname, ($($arg),*)))})*
//                     // ("mincomp", None, [F2(_)]) => {Some(Fop!(MINCOMP2, mincomp, (x)))}
//                     _ => None,
//                 }
//             }

//             impl<M, CTX> Eval<M,CTX> for FN
//             where
//                 M: Module,
//                 CTX: Context,
//             {
//                 type Output = CTX::T;
//                 #[inline]
//                 fn eval(&self, en: &Expression<M>, ctx: &CTX) -> Self::Output {
//                     match self {
//                         $(Self::[<$fname:upper>]($($arg),*) => {CTX::T::$fname($($arg.eval(en, ctx)),*)})*
//                     }
//                 }
//             }

//             impl<M, CTX> Eval<M,CTX> for FN2
//             where
//                 M: Module,
//                 CTX: Context,
//             {
//                 type Output = [CTX::T;2];
//                 #[inline]
//                 fn eval(&self, en: &Expression<M>, ctx: &CTX) -> Self::Output {
//                     match self {
//                         $(Self::[<$fname:upper>]($($arg),*) => {map2!(CTX::T::$fname, $($arg.eval(en, ctx)),+)})*
//                     }
//                 }
//             }

//             impl<M, CTX> Eval<M,CTX> for FN3
//             where
//                 M: Module,
//                 CTX: Context,
//             {
//                 type Output = [CTX::T;3];
//                 #[inline]
//                 fn eval(&self, en: &Expression<M>, ctx: &CTX) -> Self::Output {
//                     match self {
//                         $(Self::[<$fname:upper>]($($arg),*) => {map3!(CTX::T::$fname, $($arg.eval(en, ctx)),+)})*
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
//     deg(x),
//     rad(x),
//     bias(x, b),
//     lerp(a, b, t),
//     fit(x, oldmin, oldmax, newmin, newmax),
//     fit01(x, newmin, newmax),
//     clamp(x, min, max),
//     clamp01(x),
// );
