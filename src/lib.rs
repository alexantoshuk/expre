//#![warn(missing_docs)]
pub mod builtins;
pub mod compiler;
pub mod context;
pub mod error;
pub mod evaler;
pub mod float;
pub mod op;
pub mod parser;
pub mod tokens;
pub use self::compiler::*;
pub use self::context::*;
pub use self::error::Error;
pub use self::evaler::*;
// mod traits;
pub use self::parser::{parse, Ast, ParseExpr};
use std::fmt;

pub struct Signature<'a> {
    name: &'a str,
    args: &'a [op::ARG],
}

impl<'a> fmt::Display for Signature<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.name);
        let mut iter_args = self.args.iter();
        if let Some(arg) = iter_args.next() {
            write!(f, "{}", arg.name());
            for arg in iter_args {
                write!(f, ",{}", arg.name())?;
            }
        }
        write!(f, ")")
    }
}
pub fn signature<'a>(name: &'a str, args: &'a [op::ARG]) -> Signature<'a> {
    Signature { name, args }
}

fn debug_indexed_list<T>(f: &mut fmt::Formatter, lst: &[T]) -> Result<(), fmt::Error>
where
    T: fmt::Debug,
{
    let sep = '\n';
    let ident = "  ";
    for (i, x) in lst.iter().enumerate() {
        write!(f, "{sep}{ident}{i}:\t{x:?}")?;
    }
    Ok(())
}

fn display_indexed_list<T>(f: &mut fmt::Formatter, lst: &[T]) -> Result<(), fmt::Error>
where
    T: fmt::Display,
{
    let sep = '\n';
    let ident = "  ";
    for (i, x) in lst.iter().enumerate() {
        write!(f, "{sep}{ident}{i}:\t{x}")?;
    }
    Ok(())
}

#[macro_export]
macro_rules! _map {
    ($f:expr, $i: literal, $($a:expr),+$(,)?) => {
        $f($($a[$i]),+)
    };
}

#[macro_export]
macro_rules! map {
    ($f:expr, $($a:expr),+$(,)?) => {
        $f($($a),+)
    };
}

macro_rules! map2 {
    ($f:expr, $($a:expr),+) => {
        [
            $f($($a[0]),+),
            $f($($a[1]),+),
        ].into()
    };
}
pub(crate) use map2;

macro_rules! map3 {
    ($f:expr, $($a:expr),+) => {
        [
            $f($($a[0]),+),
            $f($($a[1]),+),
            $f($($a[2]),+),
        ].into()
    };
}
pub(crate) use map3;

macro_rules! map4 {
    ($f:expr, $($a:expr),+) => {
        [
            $f($($a[0]),+),
            $f($($a[1]),+),
            $f($($a[2]),+),
            $f($($a[3]),+),
        ].into()
    };
}
pub(crate) use map4;

macro_rules! max {
    // Base case: when there's only one argument
    ($x:expr) => {
        &$x
    };
    // Recursive case: compare the first argument with the max of the rest
    ($x:expr, $($rest:expr),+) => {
        std::cmp::max(&$x, crate::max!($($rest),+))
    };
}
pub(crate) use max;

macro_rules! compile_op {
    ($ename:ident, $fname:ident, ($($a:ident),+ )) => {
        #[allow(unused_parens)]
        match crate::max!($($a.optype()),+) {
            Type::F | Type::B => {
                match ($($a.try_into().unwrap()),+) {
                    ($(F::CONST($a)),+) => FOP(FOP::CONST(f64::$fname($($a),+))),
                    ($($a),+) => FOP(FOP::$ename($($a),+)),
                }
            }
            Type::F2 => {
                match ($($a.try_into().unwrap()),+) {
                    ($(F2::CONST($a)),+) => FOP2(FOP2::CONST(map2!(f64::$fname, $($a),+))),
                    ($($a),+) => FOP2(FOP2::$ename($($a),+)),
                }
            }
            Type::F3=> {
                match ($($a.try_into()?),+) {
                    ($(F3::CONST($a)),+) => FOP3(FOP3::CONST(map3!(f64::$fname, $($a),+))),
                    ($($a),+) => FOP3(FOP3::$ename($($a),+)),
                }
            }
        }
    };
}

pub(crate) use compile_op;

macro_rules! compile_stdfn {
    ($ename:ident, $fname:ident, ($($a:ident),+ )) => {
        #[allow(unused_parens)]
        match crate::max!($($a.optype()),+) {
            Type::F | Type::B => {
                match ($($a.try_into().ok()?),+) {
                    ($(F::CONST($a)),+) => FOP(FOP::CONST(f64::$fname($($a),+))),
                    ($($a),+) => FOP(FOP::STDFN(STDFN::$ename($($a),+))),
                }
            }
            Type::F2 => {
                match ($($a.try_into().ok()?),+) {
                    ($(F2::CONST($a)),+) => FOP2(FOP2::CONST(map2!(f64::$fname, $($a),+))),
                    ($($a),+) => FOP2(FOP2::STDFN(STDFN2::$ename($($a),+))),
                }
            }
            Type::F3=> {
                match ($($a.try_into().ok()?),+) {
                    ($(F3::CONST($a)),+) => FOP3(FOP3::CONST(map3!(f64::$fname, $($a),+))),
                    ($($a),+) => FOP3(FOP3::STDFN(STDFN3::$ename($($a),+))),
                }
            }
        }
    };
}

pub(crate) use compile_stdfn;
// #[macro_export]
// macro_rules! op_func1 {
//     ($f:ident, $args: expr) => {
//         match $args {
//             &[FICV(FICV::CONST(c))] => Some(F(F::CONST(f32::$f(c)))),
//             &[FICV(x)] => Some(F(F::FUNC(F_F(T::$f, x)))),
//             &[UICV(UICV::CONST(c))] => Some(F2(F2::CONST(crate::map2!(f32::$f, c)))),
//             &[UICV(x)] => unimplemented!(),
//             // &[UICV(x)] => Some(FOP2(UFUNC(U_U(T::$f, x)))),
//             _ => None,
//         }
//     };
// }

// #[macro_export]
// macro_rules! op_func2 {
//     ($f:ident, $args: expr) => {
//         match $args {
//             &[FICV(FICV::FCONST(c0)), FICV(FICV::FCONST(c1))] => Some(FOP(FCONST(f32::$f(c0, c1)))),
//             &[FICV(x0), FICV(x1)] => Some(FOP(FFUNC(F_FF(T::$f, x0, x1)))),
//             &[x0 @ (FICV(_) | UICV(_)), x1 @ (UICV(_) | FICV(_))] => {
//                 let x0 = x0.into();
//                 let x1 = x1.into();
//                 let uop = match (x0, x1) {
//                     (UICV::UCONST(base), UICV::UCONST(power)) => {
//                         UCONST(crate::map2!(f32::$f, base, power))
//                     }
//                     _ => unimplemented!(), //UFUNC(U_UU(T::$f, x0, x1)),
//                 };
//                 Some(FOP2(uop))
//             }
//             _ => None,
//         }
//     };
// }

/*
let resolver = expre::parse()

*/

// #[macro_export]
// macro_rules! module {
//     ($pub:vis $module_name:ident {
//             F {
//                 $(($fstr: literal, $($fargname:ident : $fargty:ty),*) => $fname:ident($($farg:expr),*),)*
//                 $(_($fstr_: literal, $($fargname_:ident : $fargty_:ty),*) => $fname_:ident($($farg_:expr),*),)*
//             },

//             F2 {
//                 $(($ustr: literal, $($uargname:ident : $uargty:ty),*) => $uname:ident($($uarg:expr),*),)*
//                 $(_($ustr_: literal, $($uargname_:ident : $uargty_:ty),*) => $uname_:ident($($uarg_:expr),*),)*
//             },
//         }
//     ) => {
//         use paste::paste;
//         paste!{
//             #[derive(Eq, PartialEq, Hash, Clone, Debug)]
//             $pub enum [<$module_name F>] {
//                 $($fname($($fargty),*)),*
//             }

//             #[derive(Eq, PartialEq, Hash, Clone, Debug)]
//             $pub enum [<$module_name F2>] {
//                 $($uname($($uargty),*)),*
//             }

//             #[derive(Debug, Clone)]
//             $pub struct $module_name {
//                 pub vars: IndexMap<String,ARG>,
//             }

//             impl $module_name {
//                 pub fn new(vars:IndexMap<String,ARG>)-> Self {
//                     Self {vars}
//                 }
//             }

//             impl Module for $module_name {
//                 type FN = [<$module_name F>];
//                 type FN2 = [<$module_name F2>];

//                 #[inline]
//                 fn dispatch_var(&self, name: &str) -> Option<&ARG> {
//                     self.vars.get(name)
//                 }

//                 #[inline]
//                 fn dispatch_fn(&self, name: &str, args: &[ARG]) -> Option<OP<Self::FN, Self::FN2>>{
//                     match (name, args) {
//                         $(($fstr_, &[$($fargty_($fargname_)),*]) => {Some(FOP(FOP::FN(Self::FN::$fname_($($farg_.into()),*))))})*
//                         $(("$fname", &[$($fargty(F::CONST($fargname))),*]) => {Some(FOP(FOP::CONST(f64::$fname($($fargname),*))))})*
//                         $(("$fname", &[$($fargty($fargname)),*]) => {Some(FOP(FOP::FN(Self::FN::$fname($($farg.into()),*))))})*

//                         $(($ustr_, &[$($uargty_($uargname_)),*]) => {Some(FOP2(FOP2::FN(Self::FN2::$uname_($($uarg_.into()),*))))})*
//                         $(($ustr, &[$($uargname @ (F(F::CONST(_)) | F2(F2::CONST(_)))),*]) => {Some(FOP2(FOP2::CONST(<[f64;2]>::$uname($($uargname.into()),*))))})*
//                         $(($ustr, &[$($uargty($uargname)),*]) => {Some(FOP2(FOP2::FN(Self::FN2::$uname($($uarg.into()),*))))})*
//                         _ => None,
//                     }
//                 }
//             }

//             impl<T, CTX> EvalF<$module_name, T, CTX> for [<$module_name F>]
//             where
//                 T: Float,
//                 CTX: Context<T>,
//             {
//                 #[inline]
//                 fn eval(&self, en: &Expression<$module_name>, ctx: &CTX) -> T {
//                     match self {
//                         $(Self::$fname($($fargname),*) => {T::$fname($($fargname.eval(en, ctx)),*)})*
//                         _=> T::ZERO
//                     }
//                 }
//             }

//             impl<T, CTX> EvalF2<$module_name, T, CTX> for [<$module_name F2>]
//             where
//                 T: Float,
//                 CTX: Context<T>,
//             {
//                 #[inline]
//                 fn eval(&self, en: &Expression<$module_name>, ctx: &CTX) -> [T;2] {
//                     match self {
//                         $(Self::$uname($($uargname),*) => {<[T;2]>::$uname($($uargname.eval(en, ctx)),*)})*
//                         _=> [T::ZERO;2]
//                     }
//                 }
//             }
//         }
//     };
// }

// macro_rules! _module {
//     ($pub:vis $module_name:ident<$T:ty> {
//         $(F::$fname:ident($($fargname:ident : $fargty:ty),*);)*
//         $(@F::$fname_:ident($($fargname_:ident : $fargty_:ty),*) => $fname2_:ident($($fargname2_:expr),*);)*
//         $(F2::$uname:ident($($uargname:ident : $uargty:ty),*);)*
//         $(@F2::$uname_:ident($($uargname_:ident : $uargty_:ty),*) => $uname2_:ident($($uargname2_:expr),*);)*
//     }) => {
//         use paste::paste;

//         paste!{
//             #[derive(Eq, PartialEq, Hash, Clone, Debug)]
//             $pub enum [<$module_name F>] {
//                 $($fname($($fargty),*)),*
//             }

//             #[derive(Eq, PartialEq, Hash, Clone, Debug)]
//             $pub enum [<$module_name F2>] {
//                 $($uname($($uargty),*)),*
//             }

//             #[derive(Debug, Clone)]
//             $pub struct $module_name {
//                 pub vars: IndexMap<String,ARG>,
//             }

//             impl $module_name {
//                 pub fn new()-> Self {
//                     Self {vars: IndexMap::new()}
//                 }

//                 pub fn with_vars(vars:IndexMap<String,ARG>)-> Self {
//                     Self {vars}
//                 }
//             }

//             impl Module for $module_name {
//                 type FN = [<$module_name F>];
//                 type FN2 = [<$module_name F2>];

//                 #[inline]
//                 fn dispatch_var(&self, name: &str) -> Option<&ARG> {
//                     self.vars.get(name)
//                 }

//                 #[inline]
//                 fn dispatch_fn(&self, name: &str, args: &[ARG]) -> Option<OP<Self::FN, Self::FN2>>{
//                     match (name, args) {
//                         $((stringify!($fname_), &[$($fargty_($fargname_)),*]) => {Some(FOP(FOP::FN(Self::FN::$fname2_($($fargname2_),*))))})*
//                         $((stringify!($fname), &[$(ref $fargname @ (F(F::CONST(_)) | $fargty($fargty::CONST(_)))),*]) => {Some(FOP(FOP::CONST(f64::$fname($($fargname.clone().try_into().unwrap()),*))))})*
//                         $((stringify!($fname), &[$($fargty($fargname)),*]) => {Some(FOP(FOP::FN(Self::FN::$fname($($fargname),*))))})*

//                         $((stringify!($uname_), &[$($uargty_($uargname_)),*]) => {Some(FOP(FOP::FN(Self::FN::$uname2_($($uargname2_),*))))})*
//                         $((stringify!($uname), &[$(ref $uargname @ (F(F::CONST(_)) | $uargty($uargty::CONST(_)))),*]) => {Some(FOP2(FOP2::CONST(<[f64;2]>::$uname($($uargname.clone().try_into().unwrap()),*))))})*
//                         $((stringify!($uname), &[$($uargty($uargname)),*]) => {Some(FOP2(FOP2::FN(Self::FN2::$uname($($uargname),*))))})*

//                         _ => None,
//                     }
//                 }
//             }

//             impl EvalF<$module_name, $T> for [<$module_name F>]

//             {
//                 #[inline]
//                 fn eval(&self, en: &Expression<$module_name>, ctx: &[$T]) -> $T {
//                     match self {
//                         $(Self::$fname($($fargname),*) => {$T::$fname($($fargname.eval(en, ctx)),*)})*
//                         _=> unreachable!(),
//                     }
//                 }
//             }

//             impl EvalF2<$module_name, $T> for [<$module_name F2>]

//             {
//                 #[inline]
//                 fn eval(&self, en: &Expression<$module_name>, ctx: &[$T]) -> [$T;2] {
//                     match self {
//                         $(Self::$uname($($uargname),*) => {<[$T;2]>::$uname($($uargname.eval(en, ctx)),*)})*
//                         _=> unreachable!(),
//                     }
//                 }
//             }
//         }
//     };
// }

// pub(crate) use _module;

// #[macro_export]
// macro_rules! module {
//     ($pub:vis $module_name:ident<$T:ty> {
//         $(F::$fname:ident($($fargname:ident : $fargty:ty),*);)*
//         $(@F::$fname_:ident($($fargname_:ident : $fargty_:ty),*) => $fname2_:ident($($fargname2_:expr),*);)*
//         $(F2::$uname:ident($($uargname:ident : $uargty:ty),*);)*
//         $(@F2::$uname_:ident($($uargname_:ident : $uargty_:ty),*) => $uname2_:ident($($uargname2_:expr),*);)*
//     }) => {
//         crate::_module! {
//             $pub $module_name<$T> {
//                 F::floor(x:F);
//                 F::ceil(x:F);
//                 F::round(x:F);
//                 F::recip(x:F);
//                 F::abs(x:F);
//                 F::ln(x:F);
//                 F::min(x:F, y:F);
//                 F::max(x:F, y:F);
//                 F::pow(x:F, n:F);
//                 F::sqrt(x:F);
//                 F::cbrt(x:F);
//                 F::hypot(x:F, y:F);
//                 F::sin(x:F);
//                 F::cos(x:F);
//                 F::bias(x:F,b:F);
//                 F::fit(x:F, oldmin:F, oldmax:F, newmin:F, newmax:F);
//                 F::fit01(x:F, newmin:F, newmax:F);
//                 F::clamp(x:F, min:F, max:F);
//                 F::clamp01(x:F);
//                 $(F::$fname($($fargname : $fargty),*);)*
//                 $(@F::$fname_($($fargname_ : $fargty_),*) => $fname2_($($fargname2_),*);)*
//                 F2::floor(x:F2);
//                 F2::ceil(x:F2);
//                 F2::round(x:F2);
//                 F2::recip(x:F2);
//                 F2::abs(x:F2);
//                 F2::ln(x:F2);
//                 F2::min(x:F2, y:F2);
//                 F2::max(x:F2, y:F2);
//                 F2::pow(x:F2, n:F2);
//                 F2::sqrt(x:F2);
//                 F2::cbrt(x:F2);
//                 F2::hypot(x:F2, y:F2);
//                 F2::sin(x:F2);
//                 F2::cos(x:F2);
//                 F2::bias(x:F2,b:F2);
//                 F2::fit(x:F2, oldmin:F2, oldmax:F2, newmin:F2, newmax:F2);
//                 F2::fit01(x:F2, newmin:F2, newmax:F2);
//                 F2::clamp(x:F2, min:F2, max:F2);
//                 F2::clamp01(x:F2);
//                 $(F2::$uname($($uargname : $uargty),*);)*
//                 $(@F2::$uname_($($uargname_ : $uargty_),*) => $uname2_($($uargname2_),*);)*
//             }
//         }
//     };
// }
