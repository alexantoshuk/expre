//#![warn(missing_docs)]
pub mod builtins;
pub mod compiler;
pub mod context;
mod ctx;
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
    args: &'a [op::ICV],
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
pub fn signature<'a>(name: &'a str, args: &'a [op::ICV]) -> Signature<'a> {
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

macro_rules! map {
    ($f:expr, $($a:expr),+$(,)?) => {
        $f($($a),+)
    };
}
pub(crate) use map;

macro_rules! map1 {
    ($f:expr, $($a:expr),+) => {
        [
            $f($($a[0]),+),
        ]
    };
}
pub(crate) use map1;

macro_rules! map2 {
    ($f:expr, $($a:expr),+) => {
        [
            $f($($a[0]),+),
            $f($($a[1]),+),
        ]
    };
}
pub(crate) use map2;

macro_rules! map3 {
    ($f:expr, $($a:expr),+) => {
        [
            $f($($a[0]),+),
            $f($($a[1]),+),
            $f($($a[2]),+),
        ]
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
        ]
    };
}
pub(crate) use map4;

macro_rules! map8 {
    ($f:expr, $($a:expr),+) => {
        [
            $f($($a[0]),+),
            $f($($a[1]),+),
            $f($($a[2]),+),
            $f($($a[3]),+),
            $f($($a[4]),+),
            $f($($a[5]),+),
            $f($($a[6]),+),
            $f($($a[7]),+),
        ]
    };
}
pub(crate) use map8;

macro_rules! map_n {
    (1, $f:expr, $($a:expr),+) => {
        crate::map1!($f, $($a),+)
    };
    (2, $f:expr, $($a:expr),+) => {
        crate::map2!($f, $($a),+)
    };
    (3, $f:expr, $($a:expr),+) => {
        crate::map3!($f, $($a),+)
    };
    (4, $f:expr, $($a:expr),+) => {
        crate::map4!($f, $($a),+)
    };
    (8, $f:expr, $($a:expr),+) => {
        crate::map8!($f, $($a),+)
    };
}
pub(crate) use map_n;

macro_rules! and {
    // Base case: when there's only one argument
    ($x:expr) => {
        $x
    };
    // Recursive case: compare the first argument with the max of the rest
    ($x:expr, $($rest:expr),+) => {
        $x.and(crate::and!($($rest),+))
    };
}
pub(crate) use and;

macro_rules! min {
    // Base case: when there's only one argument
    ($x:expr) => {
        $x
    };
    // Recursive case: compare the first argument with the max of the rest
    ($x:expr, $($rest:expr),+) => {
        $x.min(crate::min!($($rest),+))
    };
}
pub(crate) use min;

macro_rules! max {
    // Base case: when there's only one argument
    ($x:expr) => {
        $x
    };
    // Recursive case: compare the first argument with the max of the rest
    ($x:expr, $($rest:expr),+) => {
        $x.max(crate::max!($($rest),+))
    };
}
pub(crate) use max;
// macro_rules! max {
//     // Base case: when there's only one argument
//     ($x:expr) => {
//         &$x
//     };
//     // Recursive case: compare the first argument with the max of the rest
//     ($x:expr, $($rest:expr),+) => {
//         std::cmp::max(&$x, crate::max!($($rest),+))
//     };
// }
// pub(crate) use max;
// compile_fop(ADD(x:F2,y:F2))

// macro_rules! arg2op {
//     (F) => {
//         Fop
//     };
//     (F2) => {
//         F2op
//     };
//     (F3) => {
//         F3op
//     };
//     (B) => {
//         Bop
//     };
// }

// macro_rules! compile_op {
//     ($op:ident, $ename:ident ($($a:ident : $atype:ident),+ ), $fname:expr) => {
//         match ($($a),+) {
//             ($($atype::CONST($a)),+) => $op($op::CONST($fname($($a),+))),
//             ($($a),+) => $op($op::$ename($($a),+)),
//         }
//     };
// }

// pub(crate) use compile_ty_op;

macro_rules! compile_op {
    (:: $ename:ident ($($a:ident ),+ ), $fname:expr) => {
        match crate::max!($($a.optype()),+) {
            Type::F | Type::B => {
                match ($($a.try_into()?),+) {
                    ($(F::CONST($a)),+) => Fop(Fop::CONST($fname($($a),+))),
                    ($($a),+) => Fop(Fop::$ename($($a),+)),
                }
            }
            Type::F2 => {
                match ($($a.try_into()?),+) {
                    ($(F2::CONST($a)),+) => F2op(F2op::CONST(map2!($fname, $($a),+))),
                    ($($a),+) => F2op(F2op::$ename($($a),+)),
                }
            }
            Type::F3=> {
                match ($($a.try_into()?),+) {
                    ($(F3::CONST($a)),+) => F3op(F3op::CONST(map3!($fname, $($a),+))),
                    ($($a),+) => F3op(F3op::$ename($($a),+)),
                }
            }
        }
    };
    ($op:ident :: $ename:ident ($($a:ident : $atype:ident),+ ), $fname:expr) => {
        match ($($a.try_into()?),+) {
            ($($atype::CONST($a)),+) => $op($op::CONST($fname($($a),+))),
            ($($a),+) => $op($op::$ename($($a),+)),
        }
    };
}

pub(crate) use compile_op;

// macro_rules! create_FN {
//     (
//         $(Fop@ :: $ename:ident ($($a:ident),+ ) {$fname:expr})*
//         $(Fop :: $f_ename:ident ($($f_a:ident : $f_atype:ident),+ ) {$f_fname:expr})*
//         $(F2op :: $f2_ename:ident ($($f2_a:ident : $f2_atype:ident),+ ) {$f2_fname:expr})*
//         $(F3op :: $f3_ename:ident ($($f3_a:ident : $f3_atype:ident),+ ) {$f3_fname:expr})*
//     ) => {
//         macro_rules! _type {
//             ($name: ident, $T: ty)=>{
//                 $T
//             }
//         }
//         pub enum FN {
//             $($ename($(_type!($a, F)),*),)*
//             $($f_ename($(_type!($f_a, $f_atype)),*),)*
//         }
//         pub enum FN2 {
//             $($ename($(_type!($a, F2)),*)),*
//             $($f2_ename($(_type!($f2_a, $f2_atype)),*),)*
//         }
//         pub enum FN3 {
//             $($ename($(_type!($a, F3)),*)),*
//             $($f3_ename($(_type!($f3_a, $f3_atype)),*),)*
//         }

//         #[inline]
//         pub fn dispatch_func(name: &str, str_arg: Option<&str>, args: &[ICV]) -> Result<OP,Error>{
//             paste!{
//                 match (name, str_arg, args) {
//                     $((stringify!([<$ename:lower>]), None, [$($a),*]) => { Ok(compile_fn!(Fop@ :: $ename ($($a),*), $fname)) })*
//                     $((stringify!([<$f_ename:lower>]), None, [$($f_a),*]) => { Ok(compile_fn!(Fop :: $f_ename ($($f_a: $f_atype),*), $f_fname)) })*
//                     $((stringify!([<$f2_ename:lower>]), None, [$($f2_a),*]) => { Ok(compile_fn!(F2op :: $f2_ename ($($f2_a: $f2_atype),*), $f2_fname)) })*
//                     $((stringify!([<$f3_ename:lower>]), None, [$($f3_a),*]) => { Ok(compile_fn!(F3op :: $f3_ename ($($f3_a: $f3_atype),*), $f3_fname)) })*

//                     _ => Err(Error::Unreachable),
//                 }
//             }
//         }

//     };
// }

macro_rules! compile_stdfn {
    ($ename:ident, $fname:ident, ($($a:ident),+ )) => {
        #[allow(unused_parens)]
        match crate::max!($($a.optype()),+) {
            Type::F | Type::B => {
                match ($($a.try_into().ok()?),+) {
                    ($(F::CONST($a)),+) => Fop(Fop::CONST(f64::$fname($($a),+))),
                    ($($a),+) => Fop(Fop::FN(Ffn::$ename($($a),+))),
                }
            }
            Type::F2 => {
                match ($($a.try_into().ok()?),+) {
                    ($(F2::CONST($a)),+) => F2op(F2op::CONST(map2!(f64::$fname, $($a),+))),
                    ($($a),+) => F2op(F2op::FN(F2fn::$ename($($a),+))),
                }
            }
            Type::F3=> {
                match ($($a.try_into().ok()?),+) {
                    ($(F3::CONST($a)),+) => F3op(F3op::CONST(map3!(f64::$fname, $($a),+))),
                    ($($a),+) => F3op(F3op::FN(F3fn::$ename($($a),+))),
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
//             // &[UICV(x)] => Some(F2op(UFUNC(U_U(T::$f, x)))),
//             _ => None,
//         }
//     };
// }

// #[macro_export]
// macro_rules! op_func2 {
//     ($f:ident, $args: expr) => {
//         match $args {
//             &[FICV(FICV::FCONST(c0)), FICV(FICV::FCONST(c1))] => Some(Fop(FCONST(f32::$f(c0, c1)))),
//             &[FICV(x0), FICV(x1)] => Some(Fop(FFUNC(F_FF(T::$f, x0, x1)))),
//             &[x0 @ (FICV(_) | UICV(_)), x1 @ (UICV(_) | FICV(_))] => {
//                 let x0 = x0.into();
//                 let x1 = x1.into();
//                 let uop = match (x0, x1) {
//                     (UICV::UCONST(base), UICV::UCONST(power)) => {
//                         UCONST(crate::map2!(f32::$f, base, power))
//                     }
//                     _ => unimplemented!(), //UFUNC(U_UU(T::$f, x0, x1)),
//                 };
//                 Some(F2op(uop))
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
//                 pub vars: IndexMap<String,ICV>,
//             }

//             impl $module_name {
//                 pub fn new(vars:IndexMap<String,ICV>)-> Self {
//                     Self {vars}
//                 }
//             }

//             impl Module for $module_name {
//                 type FN = [<$module_name F>];
//                 type FN2 = [<$module_name F2>];

//                 #[inline]
//                 fn dispatch_var(&self, name: &str) -> Option<&ICV> {
//                     self.vars.get(name)
//                 }

//                 #[inline]
//                 fn dispatch_fn(&self, name: &str, args: &[ICV]) -> Option<OP<Self::FN, Self::FN2>>{
//                     match (name, args) {
//                         $(($fstr_, &[$($fargty_($fargname_)),*]) => {Some(Fop(Fop::FN(Self::Ffn::$fname_($($farg_.into()),*))))})*
//                         $(("$fname", &[$($fargty(F::CONST($fargname))),*]) => {Some(Fop(Fop::CONST(f64::$fname($($fargname),*))))})*
//                         $(("$fname", &[$($fargty($fargname)),*]) => {Some(Fop(Fop::FN(Self::Ffn::$fname($($farg.into()),*))))})*

//                         $(($ustr_, &[$($uargty_($uargname_)),*]) => {Some(F2op(F2op::FN(Self::F2fn::$uname_($($uarg_.into()),*))))})*
//                         $(($ustr, &[$($uargname @ (F(F::CONST(_)) | F2(F2::CONST(_)))),*]) => {Some(F2op(F2op::CONST(<[f64;2]>::$uname($($uargname.into()),*))))})*
//                         $(($ustr, &[$($uargty($uargname)),*]) => {Some(F2op(F2op::FN(Self::F2fn::$uname($($uarg.into()),*))))})*
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
//                 pub vars: IndexMap<String,ICV>,
//             }

//             impl $module_name {
//                 pub fn new()-> Self {
//                     Self {vars: IndexMap::new()}
//                 }

//                 pub fn with_vars(vars:IndexMap<String,ICV>)-> Self {
//                     Self {vars}
//                 }
//             }

//             impl Module for $module_name {
//                 type FN = [<$module_name F>];
//                 type FN2 = [<$module_name F2>];

//                 #[inline]
//                 fn dispatch_var(&self, name: &str) -> Option<&ICV> {
//                     self.vars.get(name)
//                 }

//                 #[inline]
//                 fn dispatch_fn(&self, name: &str, args: &[ICV]) -> Option<OP<Self::FN, Self::FN2>>{
//                     match (name, args) {
//                         $((stringify!($fname_), &[$($fargty_($fargname_)),*]) => {Some(Fop(Fop::FN(Self::Ffn::$fname2_($($fargname2_),*))))})*
//                         $((stringify!($fname), &[$(ref $fargname @ (F(F::CONST(_)) | $fargty($fargty::CONST(_)))),*]) => {Some(Fop(Fop::CONST(f64::$fname($($fargname.clone().try_into().unwrap()),*))))})*
//                         $((stringify!($fname), &[$($fargty($fargname)),*]) => {Some(Fop(Fop::FN(Self::Ffn::$fname($($fargname),*))))})*

//                         $((stringify!($uname_), &[$($uargty_($uargname_)),*]) => {Some(Fop(Fop::FN(Self::Ffn::$uname2_($($uargname2_),*))))})*
//                         $((stringify!($uname), &[$(ref $uargname @ (F(F::CONST(_)) | $uargty($uargty::CONST(_)))),*]) => {Some(F2op(F2op::CONST(<[f64;2]>::$uname($($uargname.clone().try_into().unwrap()),*))))})*
//                         $((stringify!($uname), &[$($uargty($uargname)),*]) => {Some(F2op(F2op::FN(Self::F2fn::$uname($($uargname),*))))})*

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

//                 F::FIT01(x:F, newmin:F, newmax:F) {Float::fit01};
//                 F::CLAMP(x:F, min:F, max:F) {Float::clamp};
//                 F2::FLOOR(x:F2) {Float2::floor};
//                 F3::CEIL(x:F2) {Float3::ceil};
