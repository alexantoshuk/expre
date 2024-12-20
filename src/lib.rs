//#![warn(missing_docs)]
pub mod compiler;
pub mod context;
pub mod error;
pub mod evaler;
pub mod float;
pub mod ops;
pub mod parser;
pub mod tokens;
pub use self::compiler::*;
pub use self::context::*;
pub use self::error::Error;
pub use self::evaler::*;

pub use self::parser::{parse, Ast, ParseExpr};
use std::fmt;

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

#[macro_export]
macro_rules! map2 {
    ($f:expr, $($a:expr),+$(,)?) => {
        [
            crate::_map!($f, 0, $($a),+),
            crate::_map!($f, 1, $($a),+),
        ]
    };
}

#[macro_export]
macro_rules! map3 {
    ($f:expr, $($a:expr),+$(,)?) => {
        [
            crate::_map!($f, 0, $($a),+),
            crate::_map!($f, 1, $($a),+),
            crate::_map!($f, 2, $($a),+),
        ]
    };
}

#[macro_export]
macro_rules! map4 {
    ($f:expr, $($a:expr),+$(,)?) => {
        [
            crate::_map!($f, 0, $($a),+),
            crate::_map!($f, 1, $($a),+),
            crate::_map!($f, 2, $($a),+),
            crate::_map!($f, 3, $($a),+),
        ]
    };
}

// #[macro_export]
// macro_rules! op_func1 {
//     ($f:ident, $args: expr) => {
//         match $args {
//             &[FICV(FICV::CONST(c))] => Some(F(F::CONST(f32::$f(c)))),
//             &[FICV(x)] => Some(F(F::FUNC(F_F(T::$f, x)))),
//             &[UICV(UICV::CONST(c))] => Some(U(U::CONST(crate::map2!(f32::$f, c)))),
//             &[UICV(x)] => unimplemented!(),
//             // &[UICV(x)] => Some(UOP(UFUNC(U_U(T::$f, x)))),
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
//                 Some(UOP(uop))
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

//             U {
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
//             $pub enum [<$module_name U>] {
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
//                 type FFN = [<$module_name F>];
//                 type UFN = [<$module_name U>];

//                 #[inline]
//                 fn dispatch_var(&self, name: &str) -> Option<&ICV> {
//                     self.vars.get(name)
//                 }

//                 #[inline]
//                 fn dispatch_func(&self, name: &str, args: &[ICV]) -> Option<OP<Self::FFN, Self::UFN>>{
//                     match (name, args) {
//                         $(($fstr_, &[$($fargty_($fargname_)),*]) => {Some(FO(FO::FN(Self::FFN::$fname_($($farg_.into()),*))))})*
//                         $(("$fname", &[$($fargty(F::CONST($fargname))),*]) => {Some(FO(FO::CONST(f64::$fname($($fargname),*))))})*
//                         $(("$fname", &[$($fargty($fargname)),*]) => {Some(FO(FO::FN(Self::FFN::$fname($($farg.into()),*))))})*

//                         $(($ustr_, &[$($uargty_($uargname_)),*]) => {Some(UO(UO::FN(Self::UFN::$uname_($($uarg_.into()),*))))})*
//                         $(($ustr, &[$($uargname @ (F(F::CONST(_)) | U(U::CONST(_)))),*]) => {Some(UO(UO::CONST(<[f64;2]>::$uname($($uargname.into()),*))))})*
//                         $(($ustr, &[$($uargty($uargname)),*]) => {Some(UO(UO::FN(Self::UFN::$uname($($uarg.into()),*))))})*
//                         _ => None,
//                     }
//                 }
//             }

//             impl<T, CTX> FEvaler<$module_name, T, CTX> for [<$module_name F>]
//             where
//                 T: Float,
//                 CTX: Context<T>,
//             {
//                 #[inline]
//                 fn eval(&self, cexpr: &CExpr<$module_name>, ctx: &CTX) -> T {
//                     match self {
//                         $(Self::$fname($($fargname),*) => {T::$fname($($fargname.eval(cexpr, ctx)),*)})*
//                         _=> T::ZERO
//                     }
//                 }
//             }

//             impl<T, CTX> UEvaler<$module_name, T, CTX> for [<$module_name U>]
//             where
//                 T: Float,
//                 CTX: Context<T>,
//             {
//                 #[inline]
//                 fn eval(&self, cexpr: &CExpr<$module_name>, ctx: &CTX) -> [T;2] {
//                     match self {
//                         $(Self::$uname($($uargname),*) => {<[T;2]>::$uname($($uargname.eval(cexpr, ctx)),*)})*
//                         _=> [T::ZERO;2]
//                     }
//                 }
//             }
//         }
//     };
// }

#[macro_export]
macro_rules! module {
    ($pub:vis $module_name:ident<$T:ty> {
        $(F::$fname:ident($($fargname:ident : $fargty:ty),*);)*
        $(@F::$fname_:ident($($fargname_:ident : $fargty_:ty),*) => $fname2_:ident($($fargname2_:expr),*);)*
        $(U::$uname:ident($($uargname:ident : $uargty:ty),*);)*
        $(@U::$uname_:ident($($uargname_:ident : $uargty_:ty),*) => $uname2_:ident($($uargname2_:expr),*);)*

    }) => {
        use paste::paste;
        paste!{
            #[derive(Eq, PartialEq, Hash, Clone, Debug)]
            $pub enum [<$module_name F>] {
                $($fname($($fargty),*)),*
            }

            #[derive(Eq, PartialEq, Hash, Clone, Debug)]
            $pub enum [<$module_name U>] {
                $($uname($($uargty),*)),*
            }

            #[derive(Debug, Clone)]
            $pub struct $module_name {
                pub vars: IndexMap<String,ICV>,
            }

            impl $module_name {
                pub fn new(vars:IndexMap<String,ICV>)-> Self {
                    Self {vars}
                }
            }

            impl Module for $module_name {
                type FFN = [<$module_name F>];
                type UFN = [<$module_name U>];

                #[inline]
                fn dispatch_var(&self, name: &str) -> Option<&ICV> {
                    self.vars.get(name)
                }

                #[inline]
                fn dispatch_func(&self, name: &str, args: &[ICV]) -> Option<OP<Self::FFN, Self::UFN>>{
                    match (name, args) {
                        $((stringify!($fname_), &[$($fargty_($fargname_)),*]) => {Some(FO(FO::FN(Self::FFN::$fname2_($($fargname2_.into()),*))))})*
                        $((stringify!($fname), &[$(ref $fargname @ (F(F::CONST(_)) | $fargty($fargty::CONST(_)))),*]) => {Some(FO(FO::CONST(f64::$fname($($fargname.clone().try_into().unwrap()),*))))})*
                        $((stringify!($fname), &[$($fargty($fargname)),*]) => {Some(FO(FO::FN(Self::FFN::$fname($($fargname.into()),*))))})*

                        $((stringify!($uname_), &[$($uargty_($uargname_)),*]) => {Some(FO(FO::FN(Self::FFN::$uname2_($($uargname2_.into()),*))))})*
                        $((stringify!($uname), &[$(ref $uargname @ (F(F::CONST(_)) | $uargty($uargty::CONST(_)))),*]) => {Some(UO(UO::CONST(<[f64;2]>::$uname($($uargname.clone().try_into().unwrap()),*))))})*
                        $((stringify!($uname), &[$($uargty($uargname)),*]) => {Some(UO(UO::FN(Self::UFN::$uname($($uargname.into()),*))))})*

                        _ => None,
                    }
                }
            }

            impl<CTX> FEvaler<$module_name, $T, CTX> for [<$module_name F>]
            where
                CTX: Context<$T>,
            {
                #[inline]
                fn eval(&self, cexpr: &CExpr<$module_name>, ctx: &CTX) -> $T {
                    match self {
                        $(Self::$fname($($fargname),*) => {$T::$fname($($fargname.eval(cexpr, ctx)),*)})*
                        _=> unreachable!(),
                    }
                }
            }

            impl<CTX> UEvaler<$module_name, $T, CTX> for [<$module_name U>]
            where
                CTX: Context<$T>,
            {
                #[inline]
                fn eval(&self, cexpr: &CExpr<$module_name>, ctx: &CTX) -> [$T;2] {
                    match self {
                        $(Self::$uname($($uargname),*) => {<[$T;2]>::$uname($($uargname.eval(cexpr, ctx)),*)})*
                        _=> unreachable!(),
                    }
                }
            }
        }
    };
}
