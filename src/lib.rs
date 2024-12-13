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
