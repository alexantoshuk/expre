use crate::evaler::{FEvaler, UEvaler};
use crate::float::Float;
use crate::ops::*;
use bytemuck::*;
use std::fmt::Debug;
use std::hash::Hash;

// pub trait Context: Sized + Clone + Debug {
//     type FFN: Eq + PartialEq + Hash + Debug; // + FEvaler;
//     type UFN: Eq + PartialEq + Hash + Debug; // + UEvaler;
//     type FOP: Float;

//     fn var(_name: &str) -> Option<OP<Self>> {
//         None
//     }

//     fn func(_name: &str, _sarg: Option<&str>, _args: &[ARG]) -> Option<OP<Self>> {
//         None
//     }

//     fn get_fvar(&self, offset: usize) -> Self::FOP {
//         unsafe { *((self as *const Self as *const Self::FOP).add(offset)) }
//     }

//     fn get_uvar(&self, offset: usize) -> [Self::FOP; 2] {
//         unsafe { *((self as *const Self as *const Self::FOP).add(offset) as *const [Self::FOP; 2]) }
//     }

//     fn get_vvar(&self, offset: usize) -> [Self::FOP; 3] {
//         unsafe { *((self as *const Self as *const Self::FOP).add(offset) as *const [Self::FOP; 3]) }
//     }
// }

// pub trait FN: Sized + Clone + Debug {
//     type Output: Float;

//     fn dispatch(_name: &str, _sargs: Option<&str>, _args: &[ARG]) -> Option<Self>;
//     fn func(&self) -> impl FnOnce() -> Self::Output;
// }

// pub trait FDispatcher: Eq + PartialEq + Hash + Clone + Debug {
//     fn dispatch(_name: &str, _args: &[ARG]) -> Option<FOP<Self>>;
// }
// pub trait UDispatcher: Eq + PartialEq + Hash + Clone + Debug {
//     fn dispatch(_name: &str, _args: &[ARG]) -> Option<UOP<Self>>;
// }

pub trait Module: Sized + Clone {
    type FFN: Eq + PartialEq + Hash + Clone + Debug;
    type UFN: Eq + PartialEq + Hash + Clone + Debug;

    fn dispatch_var(&self, _name: &str) -> Option<&ARG> {
        None
    }

    fn dispatch_func(&self, _name: &str, _args: &[ARG]) -> Option<OP<Self::FFN, Self::UFN>> {
        None
    }
}

impl Module for () {
    type FFN = ();
    type UFN = ();
}

#[inline]
pub fn get<T: Float>(data: &[T], offset: usize) -> &T {
    &data[offset]
}

#[inline]
pub fn get_n<T: Float, const N: usize>(data: &[T], offset: usize) -> &[T; N] {
    let slice = &data[offset..offset + N];
    unsafe { &*(slice.as_ptr() as *const [T; N]) }
}

pub trait Context<T: Float>: Sized + Clone + Debug {
    fn get_fvar(&self, offset: usize) -> T {
        unsafe { *((self as *const Self as *const T).add(offset)) }
    }

    fn get_uvar(&self, offset: usize) -> [T; 2] {
        unsafe { *((self as *const Self as *const T).add(offset) as *const [T; 2]) }
    }

    fn get_vvar(&self, offset: usize) -> [T; 3] {
        unsafe { *((self as *const Self as *const T).add(offset) as *const [T; 3]) }
    }
}

// #[derive(Clone, Debug)]
// struct ConstCtx;
// impl Context for ConstCtx {
//     type T = f64;
// }

// /// Implement Std context
// #[derive(Clone, Debug)]
// pub struct Std;

// #[derive(Hash, PartialEq, Eq, Debug)]
// pub enum FStdFunc {
//     SIN(F),
// }

// #[derive(Hash, PartialEq, Eq, Debug)]
// pub enum UStdFunc {
//     SIN(U),
// }

// impl Context for Std {
//     type FFN = FStdFunc;
//     type UFN = UStdFunc;
//     type FOP = f32;

//     /// Get the const or var associated with the given `name`
//     #[inline]
//     fn var(name: &str) -> Option<OP<Self>> {
//         match name {
//             "PI" => Some(FOP(FOP::CONST(f64::PI))),
//             "E" => Some(FOP(FOP::CONST(f64::E))),
//             "EPS" => Some(FOP(FOP::CONST(f64::EPSILON))),
//             _ => None,
//         }
//     }

//     /// Get the function associated with the given `name` and args
//     #[inline]
//     fn func(name: &str, sarg: Option<&str>, args: &[ARG]) -> Option<OP<Self>> {
//         match (name, sarg, args) {
//             ("sin", None, &[F(icv)]) => Some(FOP(FOP::FN(Self::FFN::SIN(icv)))),
//             ("sin", None, &[U(icv)]) => Some(UOP(UOP::FN(Self::UFN::SIN(icv)))),
//             _ => None,
//         }
//     }
// }

// // Example of implementation custom context with deriving constants and functions from Std
// #[derive(Clone, Debug)]
// pub struct Custom;

// impl Context for Custom {
//     type FFN = FStdFunc;
//     type UFN = UStdFunc;

//     /// Get the const or var associated with the given `name`
//     #[inline]
//     fn var(name: &str) -> Option<OP<Self>> {
//         match name {
//             "id" => Some(FOP(FOP::VAR(123))),
//             _ => Std::var(name),
//         }
//     }

//     /// Get the function associated with the given `name` and args
//     #[inline]
//     fn func(name: &str, sarg: &Option<String>, args: &[ARG]) -> Option<OP<Self>> {
//         Std::func(name, sarg, args)
//     }
// }
