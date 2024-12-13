use crate::evaler::{FEvaler, UEvaler};
use crate::float::Float;
use crate::ops::*;
use std::fmt::Debug;
use std::hash::Hash;
// pub trait Context: Sized + Clone + Debug {
//     type FFN: Eq + PartialEq + Hash + Debug; // + FEvaler;
//     type UFN: Eq + PartialEq + Hash + Debug; // + UEvaler;
//     type F: Float;

//     fn var(_name: &str) -> Option<OP<Self>> {
//         None
//     }

//     fn func(_name: &str, _sarg: Option<&str>, _args: &[ICV]) -> Option<OP<Self>> {
//         None
//     }

//     fn get_fvar(&self, offset: usize) -> Self::F {
//         unsafe { *((self as *const Self as *const Self::F).add(offset)) }
//     }

//     fn get_uvar(&self, offset: usize) -> [Self::F; 2] {
//         unsafe { *((self as *const Self as *const Self::F).add(offset) as *const [Self::F; 2]) }
//     }

//     fn get_vvar(&self, offset: usize) -> [Self::F; 3] {
//         unsafe { *((self as *const Self as *const Self::F).add(offset) as *const [Self::F; 3]) }
//     }
// }

pub trait Module: Sized + Clone + Debug {
    type FFN: Eq + PartialEq + Hash + Clone + Debug;
    type UFN: Eq + PartialEq + Hash + Clone + Debug;

    fn var(&self, _name: &str) -> Option<OP<Self::FFN, Self::UFN>> {
        None
    }

    fn func(
        &self,
        _name: &str,
        _sarg: Option<&str>,
        _args: &[ICV],
    ) -> Option<OP<Self::FFN, Self::UFN>> {
        None
    }
}

pub trait Context: Sized + Clone + Debug {
    type F: Float;

    fn get_fvar(&self, offset: usize) -> Self::F {
        unsafe { *((self as *const Self as *const Self::F).add(offset)) }
    }

    fn get_uvar(&self, offset: usize) -> [Self::F; 2] {
        unsafe { *((self as *const Self as *const Self::F).add(offset) as *const [Self::F; 2]) }
    }

    fn get_vvar(&self, offset: usize) -> [Self::F; 3] {
        unsafe { *((self as *const Self as *const Self::F).add(offset) as *const [Self::F; 3]) }
    }
}

/// Implement Std context
#[derive(Clone, Debug)]
pub struct Std;

#[derive(Hash, PartialEq, Eq, Debug)]
pub enum FStdFunc {
    SIN(FICV),
}

#[derive(Hash, PartialEq, Eq, Debug)]
pub enum UStdFunc {
    SIN(UICV),
}

// impl Context for Std {
//     type FFN = FStdFunc;
//     type UFN = UStdFunc;
//     type F = f32;

//     /// Get the const or var associated with the given `name`
//     #[inline]
//     fn var(name: &str) -> Option<OP<Self>> {
//         match name {
//             "PI" => Some(F(F::CONST(f64::PI))),
//             "E" => Some(F(F::CONST(f64::E))),
//             "EPS" => Some(F(F::CONST(f64::EPSILON))),
//             _ => None,
//         }
//     }

//     /// Get the function associated with the given `name` and args
//     #[inline]
//     fn func(name: &str, sarg: Option<&str>, args: &[ICV]) -> Option<OP<Self>> {
//         match (name, sarg, args) {
//             ("sin", None, &[FICV(icv)]) => Some(F(F::FUNC(Self::FFN::SIN(icv)))),
//             ("sin", None, &[UICV(icv)]) => Some(U(U::FUNC(Self::UFN::SIN(icv)))),
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
//             "id" => Some(F(F::VAR(123))),
//             _ => Std::var(name),
//         }
//     }

//     /// Get the function associated with the given `name` and args
//     #[inline]
//     fn func(name: &str, sarg: &Option<String>, args: &[ICV]) -> Option<OP<Self>> {
//         Std::func(name, sarg, args)
//     }
// }
