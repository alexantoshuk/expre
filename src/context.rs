use crate::compiler::Expression;
use crate::error::Error;
use crate::float::Float;
use crate::op::*;
use bytemuck::Pod;
use std::fmt::Debug;
use std::hash::Hash;

pub trait Module: Sized + Clone + Debug {
    fn dispatch_ident(&self, _name: &str) -> Option<OP> {
        None
    }

    fn dispatch_func(&self, _name: &str, string: Option<&str>, _args: &[ARG]) -> Option<OP> {
        None
    }
}

pub trait Context {
    type T: Float;
    fn f(&self, index: usize) -> Self::T;
    //  {
    //     unsafe { *((self as *const Self as *const Self::T).add(index)) }
    // }

    fn f2(&self, index: usize) -> [Self::T; 2];
    //  {
    //     unsafe { *((self as *const Self as *const Self::T).add(index) as *const [Self::T; 2]) }
    // }

    fn f3(&self, index: usize) -> [Self::T; 3];
    //  {
    //     unsafe { *((self as *const Self as *const Self::T).add(index) as *const [Self::T; 3]) }
    // }
}

impl<T: Float> Context for &[T] {
    type T = T;
    fn f(&self, index: usize) -> T {
        debug_assert!(index < self.len());
        unsafe { *((self.as_ptr() as *const Self::T).add(index)) }
    }

    fn f2(&self, index: usize) -> [T; 2] {
        debug_assert!(index + 1 < self.len());
        unsafe { *((self.as_ptr() as *const Self::T).add(index) as *const [Self::T; 2]) }
    }

    fn f3(&self, index: usize) -> [T; 3] {
        debug_assert!(index + 2 < self.len());
        unsafe { *((self.as_ptr() as *const Self::T).add(index) as *const [Self::T; 3]) }
    }
}
