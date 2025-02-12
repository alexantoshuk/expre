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

    fn dispatch_func(&self, _name: &str, _string: Option<&str>, _args: &[ARG]) -> Option<OP> {
        None
    }
}

pub struct Buffer<T>(Vec<T>);
impl<T> Buffer<T> {
    pub fn push(&mut self, value: T) -> usize {
        let pos = self.0.len();
        self.0.push(value);
        pos
    }

    pub fn push_n<const N: usize>(&mut self, value: [T; N]) -> usize {
        let pos = self.0.len();
        for v in value {
            self.0.push(v);
        }
        pos
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.0.get(index)
    }

    pub fn get_n<const N: usize>(&self, index: usize) -> Option<&[T; N]> {
        if index + N.max(1) <= self.0.len() {
            Some(unsafe { self.get_n_unchecked(index) })
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.0.get_mut(index)
    }

    pub fn get_n_mut<const N: usize>(&mut self, index: usize) -> Option<&mut [T; N]> {
        if index + N.max(1) <= self.0.len() {
            Some(unsafe { self.get_n_unchecked_mut(index) })
        } else {
            None
        }
    }

    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        self.0.get_unchecked(index)
    }

    pub unsafe fn get_n_unchecked<const N: usize>(&self, index: usize) -> &[T; N] {
        &*(self.0.as_ptr().add(index) as *const [T; N])
    }

    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        self.0.get_unchecked_mut(index)
    }

    pub unsafe fn get_n_unchecked_mut<const N: usize>(&mut self, index: usize) -> &mut [T; N] {
        &mut *(self.0.as_mut_ptr().add(index) as *mut [T; N])
    }
}

impl<T, V: Into<Vec<T>>> From<V> for Buffer<T> {
    fn from(value: V) -> Self {
        Self(value.into())
    }
}

// pub struct BufferRef<T>([T]);
// impl<T> BufferRef<T> {
//     pub fn get(&self, index: usize) -> Option<&T> {
//         self.0.get(index)
//     }

//     pub fn get2(&self, index: usize) -> Option<&[T; 2]> {
//         if index + 1 < self.0.len() {
//             Some(unsafe { &*(self.0.as_ptr().add(index) as *const [T; 2]) })
//         } else {
//             None
//         }
//     }

//     pub fn get3(&self, index: usize) -> Option<&[T; 3]> {
//         if index + 2 < self.0.len() {
//             Some(unsafe { &*(self.0.as_ptr().add(index) as *const [T; 3]) })
//         } else {
//             None
//         }
//     }
// }

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
