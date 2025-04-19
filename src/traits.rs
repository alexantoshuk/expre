use crate::float::*;
use crate::op::ICV;

pub struct Expression<'m, M: Module> {
    module: &'m M,
    pub(crate) ops: Vec<OP<M>>,
}

pub trait Context {
    type T: Float;
    fn f(&self, index: usize) -> Self::T;
    fn f2(&self, index: usize) -> [Self::T; 2];
    fn f3(&self, index: usize) -> [Self::T; 3];
}

pub trait Eval<CTX>: Sized
where
    CTX: Context,
{
    fn eval_b(&self, slab: &[Self], ctx: &CTX) -> <CTX::T as Float>::Mask {
        Default::default()
    }
    fn eval_f(&self, slab: &[Self], ctx: &CTX) -> CTX::T {
        Default::default()
    }
    fn eval_f2<F2: Float2<CTX::T>>(&self, slab: &[Self], ctx: &CTX) -> F2 {
        Default::default()
    }
    fn eval_f3<F3: Float3<CTX::T>>(&self, slab: &[Self], ctx: &CTX) -> F3 {
        Default::default()
    }
}

pub trait Module: Sized {
    type CTX: Context;
    type OP: Eval<Self::CTX>;

    fn dispatch_var(&self, _name: &str) -> Option<&ICV> {
        None
    }

    fn dispatch_fn(&self, _name: &str, _args: &[ICV]) -> Option<Self::OP> {
        None
    }
}

pub enum Type {
    F,
    F2,
    F3,
    B,
    S,
}

pub trait OP {
    fn optype(&self) -> Type;
}
