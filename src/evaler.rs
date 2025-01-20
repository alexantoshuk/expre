use crate::builtins::Builtins;
use crate::compiler::*;
use crate::context::*;
use crate::float::*;
use crate::op::*;
use crate::{map2, map3};
use indexmap::{IndexMap, IndexSet};
use std::ops::{Add, Div, Index, Mul, Neg, Sub};

#[derive(Debug, Clone, PartialEq)]
pub enum Value<T> {
    F(T),
    F2([T; 2]),
    F3([T; 3]),
}

pub trait Inner<T> {
    fn inner(self) -> T;
}

impl<T> Inner<T> for Value<T> {
    #[inline]
    fn inner(self) -> T {
        match self {
            Self::F(x) => x,
            Self::F2([x, _]) => x,
            Self::F3([x, _, _]) => x,
        }
    }
}

impl<T> Inner<[T; 1]> for Value<T> {
    #[inline]
    fn inner(self) -> [T; 1] {
        match self {
            Self::F(x) => [x],
            Self::F2([x, _]) => [x],
            Self::F3([x, _, _]) => [x],
        }
    }
}

impl<T: Float> Inner<[T; 2]> for Value<T> {
    #[inline]
    fn inner(self) -> [T; 2] {
        match self {
            Self::F2(xy) => xy,
            Self::F(x) => [x, T::ZERO],
            Self::F3([x, y, _]) => [x, y],
        }
    }
}

impl<T: Float> Inner<[T; 3]> for Value<T> {
    #[inline]
    fn inner(self) -> [T; 3] {
        match self {
            Self::F3(xyz) => xyz,
            Self::F(x) => [x, T::ZERO, T::ZERO],
            Self::F2([x, y]) => [x, y, T::ZERO],
        }
    }
}

pub trait Eval<M, CTX>
where
    M: Module,
    CTX: Context,
{
    type Output: Default;
    fn eval(&self, ex: &Expression<M>, ctx: &CTX) -> Self::Output {
        Default::default()
    }
}

impl<M> Expression<'_, M>
where
    M: Module,
{
    fn eval<CTX>(&self, ctx: &CTX) -> Value<CTX::T>
    where
        CTX: Context,
    {
        match self.ops.last().unwrap() {
            FOP(o) => Value::F(o.eval(self, ctx)),
            FOP2(o) => Value::F2(o.eval(self, ctx)),
            FOP3(o) => Value::F3(o.eval(self, ctx)),
            BOP(o) => Value::F(Float::from_mask(o.eval(self, ctx))),
        }
    }
}

impl<M, CTX> Eval<M, CTX> for B
where
    M: Module,
    CTX: Context,
{
    type Output = <CTX::T as Float>::Mask;

    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &CTX) -> Self::Output {
        match self {
            Self::CONST(c) => <CTX::T as Float>::Mask::from_bool(*c),
            Self::VAR(offset) => ctx.f(*offset).to_mask(),
            Self::I(i) => match ex.get(*i) {
                BOP(o) => o.eval(ex, ctx),
                _ => unreachable!(),
            },
        }
    }
}

// impl<M, CTX> EvalB<M, CTX> for B
// where
//     M: Module,
//     CTX: Context,
// {
//     #[inline]
//     fn eval(&self, ex: &Expression<M>, ctx: &CTX) -> <CTX::T as Float>::Mask {
//         match self {
//             Self::CONST(c) => <CTX::T as Float>::Mask::from_bool(*c),
//             Self::VAR(offset) => ctx.f(*offset).to_mask(),
//             Self::I(i) => match ex.get(*i) {
//                 BOP(o) => o.eval(ex, ctx),
//                 _ => unreachable!(),
//             },
//         }
//     }
// }

impl<M, CTX> Eval<M, CTX> for F
where
    M: Module,
    CTX: Context,
{
    type Output = CTX::T;
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &CTX) -> Self::Output {
        match self {
            Self::CONST(c) => CTX::T::from_f64(*c),
            Self::VAR(offset) => ctx.f(*offset),
            Self::I(i) => match ex.get(*i) {
                FOP(o) => o.eval(ex, ctx),
                _ => unreachable!(),
            },
        }
    }
}

impl<M, CTX> Eval<M, CTX> for F2
where
    M: Module,
    CTX: Context,
{
    type Output = [CTX::T; 2];
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &CTX) -> Self::Output {
        match self {
            Self::CONST([x, y]) => [CTX::T::from_f64(*x), CTX::T::from_f64(*y)],
            Self::VAR(offset) => ctx.f2(*offset),
            Self::I(i) => match ex.get(*i) {
                FOP2(o) => o.eval(ex, ctx),
                _ => unreachable!(),
            },
            Self::F(f) => [f.eval(ex, ctx); 2],
        }
    }
}

impl<M, CTX> Eval<M, CTX> for F3
where
    M: Module,
    CTX: Context,
{
    type Output = [CTX::T; 3];
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &CTX) -> Self::Output {
        match self {
            Self::CONST([x, y, z]) => [
                CTX::T::from_f64(*x),
                CTX::T::from_f64(*y),
                CTX::T::from_f64(*z),
            ],
            Self::VAR(offset) => ctx.f3(*offset),
            Self::I(i) => match ex.get(*i) {
                FOP3(o) => o.eval(ex, ctx),
                _ => unreachable!(),
            },
            Self::F(f) => [f.eval(ex, ctx); 3],
        }
    }
}

impl<M, CTX> Eval<M, CTX> for BOP
where
    M: Module,
    CTX: Context,
{
    type Output = <CTX::T as Float>::Mask;

    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &CTX) -> <CTX::T as Float>::Mask {
        match self {
            Self::EQ(l, r) => Float::eq(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NE(l, r) => Float::ne(l.eval(ex, ctx), r.eval(ex, ctx)),

            Self::EQ2(l, r) => Float2::eq(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NE2(l, r) => Float2::ne(l.eval(ex, ctx), r.eval(ex, ctx)),

            Self::EQ3(l, r) => Float3::eq(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NE3(l, r) => Float3::ne(l.eval(ex, ctx), r.eval(ex, ctx)),

            Self::LT(l, r) => Float::lt(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::LE(l, r) => Float::le(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::GE(l, r) => Float::ge(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::GT(l, r) => Float::gt(l.eval(ex, ctx), r.eval(ex, ctx)),

            Self::NOT(a) => Mask::not(a.eval(ex, ctx)),
            Self::OR(l, r) => Mask::or(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::AND(l, r) => Mask::and(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::IF(b, then, els) => {
                Mask::select(b.eval(ex, ctx), then.eval(ex, ctx), els.eval(ex, ctx))
            }
            Self::CONST(c) => Mask::from_bool(*c),
        }
    }
}

impl<M, CTX> Eval<M, CTX> for FOP
where
    M: Module,
    CTX: Context,
{
    type Output = CTX::T;
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &CTX) -> Self::Output {
        match self {
            Self::MUL(l, r) => l.eval(ex, ctx) * r.eval(ex, ctx),
            Self::ADD(l, r) => Add::add(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NEG(a) => Neg::neg(a.eval(ex, ctx)),
            Self::INV(a) => Float::recip(a.eval(ex, ctx)),
            Self::REM(l, r) => Float::rem(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::POW(l, r) => Float::pow(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::IF(b, then, els) => {
                Float::select(b.eval(ex, ctx), then.eval(ex, ctx), els.eval(ex, ctx))
            }
            Self::STDFN(f) => f.eval(ex, ctx),
            Self::CONST(c) => Float::from_f64(*c),
            Self::VAR(offset) => ctx.f(*offset),
        }
    }
}

impl<M, CTX> Eval<M, CTX> for FOP2
where
    M: Module,
    CTX: Context,
{
    type Output = [CTX::T; 2];
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &CTX) -> Self::Output {
        match self {
            Self::NEW([x, y]) => [x.eval(ex, ctx), y.eval(ex, ctx)],
            Self::ADD(l, r) => map2!(Add::add, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::MUL(l, r) => map2!(Mul::mul, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::POW(l, r) => map2!(Float::pow, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::REM(l, r) => map2!(Float::rem, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NEG(a) => map2!(Neg::neg, a.eval(ex, ctx)),
            Self::INV(a) => map2!(Float::recip, a.eval(ex, ctx)),
            Self::IF(b, then, els) => {
                Float2::select(b.eval(ex, ctx), then.eval(ex, ctx), els.eval(ex, ctx))
            }
            Self::STDFN(f) => f.eval(ex, ctx),
            Self::CONST(c) => map2!(Float::from_f64, c),
            Self::VAR(offset) => ctx.f2(*offset),
        }
    }
}

impl<M, CTX> Eval<M, CTX> for FOP3
where
    M: Module,
    CTX: Context,
{
    type Output = [CTX::T; 3];
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &CTX) -> Self::Output {
        match self {
            Self::NEW([x, y, z]) => [x.eval(ex, ctx), y.eval(ex, ctx), z.eval(ex, ctx)],
            Self::ADD(l, r) => map3!(Add::add, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::MUL(l, r) => map3!(Mul::mul, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::POW(l, r) => map3!(Float::pow, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::REM(l, r) => map3!(Float::rem, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NEG(a) => map3!(Neg::neg, a.eval(ex, ctx)),
            Self::INV(a) => map3!(Float::recip, a.eval(ex, ctx)),
            Self::IF(b, then, els) => {
                Float3::select(b.eval(ex, ctx), then.eval(ex, ctx), els.eval(ex, ctx))
            }
            Self::STDFN(f) => f.eval(ex, ctx),
            Self::CONST(c) => map3!(Float::from_f64, c),
            Self::VAR(offset) => ctx.f3(*offset),
        }
    }
}

#[cfg(test)]
mod test {
    use core::f64;

    use super::*;
    use crate::parser::Ast;
    #[test]
    fn test_eval() {
        let expr_str = "a=5+id;c=a+2;c";
        // macro_rules! apply_context {
        //     (struct $NAME: ident { }) => {};
        // }

        // #[repr(C)]
        // #[derive(Debug, Clone)]
        // struct Data {
        //     buffer: Box<u8>,
        //     offsets: IndexMap<String, ARG>,
        // }

        // impl Module for Data {
        //     type STDFN = ();
        //     type FN2 = ();
        //     type FOP = f32;
        //     fn var(name: &str) -> Option<OP<Self>> {
        //         match name {
        //             "id" => Some(FOP(FOP::VAR(0))),
        //             "b" => Some(FOP(FOP::VAR(1))),
        //             "uv" => Some(FOP2(FOP2::VAR(2))),
        //             _ => None,
        //         }
        //     }
        // }

        let mmm = Builtins {
            vars: IndexMap::from([
                ("id".into(), F(F::VAR(0))),
                ("b".into(), F(F::VAR(1))),
                ("uv".into(), F2(F2::VAR(2))),
                ("pid".into(), F(F::CONST(1.0))),
            ]),
        };

        #[repr(C)]
        #[derive(Debug, Clone)]
        struct Ctx {
            id: f32,
            b: f32,
            uv: [f32; 2],
        }

        let a = 0;

        let ctx = [0.5, 1.0, 1.0, 2.0];

        // let expre = Ctx::new();
        // let e = expre.parse("5+6")?;
        // let c = e.compile().try_into()?;
        // let result = c.eval();
        //
        //
        // println!("size of OP: {}", std::mem::size_of::<OP<MyModule>>());
        println!("size of ARG: {}", std::mem::size_of::<ARG>());
        println!("size of F: {}", std::mem::size_of::<F>());
        println!("size of F2: {}", std::mem::size_of::<F2>());
        let mut ast = Ast::new();

        let mut ex = Expression::new(&mmm);

        eprintln!("Test expr: '{}'\n", expr_str);

        println!("PARSE: {:?}", ast.parse(expr_str));
        println!("AST: {}", ast);
        // struct Data {
        //     x: f32,
        //     y: FCONST,
        //     z: FCONST,
        //     // w: UnsafeCell<f64>,
        // }
        // // {
        // let mut data = Data {
        //     x: 10.0,
        //     y: 5.0,
        //     z: 3.0,
        //     // w: 4.0.into(),
        // };

        // ex.add_var("x".to_owned(), &data.x);
        // ex.add_var("y".to_owned(), &data.y);
        // ex.add_var("z".to_owned(), &data.z);
        // ex.add_var("w".to_owned(), &data.w);

        let ok = ast.compile(&mut ex);
        println!("OK: {:?}", ok);
        // eprintln!("CEXPR: {:?}", ok);
        // data.x = 0.0;
        // }

        let v = ex.eval(&ctx.as_slice());
        println!("CEXPR:\n{:?}", ex);
        assert_eq!(Value::F2([88956.0; 2]), v);

        // let expr_str = "a=((1+-5.345) +4 +xxxxxxxx +5)-xxxxxxxx;a +((((87))) - tan(xxxxxxxx)) + 1.3446346346346324e-2 + (97 + (((15 / 55*xxxxxxxx * ((sin(-31))) + 35))) + (15 - (cos(9))) - (39 / 26) / 20*cos(yyyyyyyyyyyyy) / 91 +(abs(-xxxxxxxx))+ 27 / (33 * sin(26) + 28-(yyyyyyyyyyyyy) - a*a+(7) / 10*tan(yyyyyyyyyyyyy) + 66 * 6) + sin(60) / 35 - ((29) - (cos(69)) / 44 / (92)) / (cos(89)) + 2 + 87 / 47 * ((2)) * 83 / 98 * 42 / (((67)) * ((97))) / (34 / 89 + 77) - 29 + 70 * (20)) + ((((((92))) + 23 * (98) / (95) + (((99) * (41))) + (5 + 41) + 10) - (36) / (6 + 80 * 52 + (90))))";
        // eprintln!("Test expr: '{}'\n", expr_str);

        // println!("PARSE: {:?}", ast.parse(expr_str));
        // println!("{}", ast);

        // // {

        // let ctx = [10.0, 5.0, 3.0, 3.0];

        // ex.add_var("xxxxxxxx".to_owned(), &ctx[0]);
        // ex.add_var("yyyyyyyyyyyyy".to_owned(), &ctx[1]);
        // ex.add_var("zzzzzzzzzzz".to_owned(), &ctx[2]);
        // ex.add_var("wwwwwwwwwwww".to_owned(), &ctx[3]);
        // // ex.add_var("w".to_owned(), &data.w);

        // let ok = ast.compile(&mut ex);

        // eprintln!("CEXPR: {:?}", ok);
        // // data.x = 0.0;
        // // }

        // let v = ex.eval();
        // println!("{:?}", ex);
        // assert_eq!(Value::FOP(5807.369321620128), v);
    }
}

// module! {
//     MyModule {
//         F {
//             F("sin", x:F) => sin(x),
//             F("cos", x:F) => cos(x),
//             F("clamp", x:F, min:F, max:F) => clamp(x,min,max),
//             // ("rand", min:FOP, max:FOP, seed:FOP) => rand(min,max,seed),
//             // ("rand", min:FOP, max:FOP) => rand(min,max,var("seed")),
//             // ("rand", seed:FOP) => rand(0.0,1.0,seed),
//             // ("rand") => rand(0.0,1.0,var("seed")),
//             F("clamp", x:F) => clamp(x, 0.0, F::VAR(1)),
//         },
//         F2 {
//             // ("sin", x:F2) => sin(x),
//             // _("sin", x:F2) => sin(x),
//         },
//     }
// }

// module! {
//     MyModule<f32> {
//         F::dot(x:F2,y:F2);
//         // @F::clamp(x:F) {clamp(x, 0.0, F::VAR(1))};
//         // @F::clamp(x: F) => clamp(x, 0.0, 1.0);
//         F2::zzz(x:F2);
//     }
// }

trait ZZZ {
    fn zzz(self) -> Self;
}

impl ZZZ for [f32; 2] {
    fn zzz(self) -> Self {
        [self[0] * self[0], self[1] * self[1]]
    }
}

impl ZZZ for [f64; 2] {
    fn zzz(self) -> Self {
        [self[0] * self[0], self[1] * self[1]]
    }
}

trait UUU: Sized {
    fn uuu(self) -> Self;
    fn dot(x: [Self; 2], y: [Self; 2]) -> Self;
}

impl UUU for f32 {
    fn uuu(self) -> Self {
        self * self
    }
    fn dot(x: [Self; 2], y: [Self; 2]) -> Self {
        x[0]
    }
}

impl UUU for f64 {
    fn uuu(self) -> Self {
        self * self
    }
    fn dot(x: [Self; 2], y: [Self; 2]) -> Self {
        x[0]
    }
}
