use crate::compiler::*;
use crate::context::*;
use crate::error::Error;
use crate::float::*;
use crate::{map2, map3};
// use crate::module;
use crate::ops::*;
use indexmap::{IndexMap, IndexSet};
use std::ops::{Add, Div, Index, Mul, Neg, Sub};

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Value<T> {
    FOP(T),
    UOP([T; 2]),
    // V([T; 3]),
}

impl<M> Expression<'_, M>
where
    M: Module,
{
    fn eval<T: Float>(&self, ctx: &[T]) -> Value<T>
    where
        M::FFN: FEvaler<M, T>,
        M::UFN: UEvaler<M, T>,
    {
        match self.ops.last().unwrap() {
            FOP(fop) => Value::FOP(fop.eval(self, ctx)),
            BOP(bop) => Value::FOP(T::from_mask(bop.eval(self, ctx))),
            UOP(uop) => Value::UOP(uop.eval(self, ctx)),
        }
    }

    fn feval<T: Float>(&self, ctx: &[T]) -> T
    where
        M::FFN: FEvaler<M, T>,
        M::UFN: UEvaler<M, T>,
    {
        match self.ops.last().unwrap() {
            FOP(fop) => fop.eval(self, ctx),
            BOP(bop) => T::from_mask(bop.eval(self, ctx)),
            UOP(uop) => uop.eval(self, ctx)[0],
        }
    }

    fn ueval<T: Float>(&self, ctx: &[T]) -> [T; 2]
    where
        M::FFN: FEvaler<M, T>,
        M::UFN: UEvaler<M, T>,
    {
        match self.ops.last().unwrap() {
            UOP(uop) => uop.eval(self, ctx),
            FOP(fop) => [fop.eval(self, ctx); 2],
            BOP(bop) => [T::from_mask(bop.eval(self, ctx)); 2],
        }
    }
}

// // TODO: wtb V -> U conversion?
// pub trait Evaler<M, T>
// where
//     M: Module,
//     T: Float,
// {
//     fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> Value<T>;
//     fn feval(&self, ex: &Expression<M>, ctx: &[T]) -> T;
//     fn ueval(&self, ex: &Expression<M>, ctx: &[T]) -> [T; 2] {
//         [self.feval(ex, ctx); 2]
//     }
//     fn veval(&self, ex: &Expression<M>, ctx: &[T]) -> [T; 3] {
//         [self.feval(ex, ctx); 3]
//     }
// }

pub trait FEvaler<M, T>
where
    M: Module,
    T: Float,
{
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> T;
}

pub trait UEvaler<M, T>
where
    M: Module,
    T: Float,
{
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> [T; 2];
}

pub trait BEvaler<M, T>
where
    M: Module,
    T: Float,
{
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> T::Mask;
}

impl<M, T> FEvaler<M, T> for ()
where
    M: Module,
    T: Float,
{
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> T {
        T::ZERO
    }
}

impl<M, T> UEvaler<M, T> for ()
where
    M: Module,
    T: Float,
{
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> [T; 2] {
        [T::ZERO; 2]
    }
}

impl<M, T> BEvaler<M, T> for B
where
    M: Module,
    T: Float,

    M::FFN: FEvaler<M, T>,
    M::UFN: UEvaler<M, T>,
{
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> T::Mask {
        match self {
            Self::CONST(c) => T::Mask::from_bool(*c),
            Self::VAR(offset) => get(&ctx, *offset).to_mask(),
            Self::I(i) => match ex.get(*i) {
                BOP(bop) => bop.eval(ex, ctx),
                FOP(fop) => fop.eval(ex, ctx).to_mask(),
                UOP(uop) => uop.eval(ex, ctx)[0].to_mask(),
            },
        }
    }
}

impl<M, T> FEvaler<M, T> for F
where
    M: Module,
    T: Float,

    M::FFN: FEvaler<M, T>,
    M::UFN: UEvaler<M, T>,
{
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> T {
        match self {
            Self::CONST(c) => T::from_f64(*c),
            Self::VAR(offset) => *get(&ctx, *offset),
            Self::I(i) => match ex.get(*i) {
                FOP(fop) => fop.eval(ex, ctx),
                BOP(bop) => T::from_mask(bop.eval(ex, ctx)),
                UOP(uop) => uop.eval(ex, ctx)[0],
                _ => unreachable!(),
            },
        }
    }
}

impl<M, T> UEvaler<M, T> for U
where
    M: Module,
    T: Float,

    M::FFN: FEvaler<M, T>,
    M::UFN: UEvaler<M, T>,
{
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> [T; 2] {
        match self {
            Self::CONST([x, y]) => [T::from_f64(*x), T::from_f64(*y)],
            Self::VAR(offset) => *get_n(&ctx, *offset),
            Self::I(i) => match ex.get(*i) {
                UOP(uop) => uop.eval(ex, ctx),
                FOP(fop) => [fop.eval(ex, ctx); 2],
                BOP(bop) => [T::from_mask(bop.eval(ex, ctx)); 2],
                _ => unreachable!(),
            },
        }
    }
}

impl<M, T> BEvaler<M, T> for BOP
where
    M: Module,
    T: Float,

    M::FFN: FEvaler<M, T>,
    M::UFN: UEvaler<M, T>,
{
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> T::Mask {
        let zero = T::ZERO;
        match self {
            Self::EQ(l, r) => Float::eq(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NE(l, r) => Float::ne(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::EQU(l, r) => Float2::eq(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NEU(l, r) => Float2::ne(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::LT(l, r) => Float::lt(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::LE(l, r) => Float::le(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::GE(l, r) => Float::ge(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::GT(l, r) => Float::gt(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NOT(a) => Mask::not(a.eval(ex, ctx)),
            Self::OR(l, r) => Mask::or(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::AND(l, r) => Mask::and(l.eval(ex, ctx), r.eval(ex, ctx)),

            Self::CONST(c) => Mask::from_bool(*c),
            // _ => unimplemented!(),
        }
    }
}

impl<M, T> FEvaler<M, T> for FOP<M::FFN>
where
    M: Module,
    T: Float,

    M::FFN: FEvaler<M, T>,
    M::UFN: UEvaler<M, T>,
{
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> T {
        let zero = T::ZERO;
        match self {
            Self::MUL(l, r) => l.eval(ex, ctx) * r.eval(ex, ctx),
            Self::ADD(l, r) => T::add(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NEG(a) => T::neg(a.eval(ex, ctx)),
            Self::INV(a) => T::recip(a.eval(ex, ctx)),
            Self::REM(l, r) => T::rem(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::POW(l, r) => T::pow(l.eval(ex, ctx), r.eval(ex, ctx)),

            // Self::EQ(l, r) => <T as Float>::eq(l.eval(ex, ctx), r.eval(ex, ctx)),
            // Self::NE(l, r) => <T as Float>::ne(l.eval(ex, ctx), r.eval(ex, ctx)),
            // Self::UEQ(l, r) => {
            //     let [lx, ly] = l.eval(ex, ctx);
            //     let [rx, ry] = r.eval(ex, ctx);
            //     <T as Float>::eq(lx, rx).mul(<T as Float>::eq(ly, ry))
            // }
            // Self::UNE(l, r) => {
            //     let [lx, ly] = l.eval(ex, ctx);
            //     let [rx, ry] = r.eval(ex, ctx);
            //     <T as Float>::ne(lx, rx).mul(<T as Float>::ne(ly, ry))
            // }
            // Self::LT(l, r) => T::lt(l.eval(ex, ctx), r.eval(ex, ctx)),
            // Self::LE(l, r) => T::le(l.eval(ex, ctx), r.eval(ex, ctx)),
            // Self::GE(l, r) => T::ge(l.eval(ex, ctx), r.eval(ex, ctx)),
            // Self::GT(l, r) => T::gt(l.eval(ex, ctx), r.eval(ex, ctx)),
            // Self::NOT(a) => T::not(a.eval(ex, ctx)),
            // Self::OR(l, r) => T::or(l.eval(ex, ctx), r.eval(ex, ctx)),
            // Self::AND(l, r) => T::and(l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::FN(ffn) => ffn.eval(ex, ctx),
            Self::CONST(c) => T::from_f64(*c),
            Self::VAR(offset) => *get(&ctx, *offset),
            // _ => unimplemented!(),
        }
    }
}

impl<M, T> UEvaler<M, T> for UOP<M::UFN>
where
    M: Module,
    T: Float,
    M::FFN: FEvaler<M, T>,
    M::UFN: UEvaler<M, T>,
{
    #[inline]
    fn eval(&self, ex: &Expression<M>, ctx: &[T]) -> [T; 2] {
        let zero = T::ZERO;
        match self {
            Self::SET(x, y) => [x.eval(ex, ctx), y.eval(ex, ctx)],
            Self::ADD(l, r) => map2!(Add::add, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::MUL(l, r) => map2!(Mul::mul, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::POW(l, r) => map2!(T::pow, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::REM(l, r) => map2!(T::rem, l.eval(ex, ctx), r.eval(ex, ctx)),
            Self::NEG(a) => map2!(Neg::neg, a.eval(ex, ctx)),
            Self::INV(a) => map2!(T::recip, a.eval(ex, ctx)),

            Self::FN(ufn) => ufn.eval(ex, ctx),
            Self::CONST(c) => map2!(T::from_f64, c),
            Self::VAR(offset) => *get_n(&ctx, *offset),
            // _ => unimplemented!(),
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
        let expr_str = "[1,1] *[id,0.3]";
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
        //     type FFN = ();
        //     type UFN = ();
        //     type FOP = f32;
        //     fn var(name: &str) -> Option<OP<Self>> {
        //         match name {
        //             "id" => Some(FOP(FOP::VAR(0))),
        //             "b" => Some(FOP(FOP::VAR(1))),
        //             "uv" => Some(UOP(UOP::VAR(2))),
        //             _ => None,
        //         }
        //     }
        // }

        #[derive(Clone)]
        struct MyModule {
            vars: IndexMap<String, ARG>,
        }
        impl Module for MyModule {
            type FFN = ();
            type UFN = ();

            fn dispatch_var(&self, _name: &str) -> Option<&ARG> {
                self.vars.get(_name)
            }
        }
        let mmm = MyModule {
            vars: IndexMap::from([
                ("id".into(), F(F::VAR(0))),
                ("b".into(), F(F::VAR(1))),
                ("uv".into(), U(U::VAR(2))),
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
        impl Context<f32> for Ctx {}

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
        println!("size of U: {}", std::mem::size_of::<U>());
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

        let v = ex.eval(&ctx);
        println!("CEXPR:\n{:?}", ex);
        assert_eq!(Value::FOP(88956.0), v);

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
//         U {
//             // ("sin", x:U) => sin(x),
//             // _("sin", x:U) => sin(x),
//         },
//     }
// }

// module! {
//     MyModule<f32> {
//         F::dot(x:U,y:U);
//         // @F::clamp(x:F) {clamp(x, 0.0, F::VAR(1))};
//         // @F::clamp(x: F) => clamp(x, 0.0, 1.0);
//         U::zzz(x:U);
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
