use crate::compiler::*;
use crate::context::*;
use crate::error::Error;
use crate::float::*;
// use crate::map2;
use crate::module;
use crate::ops::*;
use indexmap::{IndexMap, IndexSet};

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Value<T> {
    FOP(T),
    UOP([T; 2]),
    // V([T; 3]),
}

impl<M> Engine<M>
where
    M: Module,
{
    fn eval<T: Float, CTX: Context<T>>(&self, ctx: &CTX) -> Value<T>
    where
        M::FFN: FEvaler<M, T, CTX>,
        M::UFN: UEvaler<M, T, CTX>,
    {
        match self.ops.last().unwrap() {
            FOP(fop) => Value::FOP(fop.eval(self, ctx)),
            UOP(uop) => Value::UOP(uop.eval(self, ctx)),
        }
    }

    fn feval<T: Float, CTX: Context<T>>(&self, ctx: &CTX) -> T
    where
        M::FFN: FEvaler<M, T, CTX>,
        M::UFN: UEvaler<M, T, CTX>,
    {
        match self.ops.last().unwrap() {
            FOP(fop) => fop.eval(self, ctx),
            UOP(uop) => uop.eval(self, ctx)[0],
        }
    }

    fn ueval<T: Float, CTX: Context<T>>(&self, ctx: &CTX) -> [T; 2]
    where
        M::FFN: FEvaler<M, T, CTX>,
        M::UFN: UEvaler<M, T, CTX>,
    {
        match self.ops.last().unwrap() {
            UOP(uop) => uop.eval(self, ctx),
            FOP(fop) => [fop.eval(self, ctx); 2],
        }
    }
}

pub trait Evaler<M, T, CTX>
where
    M: Module,
    T: Float,
    CTX: Context<T>,
{
    fn eval(&self, ctx: &M, ctx: &CTX) -> Value<T>;
}

pub trait FEvaler<M, T, CTX>
where
    M: Module,
    T: Float,
    CTX: Context<T>,
{
    fn eval(&self, cexpr: &Engine<M>, ctx: &CTX) -> T;
}

pub trait UEvaler<M, T, CTX>
where
    M: Module,
    T: Float,
    CTX: Context<T>,
{
    fn eval(&self, cexpr: &Engine<M>, ctx: &CTX) -> [T; 2];
}

impl<M, T, CTX> FEvaler<M, T, CTX> for ()
where
    M: Module,
    T: Float,
    CTX: Context<T>,
{
    fn eval(&self, cexpr: &Engine<M>, ctx: &CTX) -> T {
        T::ZERO
    }
}

impl<M, T, CTX> UEvaler<M, T, CTX> for ()
where
    M: Module,
    T: Float,
    CTX: Context<T>,
{
    fn eval(&self, cexpr: &Engine<M>, ctx: &CTX) -> [T; 2] {
        [T::ZERO; 2]
    }
}

impl<M, T, CTX> FEvaler<M, T, CTX> for F
where
    M: Module,
    T: Float,
    CTX: Context<T>,
    M::FFN: FEvaler<M, T, CTX>,
    M::UFN: UEvaler<M, T, CTX>,
{
    #[inline]
    fn eval(&self, cexpr: &Engine<M>, ctx: &CTX) -> T {
        match self {
            Self::CONST(c) => T::from_f64(*c),
            Self::VAR(offset) => ctx.get_fvar(*offset),
            Self::I(i) => match cexpr.get(*i) {
                FOP(fop) => fop.eval(cexpr, ctx),
                // UOP(uop) => uop.eval(cexpr, ctx)[0],
                _ => unreachable!(),
            },
        }
    }
}

impl<M, T, CTX> UEvaler<M, T, CTX> for U
where
    M: Module,
    T: Float,
    CTX: Context<T>,
    M::FFN: FEvaler<M, T, CTX>,
    M::UFN: UEvaler<M, T, CTX>,
{
    #[inline]
    fn eval(&self, cexpr: &Engine<M>, ctx: &CTX) -> [T; 2] {
        match self {
            Self::CONST([x, y]) => [T::from_f64(*x), T::from_f64(*y)],
            Self::VAR(offset) => ctx.get_uvar(*offset),
            Self::I(i) => match cexpr.get(*i) {
                UOP(uop) => uop.eval(cexpr, ctx),
                // FOP(fop) => [fop.eval(cexpr, ctx); 2],
                _ => unreachable!(),
            },
            Self::F(ficv) => [ficv.eval(cexpr, ctx); 2],
        }
    }
}

impl<M, T, CTX> FEvaler<M, T, CTX> for FOP<M::FFN>
where
    M: Module,
    T: Float,
    CTX: Context<T>,
    M::FFN: FEvaler<M, T, CTX>,
    M::UFN: UEvaler<M, T, CTX>,
{
    #[inline]
    fn eval(&self, cexpr: &Engine<M>, ctx: &CTX) -> T {
        let zero = T::ZERO;
        match self {
            Self::MUL(licv, ricv) => T::mul(licv.eval(cexpr, ctx), ricv.eval(cexpr, ctx)),
            Self::ADD(licv, ricv) => T::add(licv.eval(cexpr, ctx), ricv.eval(cexpr, ctx)),
            Self::NEG(icv) => T::neg(icv.eval(cexpr, ctx)),
            Self::INV(icv) => T::recip(icv.eval(cexpr, ctx)),
            Self::REM(licv, ricv) => T::rem(licv.eval(cexpr, ctx), ricv.eval(cexpr, ctx)),
            Self::EXP(base, power) => T::pow(base.eval(cexpr, ctx), power.eval(cexpr, ctx)),

            // Self::EQ(licv, ricv) => (licv.eval(cexpr, ctx) == ricv.eval(cexpr, ctx)).into(),
            // Self::NE(licv, ricv) => (licv.eval(cexpr, ctx) != ricv.eval(cexpr, ctx)).into(),
            // Self::LT(licv, ricv) => (licv.eval(cexpr, ctx) < ricv.eval(cexpr, ctx)).into(),
            // Self::LTE(licv, ricv) => (licv.eval(cexpr, ctx) <= ricv.eval(cexpr, ctx)).into(),
            // Self::GTE(licv, ricv) => (licv.eval(cexpr, ctx) >= ricv.eval(cexpr, ctx)).into(),
            // Self::GT(licv, ricv) => (licv.eval(cexpr, ctx) > ricv.eval(cexpr, ctx)).into(),
            // Self::NOT(icv) => (icv.eval(cexpr, ctx) == zero).into(),

            // Self::AND(licv, ricv) => {
            //     let l = licv.eval(cexpr, ctx);
            //     if l == zero {
            //         l
            //     } else {
            //         ricv.eval(cexpr, ctx)
            //     }
            // }
            // Self::OR(licv, ricv) => {
            //     let l = licv.eval(cexpr, ctx);
            //     if l != zero {
            //         l
            //     } else {
            //         ricv.eval(cexpr, ctx)
            //     }
            // }
            Self::FN(ffn) => ffn.eval(cexpr, ctx),
            Self::CONST(c) => T::from_f64(*c),
            Self::VAR(offset) => ctx.get_fvar(*offset),
            _ => unimplemented!(),
        }
    }
}

impl<M, T, CTX> UEvaler<M, T, CTX> for UOP<M::UFN>
where
    M: Module,
    T: Float,
    CTX: Context<T>,
    M::FFN: FEvaler<M, T, CTX>,
    M::UFN: UEvaler<M, T, CTX>,
{
    #[inline]
    fn eval(&self, cexpr: &Engine<M>, ctx: &CTX) -> [T; 2] {
        let zero = T::ZERO;
        match self {
            Self::SET(icv0, icv1) => [icv0.eval(cexpr, ctx), icv1.eval(cexpr, ctx)],
            Self::ADD(licv, ricv) => <[T; 2]>::add(licv.eval(cexpr, ctx), ricv.eval(cexpr, ctx)),
            Self::MUL(licv, ricv) => <[T; 2]>::mul(licv.eval(cexpr, ctx), ricv.eval(cexpr, ctx)),
            Self::EXP(base, power) => <[T; 2]>::pow(base.eval(cexpr, ctx), power.eval(cexpr, ctx)),
            Self::REM(base, power) => <[T; 2]>::rem(base.eval(cexpr, ctx), power.eval(cexpr, ctx)),
            Self::NEG(icv) => <[T; 2]>::neg(icv.eval(cexpr, ctx)),
            Self::INV(icv) => <[T; 2]>::recip(icv.eval(cexpr, ctx)),

            // Self::NOT(icv) => map2!(|x| (x == zero).into(), icv.eval(cexpr)),
            Self::FN(ufn) => ufn.eval(cexpr, ctx),
            Self::CONST([x, y]) => [T::from_f64(*x), T::from_f64(*y)],
            Self::VAR(offset) => ctx.get_uvar(*offset),
            _ => unimplemented!(),
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
        // macro_rules! apply_context {
        //     (struct $NAME: ident { }) => {};
        // }

        // #[repr(C)]
        // #[derive(Debug, Clone)]
        // struct Data {
        //     buffer: Box<u8>,
        //     offsets: IndexMap<String, ICV>,
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

        let mmm = MyModule::with_vars(IndexMap::from([
            ("id".into(), F(F::VAR(0))),
            ("b".into(), F(F::VAR(1))),
            ("uv".into(), U(U::VAR(2))),
            ("pid".into(), F(F::CONST(1.0))),
        ]));

        #[repr(C)]
        #[derive(Debug, Clone)]
        struct Ctx {
            id: f32,
            b: f32,
            uv: [f32; 2],
        }

        let a = 0;
        impl Context<f32> for Ctx {}

        let ctx = Ctx {
            id: 0.5,
            b: 1.0,
            uv: [1.0, 2.0],
        };

        // let expre = Ctx::new();
        // let e = expre.parse("5+6")?;
        // let c = e.compile().try_into()?;
        // let result = c.eval();
        //
        //
        // println!("size of OP: {}", std::mem::size_of::<OP<MyModule>>());
        println!("size of ICV: {}", std::mem::size_of::<ICV>());
        println!("size of F: {}", std::mem::size_of::<F>());
        println!("size of U: {}", std::mem::size_of::<U>());
        let mut ast = Ast::new();

        let mut cexpr = Engine::new();

        let expr_str = "a=sin(id)+uv+id+[1,2] + dot([1,2],1)+uv+b;a";
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

        // cexpr.add_var("x".to_owned(), &data.x);
        // cexpr.add_var("y".to_owned(), &data.y);
        // cexpr.add_var("z".to_owned(), &data.z);
        // cexpr.add_var("w".to_owned(), &data.w);

        let ok = ast.compile(&mut cexpr, &mmm);
        println!("OK: {:?}", ok);
        // eprintln!("CEXPR: {:?}", ok);
        // data.x = 0.0;
        // }

        let v = cexpr.eval(&ctx);
        println!("CEXPR:\n{:?}", cexpr);
        assert_eq!(Value::FOP(88956.0), v);

        // let expr_str = "a=((1+-5.345) +4 +xxxxxxxx +5)-xxxxxxxx;a +((((87))) - tan(xxxxxxxx)) + 1.3446346346346324e-2 + (97 + (((15 / 55*xxxxxxxx * ((sin(-31))) + 35))) + (15 - (cos(9))) - (39 / 26) / 20*cos(yyyyyyyyyyyyy) / 91 +(abs(-xxxxxxxx))+ 27 / (33 * sin(26) + 28-(yyyyyyyyyyyyy) - a*a+(7) / 10*tan(yyyyyyyyyyyyy) + 66 * 6) + sin(60) / 35 - ((29) - (cos(69)) / 44 / (92)) / (cos(89)) + 2 + 87 / 47 * ((2)) * 83 / 98 * 42 / (((67)) * ((97))) / (34 / 89 + 77) - 29 + 70 * (20)) + ((((((92))) + 23 * (98) / (95) + (((99) * (41))) + (5 + 41) + 10) - (36) / (6 + 80 * 52 + (90))))";
        // eprintln!("Test expr: '{}'\n", expr_str);

        // println!("PARSE: {:?}", ast.parse(expr_str));
        // println!("{}", ast);

        // // {

        // let ctx = [10.0, 5.0, 3.0, 3.0];

        // cexpr.add_var("xxxxxxxx".to_owned(), &ctx[0]);
        // cexpr.add_var("yyyyyyyyyyyyy".to_owned(), &ctx[1]);
        // cexpr.add_var("zzzzzzzzzzz".to_owned(), &ctx[2]);
        // cexpr.add_var("wwwwwwwwwwww".to_owned(), &ctx[3]);
        // // cexpr.add_var("w".to_owned(), &data.w);

        // let ok = ast.compile(&mut cexpr);

        // eprintln!("CEXPR: {:?}", ok);
        // // data.x = 0.0;
        // // }

        // let v = cexpr.eval();
        // println!("{:?}", cexpr);
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

module! {
    MyModule<f32> {
        F::dot(x:U,y:U);
        // @F::clamp(x:F) {clamp(x, 0.0, F::VAR(1))};
        // @F::clamp(x: F) => clamp(x, 0.0, 1.0);
        U::zzz(x:U);
    }
}

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
