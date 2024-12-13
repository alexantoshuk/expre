use crate::compiler::*;
use crate::context::*;
use crate::error::Error;
use crate::float::*;
use crate::map2;
use crate::ops::*;
use indexmap::IndexMap;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Value<T> {
    F(T),
    U([T; 2]),
    // V([T; 3]),
}

impl<M> CExpr<M>
where
    M: Module,
{
    fn eval<CTX: Context>(&self, ctx: &CTX) -> Value<CTX::F>
    where
        M::FFN: FEvaler<M, CTX>,
        M::UFN: UEvaler<M, CTX>,
    {
        match self.ops.last().unwrap() {
            F(fop) => Value::F(fop.eval(self, ctx)),
            U(uop) => Value::U(uop.eval(self, ctx)),
        }
    }

    fn feval<CTX: Context>(&self, ctx: &CTX) -> CTX::F
    where
        M::FFN: FEvaler<M, CTX>,
        M::UFN: UEvaler<M, CTX>,
    {
        match self.ops.last().unwrap() {
            F(fop) => fop.eval(self, ctx),
            U(uop) => uop.eval(self, ctx)[0],
        }
    }

    fn ueval<CTX: Context>(&self, ctx: &CTX) -> [CTX::F; 2]
    where
        M::FFN: FEvaler<M, CTX>,
        M::UFN: UEvaler<M, CTX>,
    {
        match self.ops.last().unwrap() {
            U(uop) => uop.eval(self, ctx),
            F(fop) => [fop.eval(self, ctx); 2],
        }
    }
}

pub trait Evaler<M, CTX>
where
    M: Module,
    CTX: Context,
{
    fn eval(&self, ctx: &M, ctx: &CTX) -> Value<CTX::F>;
}

pub trait FEvaler<M, CTX>
where
    M: Module,
    CTX: Context,
{
    fn eval(&self, cexpr: &CExpr<M>, ctx: &CTX) -> CTX::F;
}

pub trait UEvaler<M, CTX>
where
    M: Module,

    CTX: Context,
{
    fn eval(&self, cexpr: &CExpr<M>, ctx: &CTX) -> [CTX::F; 2];
}

impl<M, CTX> FEvaler<M, CTX> for ()
where
    M: Module,
    CTX: Context,
{
    fn eval(&self, cexpr: &CExpr<M>, ctx: &CTX) -> CTX::F {
        CTX::F::ZERO
    }
}

impl<M, CTX> UEvaler<M, CTX> for ()
where
    M: Module,

    CTX: Context,
{
    fn eval(&self, cexpr: &CExpr<M>, ctx: &CTX) -> [CTX::F; 2] {
        [CTX::F::ZERO; 2]
    }
}

impl<M, CTX> FEvaler<M, CTX> for FICV
where
    M: Module,
    CTX: Context,
    M::FFN: FEvaler<M, CTX>,
    M::UFN: UEvaler<M, CTX>,
{
    #[inline]
    fn eval(&self, cexpr: &CExpr<M>, ctx: &CTX) -> CTX::F {
        match self {
            Self::CONST(c) => CTX::F::from_f64(*c),
            Self::VAR(offset) => ctx.get_fvar(*offset),
            Self::I(i) => match cexpr.get(*i) {
                F(fop) => fop.eval(cexpr, ctx),
                U(uop) => uop.eval(cexpr, ctx)[0],
            },
        }
    }
}

impl<M, CTX> UEvaler<M, CTX> for UICV
where
    M: Module,
    CTX: Context,
    M::FFN: FEvaler<M, CTX>,
    M::UFN: UEvaler<M, CTX>,
{
    #[inline]
    fn eval(&self, cexpr: &CExpr<M>, ctx: &CTX) -> [CTX::F; 2] {
        match self {
            Self::CONST([x, y]) => [CTX::F::from_f64(*x), CTX::F::from_f64(*y)],
            Self::VAR(offset) => ctx.get_uvar(*offset),
            Self::I(i) => match cexpr.get(*i) {
                U(uop) => uop.eval(cexpr, ctx),
                F(fop) => [fop.eval(cexpr, ctx); 2],
            },
            // Self::FROM(fcv) => [fcv.eval(cexpr, ctx); 2],
        }
    }
}

impl<M, CTX> FEvaler<M, CTX> for F<M::FFN>
where
    M: Module,
    CTX: Context,
    M::FFN: FEvaler<M, CTX>,
    M::UFN: UEvaler<M, CTX>,
{
    #[inline]
    fn eval(&self, cexpr: &CExpr<M>, ctx: &CTX) -> CTX::F {
        let zero = CTX::F::ZERO;
        match self {
            // FI have manually ordered these match arms in a way that FI feel should deliver good performance.
            // (FI don't think this ordering actually affects the generated code, though.)s
            Self::MUL(licv, ricv) => licv.eval(cexpr, ctx) * ricv.eval(cexpr, ctx),
            Self::ADD(licv, ricv) => licv.eval(cexpr, ctx) + ricv.eval(cexpr, ctx),
            Self::MOD(licv, ricv) => CTX::F::rem(licv.eval(cexpr, ctx), ricv.eval(cexpr, ctx)),
            Self::EXP(base, power) => CTX::F::pow(base.eval(cexpr, ctx), power.eval(cexpr, ctx)),
            Self::NEG(icv) => -icv.eval(cexpr, ctx),
            Self::INV(icv) => CTX::F::recip(icv.eval(cexpr, ctx)),

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
            Self::CONST(c) => CTX::F::from_f64(*c),
            Self::VAR(offset) => ctx.get_fvar(*offset),
            _ => unimplemented!(),
        }
    }
}

impl<M, CTX> UEvaler<M, CTX> for U<M::UFN>
where
    M: Module,
    CTX: Context,
    M::FFN: FEvaler<M, CTX>,
    M::UFN: UEvaler<M, CTX>,
{
    #[inline]
    fn eval(&self, cexpr: &CExpr<M>, ctx: &CTX) -> [CTX::F; 2] {
        let zero = CTX::F::ZERO;
        match self {
            Self::SET(icv0, icv1) => [icv0.eval(cexpr, ctx), icv1.eval(cexpr, ctx)],
            Self::ADD(licv, ricv) => map2!(
                std::ops::Add::add,
                licv.eval(cexpr, ctx),
                ricv.eval(cexpr, ctx)
            ),
            Self::MUL(licv, ricv) => map2!(
                std::ops::Mul::mul,
                licv.eval(cexpr, ctx),
                ricv.eval(cexpr, ctx)
            ),
            Self::EXP(base, power) => {
                map2!(CTX::F::pow, base.eval(cexpr, ctx), power.eval(cexpr, ctx))
            }
            Self::MOD(base, power) => {
                map2!(CTX::F::rem, base.eval(cexpr, ctx), power.eval(cexpr, ctx))
            }
            Self::NEG(icv) => map2!(std::ops::Neg::neg, icv.eval(cexpr, ctx)),
            Self::INV(icv) => map2!(CTX::F::recip, icv.eval(cexpr, ctx)),

            // Self::NOT(icv) => map2!(|x| (x == zero).into(), icv.eval(cexpr)),
            Self::CONST(c) => map2!(CTX::F::from_f64, c),
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
        //     type F = f32;
        //     fn var(name: &str) -> Option<OP<Self>> {
        //         match name {
        //             "id" => Some(F(F::VAR(0))),
        //             "b" => Some(F(F::VAR(1))),
        //             "uv" => Some(U(U::VAR(2))),
        //             _ => None,
        //         }
        //     }
        // }

        #[repr(C)]
        #[derive(Debug, Clone)]
        struct MyModule(IndexMap<String, OP<(), ()>>);
        impl MyModule {
            fn new(m: IndexMap<String, OP<(), ()>>) -> Self {
                MyModule(m)
            }
        }

        impl Module for MyModule {
            type FFN = ();
            type UFN = ();

            fn var(&self, name: &str) -> Option<OP<(), ()>> {
                self.0.get(name).cloned()
            }
        }
        let mmm = MyModule::new(IndexMap::from([
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
        impl Context for Ctx {
            type F = f32;
        }

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
        println!("size of FICV: {}", std::mem::size_of::<FICV>());
        println!("size of UICV: {}", std::mem::size_of::<UICV>());
        let mut ast = Ast::new();

        let mut cexpr = CExpr::new();

        let expr_str = "a=3+uv+id+[1,2] + 0.5+uv+b;a";
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

        // eprintln!("CEXPR: {:?}", ok);
        // data.x = 0.0;
        // }

        let v = cexpr.eval(&ctx);
        println!("CEXPR:\n{:?}", cexpr);
        assert_eq!(Value::F(88956.0), v);

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
        // assert_eq!(Value::F(5807.369321620128), v);
    }
}
