use criterion::{black_box, criterion_group, criterion_main, Criterion};
use expre::*;
use indexmap::IndexSet;
use module::Builtins;
use std::collections::{BTreeMap, HashMap};

fn criterion_benchmark(c: &mut Criterion) {
    let mut ast = expre::Ast::new();
    let mut cexpr: CExpr<Builtins> = expre::CExpr::new();
    // let mut map = BTreeMap::new();
    // map.insert("xxxxxxxx".to_string(), 10.0);
    // map.insert("yyyyyyyyyyyyy".to_string(), 5.0);
    // map.insert("zzzzzzzzzzz".to_string(), 3.0);
    // map.insert("wwwwwwwwwwww".to_string(), 3.0);

    // let ctx = |name: &str, _: &[_]| match name {
    //     "xxxxxxxx" => Some(10.0),
    //     "yyyyyyyyyyyyy" => Some(5.0),
    //     "zzzzzzzzzzz" => Some(3.0),
    //     "wwwwwwwwwwww" => Some(3.0),
    //     _ => None,
    // };
    // let vars = [
    //     "xxxxxxxx".to_owned(),
    //     "yyyyyyyyyyyyy".to_owned(),
    //     "zzzzzzzzzzz".to_owned(),
    //     "wwwwwwwwwwww".to_owned(),
    // ];
    let ctx = [10.0, 5.0, 3.0, 3.0];

    // let mapctx = |name: &str, _: &[_]| map.get(name).copied();

    let expr_str = black_box("a=((1+5) +4 +xxxxxxxx +5)-xxxxxxxx;a +((((87))) - tan(xxxxxxxx)) + 1.3446346346346324e-2 + (97 + (((15 / 55*xxxxxxxx * ((sin(-31))) + 35))) + (15 - (cos(9))) - (39 / 26) / 20*cos(yyyyyyyyyyyyy) / 91 +(abs(-xxxxxxxx))+ 27 / (33 * sin(26) + 28-(+yyyyyyyyyyyyy) - (7) / 10*tan(yyyyyyyyyyyyy) + 66 * 6) + sin(60) / 35 - ((29) - (cos(69)) / 44 / (92)) / (cos(89)) + 2 + 87 / 47 * ((2)) * 83 / 98 * 42 / (((67)) * ((97))) / (34 / 89 + 77) - 29 + 70 * (20)) + ((((((92))) + 23 * (98) / (95) + (((99) * (41))) + (5 + 41) + 10) - (36) / (6 + 80 * 52 + (90))))");
    eprintln!("Benchmarking expr: '{}'\n", expr_str);

    c.bench_function("parse", |b| b.iter(|| expre::parse(expr_str, &mut ast)));

    cexpr.add_var("xxxxxxxx".to_owned(), &ctx[0]);
    cexpr.add_var("yyyyyyyyyyyyy".to_owned(), &ctx[1]);
    cexpr.add_var("zzzzzzzzzzz".to_owned(), &ctx[2]);
    cexpr.add_var("wwwwwwwwwwww".to_owned(), &ctx[3]);

    c.bench_function("compile", |b| b.iter(|| ast.compile(&mut cexpr)));

    c.bench_function("eval", |b| b.iter(|| cexpr.eval()));

    // c.bench_function("parse -> compile -> eval", |b| {
    //     b.iter(|| expre::eval2(expr_str, &mut ast, &mut cexpr, &ctx))
    // });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
