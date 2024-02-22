use criterion::{black_box, criterion_group, criterion_main, Criterion};
use expre::*;
use std::collections::BTreeMap;

fn criterion_benchmark(c: &mut Criterion) {
    let mut ast = expre::Ast::new();
    let mut cexpr = expre::CExpr::new();
    let mut map = BTreeMap::new();
    map.insert("x".to_string(), 10.0);
    map.insert("y".to_string(), 5.0);
    map.insert("z".to_string(), 3.0);

    let expr_str = black_box("-x +((((87))) - tan(x)) + (97 + (((15 / 55*x * ((sin(-31))) + 35))) + (15 - (cos(9))) - (39 / 26) / 20*cos(y) / 91 +(abs(-x))+ 27 / (33 * sin(26) + 28-(+y) - (7) / 10*tan(y) + 66 * 6) + sin(60) / 35 - ((29) - (cos(69)) / 44 / (92)) / (cos(89)) + 2 + 87 / 47 * ((2)) * 83 / 98 * 42 / (((67)) * ((97))) / (34 / 89 + 77) - 29 + 70 * (20)) + ((((((92))) + 23 * (98) / (95) + (((99) * (41))) + (5 + 41) + 10) - (36) / (6 + 80 * 52 + (90))))");
    eprintln!("Benchmarking expr: '{}'\n", expr_str);

    c.bench_function("parse", |b| b.iter(|| expre::parse(expr_str, &mut ast)));

    c.bench_function("compile", |b| b.iter(|| ast.compile(&mut cexpr)));

    c.bench_function("eval", |b| b.iter(|| cexpr.eval(&mut map)));

    c.bench_function("parse -> compile -> eval", |b| {
        b.iter(|| expre::eval2(expr_str, &mut ast, &mut cexpr, &mut map))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
