use criterion::{black_box, criterion_group, criterion_main, Criterion};
use expre::*;
use std::collections::{BTreeMap, HashMap};

fn criterion_benchmark(c: &mut Criterion) {
    let mut ast = expre::Ast::new();
    let mut cexpr = expre::CExpr::new();
    let mut map = BTreeMap::new();
    map.insert("xxxxxxxx".to_string(), 10.0);
    map.insert("yyyyyyyyyyyyy".to_string(), 5.0);
    map.insert("zzzzzzzzzzz".to_string(), 3.0);
    map.insert("wwwwwwwwwwww".to_string(), 3.0);

    let cb = |name: &str, args: Vec<f64>| -> Option<f64> {
        match name {
            "xxxxxxxx" => Some(10.0),
            "yyyyyyyyyyyyy" => Some(5.0),
            "zzzzzzzzzzz" => Some(3.0),
            "wwwwwwwwwwww" => Some(3.0),

            _ => None,
        }
    };
    let expr_str = black_box("-xxxxxxxx +((((87))) - tan(xxxxxxxx)) + 1.3446346346346324e-2 + (97 + (((15 / 55*xxxxxxxx * ((sin(-31))) + 35))) + (15 - (cos(9))) - (39 / 26) / 20*cos(yyyyyyyyyyyyy) / 91 +(abs(-xxxxxxxx))+ 27 / (33 * sin(26) + 28-(+yyyyyyyyyyyyy) - (7) / 10*tan(yyyyyyyyyyyyy) + 66 * 6) + sin(60) / 35 - ((29) - (cos(69)) / 44 / (92)) / (cos(89)) + 2 + 87 / 47 * ((2)) * 83 / 98 * 42 / (((67)) * ((97))) / (34 / 89 + 77) - 29 + 70 * (20)) + ((((((92))) + 23 * (98) / (95) + (((99) * (41))) + (5 + 41) + 10) - (36) / (6 + 80 * 52 + (90))))");
    eprintln!("Benchmarking expr: '{}'\n", expr_str);

    c.bench_function("parse", |b| b.iter(|| expre::parse(expr_str, &mut ast)));

    c.bench_function("compile", |b| b.iter(|| ast.compile(&mut cexpr)));

    c.bench_function("eval", |b| b.iter(|| cexpr.eval(&map)));
    c.bench_function("eval cb", |b| b.iter(|| cexpr.eval(&cb)));

    c.bench_function("parse -> compile -> eval", |b| {
        b.iter(|| expre::eval2(expr_str, &mut ast, &mut cexpr, &map))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
