use crate::error::Error;

use std::collections::BTreeMap;

pub trait Context {
    fn lookup(&self, name: &str, args: &[f64]) -> Option<f64> {
        None
    }
}

// pub struct Ctx<V, F> {
//     val: V,
//     func: F,
// }

// impl<V, F> Ctx<V, F>
// where
//     V: Fn(&str) -> Option<f64>,
//     F: Fn(&str, &[f64]) -> Option<f64>,
// {
//     pub fn new(val: V, func: F) -> Self {
//         Self { val, func }
//     }
// }

impl<F> Context for F
where
    F: Fn(&str, &[f64]) -> Option<f64>,
{
    fn lookup(&self, name: &str, args: &[f64]) -> Option<f64> {
        self(name, args)
    }
}
