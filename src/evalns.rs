use crate::error::Error;

use std::collections::BTreeMap;

//---- Types:

/// All `expre` Namespaces must implement the `EvalNamespace` trait.
pub trait EvalNamespace {
    /// Perform a variable/function lookup.
    ///
    /// May return cached values.
    fn lookup(&self, name: &str, args: Vec<f64>) -> Option<f64>;
}

//// I don't want to put this into the public API until it is needed.
// pub trait Layered {
//     fn push(&self);
//     fn pop(&self);
// }

/// Use `EmptyNamespace` when you know that you won't be looking up any variables.
///
/// It is a zero-sized type, which means it gets optimized-away at compile time.
///
/// [See module-level documentation for example.](index.html#emptynamespace)
///
pub struct EmptyNamespace;

/// Type alias for `BTreeMap<String,f64>`
pub type StringToF64Namespace = BTreeMap<String, f64>;
impl EvalNamespace for StringToF64Namespace {
    #[inline]
    fn lookup(&self, name: &str, args: Vec<f64>) -> Option<f64> {
        self.get(name).copied()
    }
}

/// Type alias for `BTreeMap<&'static str,f64>`
pub type StrToF64Namespace = BTreeMap<&'static str, f64>;
impl EvalNamespace for StrToF64Namespace {
    #[inline]
    fn lookup(&self, name: &str, args: Vec<f64>) -> Option<f64> {
        self.get(name).copied()
    }
}

/// Type alias for `BTreeMap<String, Box<dyn FnMut(Vec<f64>)->f64>>`
///
/// This namespace type provides a very convenient way to register variables
/// and custom functions.  It is a bit slower than a pure callback, but it has
/// isolation and composition advantages.
pub type StringToCallbackNamespace<'a> = BTreeMap<String, Box<dyn Fn(Vec<f64>) -> f64 + 'a>>;
impl EvalNamespace for StringToCallbackNamespace<'_> {
    #[inline]
    fn lookup(&self, name: &str, args: Vec<f64>) -> Option<f64> {
        if let Some(f) = self.get(name) {
            Some(f(args))
        } else {
            None
        }
    }
}

/// Type alias for `BTreeMap<&'static str, Box<dyn FnMut(Vec<f64>)->f64>>`
///
/// This namespace type provides a very convenient way to register variables
/// and custom functions.  It is a bit slower than a pure callback, but it has
/// isolation and composition advantages.
pub type StrToCallbackNamespace<'a> = BTreeMap<&'static str, Box<dyn Fn(Vec<f64>) -> f64 + 'a>>;
impl EvalNamespace for StrToCallbackNamespace<'_> {
    #[inline]
    fn lookup(&self, name: &str, args: Vec<f64>) -> Option<f64> {
        if let Some(f) = self.get(name) {
            Some(f(args))
        } else {
            None
        }
    }
}

/// Type alias for `Vec<BTreeMap<String,f64>>`
pub type LayeredStringToF64Namespace = Vec<BTreeMap<String, f64>>;
impl EvalNamespace for LayeredStringToF64Namespace {
    #[inline]
    fn lookup(&self, name: &str, args: Vec<f64>) -> Option<f64> {
        for map in self.iter().rev() {
            if let Some(&val) = map.get(name) {
                return Some(val);
            }
        }
        None
    }
}

// I'm not making a type alias for this because of the un-name-ability of closures:
impl<F> EvalNamespace for F
where
    F: Fn(&str, Vec<f64>) -> Option<f64>,
{
    #[inline(always)]
    fn lookup(&self, name: &str, args: Vec<f64>) -> Option<f64> {
        self(name, args)
    }
}

impl EvalNamespace for EmptyNamespace {
    /// Always returns `None`, indicating that the variable is undefined.
    #[inline]
    fn lookup(&self, _name: &str, _args: Vec<f64>) -> Option<f64> {
        None
    }
}
