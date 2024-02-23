//! Evaluation Namespaces used for Variable-lookups and custom Functions.
//!
//! Several Evaluation Namespace types are defined, each with their own advantages:
//! * [`EmptyNamespace`](#emptynamespace) -- Useful when you know that your
//!   expressions don't need to look up any variables.
//! * BTreeMap -- A simple way to define variables and functions with a map.
//!   Type aliases: [StringToF64Namespace](#stringtof64namespace),
//!   [StrToF64Namespace](#strtof64namespace),
//!   [StringToCallbackNamespace](#stringtocallbacknamespace),
//!   [StrToCallbackNamespace](#strtocallbacknamespace)
//! * [`FnMut(&str,Vec<f64>) -> Option<f64>`](#callback-fnmutstrvec---option) --
//!   Define variables and custom functions using a callback function.
//! * [`CachedCallbackNamespace`](#cachedcallbacknamespace) -- Like the above
//!   callback-based Namespace, but results are cached so the callback is not
//!   queried more than once for a given variable.
//! * Vec<BTreeMap<String,f64>> -- Define variables with layered maps.
//!   Each layer is a separate 'scope'.  Higher layers take precedence
//!   over lower layers.  Very useful for creating scoped higher-level-languages.
//!   Type alias: [LayeredStringToF64Namespace](#layeredstringtof64namespace)
//!
//! # Examples
//!
//! ## EmptyNamespace
//! ```
//! fn main() -> Result<(), expre::Error> {
//!     let mut ns = expre::EmptyNamespace;
//!
//!     let val = expre::eval("sin(pi()/2)", &mut ns)?;
//!     assert_eq!(val, 1.0);
//!
//!     Ok(())
//! }
//! ```
//!
//! ## StringToF64Namespace
//! ```
//! fn main() -> Result<(), expre::Error> {
//!     let mut ns = expre::StringToF64Namespace::new();
//!     ns.insert("x".to_string(), 2.0);
//!
//!     let val = expre::eval("x * (x + 1)", &mut ns)?;
//!     assert_eq!(val, 6.0);
//!
//!     Ok(())
//! }
//! ```
//!
//! ## StrToF64Namespace
//! ```
//! fn main() -> Result<(), expre::Error> {
//!     let mut ns = expre::StrToF64Namespace::new();
//!     ns.insert("x", 2.0);
//!
//!     let val = expre::eval("x * (x + 1)", &mut ns)?;
//!     assert_eq!(val, 6.0);
//!
//!     Ok(())
//! }
//! ```
//!
//! ## Callback: FnMut(&str,Vec<f64>) -> Option<f64>
//! ```
//! fn main() -> Result<(), expre::Error> {
//!     let mut num_lookups = 0;
//!     let mut cb = |name:&str, args:Vec<f64>| -> Option<f64> {
//!         num_lookups += 1;
//!         match name {
//!             "x" => Some(2.0),
//!             _ => None,
//!         }
//!     };
//!
//!     let val = expre::eval("x * (x + 1)", &mut cb)?;
//!     assert_eq!(val, 6.0);
//!     assert_eq!(num_lookups, 2);  // Notice that 'x' was looked-up twice.
//!
//!     Ok(())
//! }
//! ```
//!
//! ## StringToCallbackNamespace
//! ```
//! fn main() -> Result<(), expre::Error> {
//!     let mut ns = expre::StringToCallbackNamespace::new();
//!     ns.insert("x".to_string(), Box::new(|_args| 2.0));
//!     ns.insert("double".to_string(), Box::new(|args| {
//!         args.get(0).map(|arg0| arg0*2.0).unwrap_or(std::f64::NAN)
//!     }));
//!
//!     let val = expre::eval("double(x + 1) + 1", &mut ns)?;
//!     assert_eq!(val, 7.0);
//!
//!     Ok(())
//! }
//! ```
//!
//! ## StrToCallbackNamespace
//! ```
//! fn main() -> Result<(), expre::Error> {
//!     let mut ns = expre::StrToCallbackNamespace::new();
//!     ns.insert("x", Box::new(|_args| 2.0));
//!     ns.insert("double", Box::new(|args| {
//!         args.get(0).map(|arg0| arg0*2.0).unwrap_or(std::f64::NAN)
//!     }));
//!
//!     let val = expre::eval("double(x + 1) + 1", &mut ns)?;
//!     assert_eq!(val, 7.0);
//!
//!     Ok(())
//! }
//! ```
//!
//! ## CachedCallbackNamespace
//! ```
//! fn main() -> Result<(), expre::Error> {
//!     let mut num_lookups = 0;
//!     let val = {
//!         let cb = |name:&str, args:Vec<f64>| -> Option<f64> {
//!             num_lookups += 1;
//!             match name {
//!                 "x" => {
//!                     // Pretend that it is very expensive to calculate this,
//!                     // and that's why we want to use the CachedCallbackNamespace cache.
//!                     for i in 0..1000000 { /* do work */ }  // Fake Work for this example.
//!                     Some(2.0)
//!                 }
//!                 _ => None,
//!             }
//!         };
//!         let mut ns = expre::CachedCallbackNamespace::new(cb);
//!
//!         expre::eval("x * (x + 1)", &mut ns)?
//!     };
//!     assert_eq!(val, 6.0);
//!     assert_eq!(num_lookups, 1);  // Notice that only 1 lookup occurred.
//!                                  // The second 'x' value was cached.
//!
//!     Ok(())
//! }
//! ```
//!
//! ## LayeredStringToF64Namespace
//! ```
//! fn main() -> Result<(), expre::Error> {
//!     let mut layer1 = expre::StringToF64Namespace::new();
//!     layer1.insert("x".to_string(), 2.0);
//!     layer1.insert("y".to_string(), 3.0);
//!
//!     let mut layers : expre::LayeredStringToF64Namespace = vec![layer1];
//!
//!     let val = expre::eval("x * y", &mut layers)?;
//!     assert_eq!(val, 6.0);
//!
//!     // Let's add another layer which shadows the previous one:
//!     let mut layer2 = expre::StringToF64Namespace::new();
//!     layer2.insert("x".to_string(), 3.0);
//!     layers.push(layer2);
//!
//!     let val = expre::eval("x * y", &mut layers)?;
//!     assert_eq!(val, 9.0);
//!
//!     // Remove the top layer and we'll be back to what we had before:
//!     layers.pop();
//!
//!     let val = expre::eval("x * y", &mut layers)?;
//!     assert_eq!(val, 6.0);
//!
//!     Ok(())
//! }
//! ```
//!
//! ## Custom Namespace Types
//!
//! If the pre-defined Namespace types aren't perfect for your application, you
//! can create your own namespace type -- just implemenet the `EvalNamespace`
//! trait (and maybe the `Cached` and `Layered` traits too).  Also, as
//! `expre` becomes more mature and is used for more real-life things, I
//! will continue to add more useful Namespace types.
//!
//! Here are a few ideas of possibly-useful custom Namespace types:
//!
//! * Vec<Fn(&str,Vec<f64>)->Option<f64>>  --  This would be a `Layered`
//!   namespace, with each layer having its own callback.  Really powerful!
//!
//! * CachedCallbacksNamespace  --  Same as above, but with a cache for each
//!   layer.  Good for expensive look-ups.

use crate::error::Error;

use std::collections::BTreeMap;

//---- Types:

/// All `expre` Namespaces must implement the `EvalNamespace` trait.
pub trait EvalNamespace {
    /// Perform a variable/function lookup.
    ///
    /// May return cached values.
    fn lookup(&mut self, name: &str, args: Vec<f64>) -> Option<f64>;
}

/// Cache operations for `EvalNamespace`s.
///
/// Implement this trait if your Namespace type uses a cache.
pub trait Cached {
    /// Creates a new cached entry.  If an entry with the same name already
    /// exists, an [`AlreadyExists` Error](../error/enum.Error.html#variant.AlreadyExists) is returned.
    fn cache_create(&mut self, name: String, val: f64) -> Result<(), Error>;

    /// Sets a cached entry.  It doesn't matter whether or not a previous value
    /// existed with this name.
    fn cache_set(&mut self, name: String, val: f64);

    /// Clear all cached entries.  Values will be recalculated and cached
    /// again the next time they are looked up.
    fn cache_clear(&mut self);
}

//// I don't want to put this into the public API until it is needed.
// pub trait Layered {
//     fn push(&mut self);
//     fn pop(&mut self);
// }

/// Use `EmptyNamespace` when you know that you won't be looking up any variables.
///
/// It is a zero-sized type, which means it gets optimized-away at compile time.
///
/// [See module-level documentation for example.](index.html#emptynamespace)
///
pub struct EmptyNamespace;

/// `CachedCallbackNamespace` is useful when your variable/function lookups are expensive.
///
/// Each variable+args combo will only be looked up once, and then it will be
/// cached and re-used for subsequent lookups.
///
/// [See module-level documentation for example.](index.html#cachedcallbacknamespace)
///
pub struct CachedCallbackNamespace<'a> {
    cache: BTreeMap<String, f64>,
    cb: Box<dyn FnMut(&str, Vec<f64>) -> Option<f64> + 'a>, // I think a reference would be more efficient than a Box, but then I would need to use a funky 'let cb=|n|{}; Namespace::new(&cb)' syntax.  The Box results in a super convenient pass-the-cb-by-value API interface.
}

/// Type alias for `BTreeMap<String,f64>`
pub type StringToF64Namespace = BTreeMap<String, f64>;
impl EvalNamespace for StringToF64Namespace {
    #[inline]
    fn lookup(&mut self, name: &str, args: Vec<f64>) -> Option<f64> {
        self.get(name).copied()
    }
}

/// Type alias for `BTreeMap<&'static str,f64>`
pub type StrToF64Namespace = BTreeMap<&'static str, f64>;
impl EvalNamespace for StrToF64Namespace {
    #[inline]
    fn lookup(&mut self, name: &str, args: Vec<f64>) -> Option<f64> {
        self.get(name).copied()
    }
}

/// Type alias for `BTreeMap<String, Box<dyn FnMut(Vec<f64>)->f64>>`
///
/// This namespace type provides a very convenient way to register variables
/// and custom functions.  It is a bit slower than a pure callback, but it has
/// isolation and composition advantages.
pub type StringToCallbackNamespace<'a> = BTreeMap<String, Box<dyn FnMut(Vec<f64>) -> f64 + 'a>>;
impl EvalNamespace for StringToCallbackNamespace<'_> {
    #[inline]
    fn lookup(&mut self, name: &str, args: Vec<f64>) -> Option<f64> {
        if let Some(f) = self.get_mut(name) {
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
pub type StrToCallbackNamespace<'a> = BTreeMap<&'static str, Box<dyn FnMut(Vec<f64>) -> f64 + 'a>>;
impl EvalNamespace for StrToCallbackNamespace<'_> {
    #[inline]
    fn lookup(&mut self, name: &str, args: Vec<f64>) -> Option<f64> {
        if let Some(f) = self.get_mut(name) {
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
    fn lookup(&mut self, name: &str, args: Vec<f64>) -> Option<f64> {
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
    F: FnMut(&str, Vec<f64>) -> Option<f64>,
{
    #[inline(always)]
    fn lookup(&mut self, name: &str, args: Vec<f64>) -> Option<f64> {
        self(name, args)
    }
}

impl EvalNamespace for EmptyNamespace {
    /// Always returns `None`, indicating that the variable is undefined.
    #[inline]
    fn lookup(&mut self, _name: &str, _args: Vec<f64>) -> Option<f64> {
        None
    }
}

impl EvalNamespace for CachedCallbackNamespace<'_> {
    /// Returns a cached value if possible, otherwise delegates to the callback function.
    fn lookup(&mut self, name: &str, args: Vec<f64>) -> Option<f64> {
        if let Some(&val) = self.cache.get(name) {
            return Some(val);
        }

        match (self.cb)(name, args) {
            Some(val) => {
                self.cache.insert(name.to_string(), val);
                Some(val)
            }
            None => None,
        }
    }
}

impl Cached for CachedCallbackNamespace<'_> {
    fn cache_create(&mut self, name: String, val: f64) -> Result<(), Error> {
        if self.cache.contains_key(&name) {
            return Err(Error::AlreadyExists);
        }
        self.cache.insert(name, val);
        Ok(())
    }
    fn cache_set(&mut self, name: String, val: f64) {
        self.cache.insert(name, val);
    }
    fn cache_clear(&mut self) {
        self.cache = BTreeMap::new();
    }
}

impl<'a> CachedCallbackNamespace<'a> {
    #[inline]
    pub fn new<F>(cb: F) -> Self
    where
        F: FnMut(&str, Vec<f64>) -> Option<f64> + 'a,
    {
        CachedCallbackNamespace {
            cache: BTreeMap::new(),
            cb: Box::new(cb),
        }
    }
}
