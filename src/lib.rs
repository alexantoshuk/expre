//! Fast evaluation of algebraic expressions
//!
//! # Features
//! * No dependencies.
//! * Safe execution of untrusted expressions.
//! * Works with stable Rust.
//! * Supports interpretation (i.e. parse & eval) as well as compiled execution (i.e. parse, compile, eval).
//! * Supports Variables and Custom Functions.
//! * `expre` is a good base for building higher-level languages.
//! * Supports many built-in functions and constants.
//! * Supports all the standard algebraic unary and binary operators (+ - * / ^ %),
//!   as well as comparisons (< <= == != >= >) and logical operators (&& ||) with
//!   short-circuit support.
//! * Easy integration into many different types of applications, including scoped evaluation.
//! * Very fast performance.
//!
//! # The `expre` Expression "Mini-Language"
//!
//! ## Built-in Functions and Constants
//!
//! These are the built-in functions that `expre` expressions support.  (You
//! can also add your own custom functions and variables -- see the
//! [Examples](#advanced-variables-and-custom-functions) section.)
//!
//! ```text
//!   * print(...strings and values...) -- Prints to stderr.  Very useful to 'probe' an expression.
//!                                        Evaluates to the last value.
//!                                        Example: `print("x is", x, "and y is", y)`
//!                                        Example: `x + print("y:", y) + z == x+y+z`
//!
//!   * log(base=10, val) -- Logarithm with optional 'base' as first argument.
//!                          If not provided, 'base' defaults to '10'.
//!                          Example: `log(100) + log(e(), 100)`
//!
//!   * e()  -- Euler's number (2.718281828459045)
//!   * pi() -- π (3.141592653589793)
//!
//!   * int(val)
//!   * ceil(val)
//!   * floor(val)
//!   * round(modulus=1, val) -- Round with optional 'modulus' as first argument.
//!                              Example: `round(1.23456) == 1  &&  round(0.001, 1.23456) == 1.235`
//!
//!   * abs(val)
//!   * sign(val)
//!
//!   * min(val, ...) -- Example: `min(1, -2, 3, -4) == -4`
//!   * max(val, ...) -- Example: `max(1, -2, 3, -4) == 3`
//!
//!   * sin(radians)    * asin(val)
//!   * cos(radians)    * acos(val)
//!   * tan(radians)    * atan(val)
//!   * sinh(val)       * asinh(val)
//!   * cosh(val)       * acosh(val)
//!   * tanh(val)       * atanh(val)
//! ```
//!
//! ## Operators
//!
//! The `and` and `or` operators are enabled by default, but if your
//! application wants to use those words for something else, they can be
//! disabled by turning off the `alpha-keywords` feature (`cargo build --no-default-features`).
//!
//! ```text
//! Listed in order of precedence:
//!
//!     (Highest Precedence) ^               Exponentiation
//!                          %               Modulo
//!                          /               Division
//!                          *               Multiplication
//!                          -               Subtraction
//!                          +               Addition
//!                          == != < <= >= > Comparisons (all have equal precedence)
//!                          && and          Logical AND with short-circuit
//!     (Lowest Precedence)  || or           Logical OR with short-circuit
//!
//! ```
//!
//! ## Numeric Literals
//!
//! ```text
//! Several numeric formats are supported:
//!
//!     Integers: 1, 2, 10, 100, 1001
//!
//!     Decimals: 1.0, 1.23456, 0.000001
//!
//!     Exponents: 1e3, 1E3, 1e-3, 1E-3, 1.2345e100
//!
//!     Suffix:
//!             1.23p        = 0.00000000000123
//!             1.23n        = 0.00000000123
//!             1.23µ, 1.23u = 0.00000123
//!             1.23m        = 0.00123
//!             1.23K, 1.23k = 1230
//!             1.23M        = 1230000
//!             1.23G        = 1230000000
//!             1.23T        = 1230000000000
//! ```
//!
//! # Examples
//!
//! ## Easy evaluation
//! The [`eval()`](ez/fn.eval.html) function performs the entire allocation-parse-eval process
//! for you.  It is slightly inefficient because it always allocates a
//! fresh [`Ast`](slab/index.html), but it is very simple to use:
//!
//! ```
//! // In case you didn't know, Rust allows `main()` to return a `Result`.
//! // This lets us use the `?` operator inside of `main()`.  Very convenient!
//! fn main() -> Result<(), expre::Error> {
//!     // This example doesn't use any variables, so just use an EmptyNamespace:
//!     let mut ctx = expre::EmptyNamespace;
//!
//!     let val = expre::eval(
//!         "1+2*3/4^5%6 + log(100K) + log(e(),100) + [3*(3-3)/3] + (2<3) && 1.23",    &mut ctx)?;
//!     //    |            |      |    |   |          |               |   |
//!     //    |            |      |    |   |          |               |   boolean logic with short-circuit support
//!     //    |            |      |    |   |          |               comparisons
//!     //    |            |      |    |   |          square-brackets act like parenthesis
//!     //    |            |      |    |   built-in constants: e(), pi()
//!     //    |            |      |    'log' can take an optional first 'base' argument, defaults to 10
//!     //    |            |      numeric literal with suffix: p, n, µ, m, K, M, G, T
//!     //    |            many built-in functions: print, int, ceil, floor, abs, sign, log, round, min, max, sin, asin, ...
//!     //    standard binary operators
//!
//!     assert_eq!(val, 1.23);
//!
//!     Ok(())
//! }
//! ```
//!
//!
//! ## Simple variables
//! Several namespace types are supported, each designed for different situations.
//! ([See the various Namespace types here.](evalns/index.html))  For simple cases, you can define variables with a
//! [`BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html):
//!
//! ```
//! use std::collections::BTreeMap;
//! fn main() -> Result<(), expre::Error> {
//!     let mut map : BTreeMap<String,f64> = BTreeMap::new();
//!     map.insert("x".to_string(), 1.0);
//!     map.insert("y".to_string(), 2.0);
//!     map.insert("z".to_string(), 3.0);
//!
//!     let val = expre::eval(r#"x + print("y:",y) + z"#,    &mut map)?;
//!     //                                 |
//!     //                                 prints "y: 2" to stderr and then evaluates to 2.0
//!
//!     assert_eq!(val, 6.0);
//!
//!     Ok(())
//! }
//! ```
//!
//! ## Advanced variables and custom functions
//! This time, instead of using a map, we will use a callback function,
//! which defines custom variables, functions, and array-like objects:
//!
//! ```
//! fn main() -> Result<(), expre::Error> {
//!     let mut cb = |name:&str, args:Vec<f64>| -> Option<f64> {
//!         let mydata : [f64; 3] = [11.1, 22.2, 33.3];
//!         match name {
//!             // Custom constants/variables:
//!             "x" => Some(3.0),
//!             "y" => Some(4.0),
//!
//!             // Custom function:
//!             "sum" => Some(args.into_iter().sum()),
//!
//!             // Custom array-like objects:
//!             // The `args.get...` code is the same as:
//!             //     mydata[args[0] as usize]
//!             // ...but it won't panic if either index is out-of-bounds.
//!             "data" => args.get(0).and_then(|f| mydata.get(*f as usize).copied()),
//!
//!             // A wildcard to handle all undefined names:
//!             _ => None,
//!         }
//!     };
//!
//!     let val = expre::eval("sum(x^2, y^2)^0.5 + data[0]",    &mut cb)?;
//!     //                           |   |                   |
//!     //                           |   |                   square-brackets act like parenthesis
//!     //                           |   variables are like custom functions with zero args
//!     //                           custom function
//!
//!     assert_eq!(val, 16.1);
//!
//!     // Let's explore some of the hidden complexities of variables:
//!     //
//!     //     * There's really no difference between a variable and a custom function.
//!     //       Therefore, variables can receive arguments too,
//!     //       which will probably be ignored.
//!     //       Therefore, these two expressions evaluate to the same thing:
//!     //           eval("x + y")  ==  eval("x(1,2,3) + y(x, y, sum(x,y))")
//!     //                                      ^^^^^      ^^^^^^^^^^^^^^
//!     //                                      All this stuff is ignored.
//!     //
//!     //     * Built-in functions take precedence WHEN CALLED AS FUNCTIONS.
//!     //       This design was chosen so that builtin functions do not pollute
//!     //       the variable namespace, which is important for some applications.
//!     //       Here are some examples:
//!     //           pi        -- Uses the custom 'pi' variable, NOT the builtin 'pi' function.  
//!     //           pi()      -- Uses the builtin 'pi' function even if a custom variable is defined.
//!     //           pi(1,2,3) -- Uses the builtin 'pi' function, and produces a WrongArgs error
//!     //                        during parse because the builtin does not expect any arguments.
//!     //           x         -- Uses the custom 'x' variable.
//!     //           x()       -- Uses the custom 'x' variable because there is no 'x' builtin.
//!     //           x(1,2,3)  -- Uses the custom 'x' variable.  The args are ignored.
//!     //           sum       -- Uses the custom 'sum' function with no arguments.
//!     //           sum()     -- Uses the custom 'sum' function with no arguments.
//!     //           sum(1,2)  -- Uses the custom 'sum' function with two arguments.
//!
//!     Ok(())
//! }
//! ```
//!
//! ## Re-use the Ast to go faster
//! If we perform the parse and eval ourselves (without relying on the 'ez'
//! interface), then we can re-use the [`Ast`](slab/index.html) allocation for
//! subsequent parsing and evaluations.  This avoids a significant amount of
//! slow memory operations:
//!
//! TODO!
//!
//! ## Compile to go super fast!
//! If you plan to evaluate an expression just one or two times, then you
//! should parse-eval as shown in previous examples.  But if you expect to
//! evaluate an expression three or more times, you can dramatically improve
//! your performance by compiling.  The compiled form is usually more than 10
//! times faster than the un-compiled form, and for constant expressions it is
//! usually more than 200 times faster.
//! ```
//! use std::collections::BTreeMap;
//! use expre::*;    // use this trait so we can call eval().
//! fn main() -> Result<(), expre::Error> {
//!     let mut ast = expre::Ast::new();
//!     let mut cexpr = expre::CExpr::new();
//!     let mut map = BTreeMap::new();
//!
//!     let expr_str = "sin(deg/360 * 2*pi())";
//!     expr_str.parse_expr( &mut ast)?;
//!     ast.compile( &mut cexpr);
//!     for deg in 0..360 {
//!         map.insert("deg".to_string(), deg as f64);
//!         // When working with compiled constant expressions, you can use the
//!         // eval_compiled*!() macros to save a function call:
//!         let val = cexpr.eval(&mut map)?;
//!         eprintln!("sin({}°) = {}", deg, val);
//!     }
//!
//!     Ok(())
//! }
//! ```
//!
//!
//! ## Let's Develop an Intuition of `expre` Internals
//! In this advanced example, we peek into the Ast to see how expressions are
//! represented after the 'parse' and 'compile' phases.
//! ```
//! use expre::*;  // use this trait so we can call compile().
//! fn main() -> Result<(), expre::Error> {
//!     let mut ast = expre::Ast::new();
//!     let mut cexpr = expre::CExpr::new();
//!
//!     let expr_str = "sin(deg/360 * 2*pi())";
//!     expr_str.parse_expr(&mut ast)?;
//!
//!     // Let's take a look at the parsed Ast:
//!     // If you find this structure confusing, take a look at the compilation
//!     // CExpr below because it is simpler.
//!     assert_eq!(format!("{:?}", ast),
//!                r#"Ast { exprs: { 0:Expr(EStdFunc(EVar("deg")), [ExprPair(EDiv, EConst(360.0)), ExprPair(EMul, EConst(2.0)), ExprPair(EMul, EStdFunc(EFuncPi))]), 1:Expr(EStdFunc(EFuncSin(0)), []) } }"#);
//!                // Pretty-Print:
//!                // ParseSlab{
//!                //     exprs:{
//!                //         0:Expr(EStdFunc(EVar("deg")),
//!                //                      [ExprPair(EDiv, EConstant(360.0)),
//!                //                                ExprPair(EMul, EConstant(2.0)),
//!                //                                ExprPair(EMul, EStdFunc(EFuncPi))]
//!                //                      ),
//!                //         1:Expr(EStdFunc(EFuncSin(ExpressionI(0))),
//!                //                      [] )
//!                //     },
//!                // }
//!
//!     ast.compile( &mut cexpr);
//!
//!     // Let's take a look at the compilation results and the Ast inside the Ast:
//!     // Notice that compilation has performed constant-folding: 1/360 * 2*pi = 0.017453292519943295
//!     // In the results below: IFuncSin(...) represents the sin function.
//!     //                       InstructionI(1) represents the Instruction stored at index 1.
//!     //                       IMul(...) represents the multiplication operator.
//!     //                       'C(0.017...)' represents a constant value of 0.017... .
//!     //                       IVar("deg") represents a variable named "deg".
//!     assert_eq!(format!("{:?}", cexpr.last().unwrap()),
//!                "IFuncSin(1)");
//!     assert_eq!(format!("{:?}", cexpr),
//!                r#"CExpr { 0:IVar("deg"), 1:IMul(0, IConst(0.017453292519943295)), 2:IFuncSin(1) }"#);
//!
//!     Ok(())
//! }
//! ```
//!
//! # Safety
//!
//! `expre` is designed to evaluate untrusted expressions safely.  By
//! default, an expression can only perform math operations; there is no way
//! for it to access other types of operations (like network or filesystem or
//! external commands).  Additionally, we guard against malicious expressions:
//!
//! * Expressions that are too large (greater than 4KB).
//! * Expressions that are too-deeply nested (greater than 32 levels).
//! * Expressions with too many values (greater than 64).
//! * Expressions with too many sub-expressions (greater than 64).
//!
//! All limits can be customized at parse time.  If any limits are exceeded,
//! [`parse()`](https://docs.rs/expre/latest/expre/parser/struct.Parser.html#method.parse) will return an
//! [Error](https://docs.rs/expre/latest/expre/error/enum.Error.html).
//!
//! Note that it *is* possible for you (the developer) to define custom functions
//! which might perform dangerous operations.  It is your responsibility to make
//! sure that all custom functionality is safe.
//!
//!
//! # Performance Benchmarks
//!
//! These benchmarks were performed on 2019-12-25.  Merry Christmas.
//!
//! Here are links to all the libraries/tools included in these benchmarks:
//!
//! * [expre (this library)](https://github.com/likebike/expre)
//! * [caldyn](https://github.com/Luthaf/caldyn)
//! * [rsc](https://github.com/codemessiah/rsc)
//! * [meval](https://github.com/rekka/meval-rs)
//! * [calc](https://github.com/redox-os/calc)
//! * [tinyexpr (Rust)](https://github.com/kondrak/tinyexpr-rs)
//! * [tinyexpr (C)](https://github.com/codeplea/tinyexpr)
//! * [bc](https://www.gnu.org/software/bc/)
//! * [python3](https://www.python.org/)
//!
//! ## Charts
//! Note that the following charts use logarithmic scales.  Therefore, tiny
//! visual differences actually represent very significant performance
//! differences.
//!
//! **Performance of evaluation of a compiled expression:**  
//! ![Compiled Eval Performance](https://raw.githubusercontent.com/likebike/expre/master/benches/results/20191225/expre-compiled.png)
//!
//! **Performance of one-time interpretation (parse and eval):**  
//! ![Interpretation Performance](https://raw.githubusercontent.com/likebike/expre/master/benches/results/20191225/expre-interp.png)
//!
//! **Performance of compiled Unsafe Variables, compared to the tinyexpr C library (the
//! only other library in our test set that supports this mode):**  
//! ![Unsafe Compiled Eval Performance](https://raw.githubusercontent.com/likebike/expre/master/benches/results/20191225/expre-compiled-unsafe.png)
//!
//! **Performance of interpreted Unsafe Variables, compared to the tinyexpr C library (the
//! only other library in our test set that supports this mode):**  
//! ![Unsafe Interpretation Performance](https://raw.githubusercontent.com/likebike/expre/master/benches/results/20191225/expre-interp-unsafe.png)
//!
//! ## Summary
//!
//! The impressive thing about these results is that `expre` consistently
//! achieves the fastest times across every benchmark and in every mode of
//! operation (interpreted, compiled, and unsafe).  It's easy to create a
//! design to claim the #1 spot in any one of these metrics by sacrificing
//! performance in another, but it is difficult to create a design that can be
//! #1 across-the-board.
//!
//! Because of the broad and robust performance advantages, `expre` is very
//! likely to be an excellent choice for your dynamic evaluation needs.
//!
//! ## Benchmark Descriptions & Analysis
//! ```text
//!     * simple = `3 * 3 - 3 / 3`
//!       This is a simple test with primitive binary operators.
//!       Since the expression is quite simple, it does a good job of showing
//!       the intrinsic performance costs of a library.
//!       Results:
//!           * For compiled expressions, `expre` is 6x as fast as the closest
//!             competitor (caldyn) because the `eval_compiled!()` macro is able to
//!             eliminate all function calls.  If the macro is not used and a
//!             normal `expr.eval()` function call is performed instead, then
//!             performance is very similar to caldyn's.
//!           * For interpreted expressions, `expre` is 2x as fast as the
//!             tinyexpr C lib, and 3x as fast as the tinyexpr Rust lib.
//!             This is because `expre` eliminates redundant work and memory
//!             allocation during the parse phase.
//!
//!     * power = `2 ^ 3 ^ 4`
//!               `2 ^ (3 ^ 4)` for `tinyexpr` and `rsc`
//!       This test shows the associativity of the exponent operator.
//!       Most libraries (including `expre`) use right-associativity,
//!       but some libraries (particularly tinyexpr and rsc) use
//!       left-associativity.
//!       This test is also interesting because it shows the precision of a
//!       library's number system.  `expre` just uses f64 and therefore truncates
//!       the result (2417851639229258300000000), while python, bc, and the
//!       tinyexpr C library produce a higher precision result
//!       (2417851639229258349412352).
//!       Results:
//!           Same as the 'simple' case.
//!
//!     * variable = `x * 2`
//!       This is a simple test of variable support.
//!       Since the expression is quite simple, it shows the intrinsic
//!       performance costs of a library's variables.
//!       Results:
//!           * The tinyexpr Rust library does not currently support variables.
//!           * For safe compiled evaluation, `expre` is 4.4x as fast as the closest
//!             competitor (caldyn).
//!           * For safe interpretation, `expre` is 3.3x as fast as the closest
//!             competitor (caldyn).
//!           * For unsafe variables, `expre` is 1.2x as fast as the
//!             tinyexpr C library.
//!
//!     * trig = `sin(x)`
//!       This is a test of variables, built-in function calls, and trigonometry.
//!       Results:
//!           * The tinyexpr Rust library does not currently support variables.
//!           * The `calc` library does not support trigonometry.
//!           * For safe compiled evaluation, `expre` is 2.6x as fast as the
//!             closest competitor (caldyn).
//!           * For safe interpretation, `expre` is 2.3x as fast as the closest
//!             competitor (caldyn).
//!           * Comparing unsafe variables with the tinyexpr C library,
//!             `expre` is 8% slower for compiled expressions (tinyexpr uses a
//!             faster `sin` implementation) and 4% faster for interpreted
//!             expressions (`expre` performs less memory allocation).
//!
//!     * quadratic = `(-z + (z^2 - 4*x*y)^0.5) / (2*x)`
//!       This test demonstrates a more complex expression, involving several
//!       variables, some of which are accessed more than once.
//!       Results:
//!           * The tinyexpr Rust library does not currently support variables.
//!           * For safe compiled evaluation, `expre` is 2x as fast as the
//!             closest competitor (rsc).
//!           * For safe interpretation, `expre` is 3.7x as fast as the
//!             closest competitor (caldyn).
//!           * Comparing unsafe variables with the tinyexpr C library,
//!             `expre` is the same speed for compiled expressions,
//!             and 1.2x as fast for interpretation.
//!
//!     * large = `((((87))) - 73) + (97 + (((15 / 55 * ((31)) + 35))) + (15 - (9)) - (39 / 26) / 20 / 91 + 27 / (33 * 26 + 28 - (7) / 10 + 66 * 6) + 60 / 35 - ((29) - (69) / 44 / (92)) / (89) + 2 + 87 / 47 * ((2)) * 83 / 98 * 42 / (((67)) * ((97))) / (34 / 89 + 77) - 29 + 70 * (20)) + ((((((92))) + 23 * (98) / (95) + (((99) * (41))) + (5 + 41) + 10) - (36) / (6 + 80 * 52 + (90))))`
//!       This is a fairly large expression that highlights parsing costs.
//!       Results:
//!           * Since there are no variables in the expression, `expre` and
//!             `caldyn` compile this down to a single constant value.  That's
//!             why these two libraries are so much faster than the rest.
//!           * For compiled evaluation, `expre` is 6x as fast as `caldyn`
//!             because it is able to eliminate function calls with the
//!             `eval_compiled!()` macro.
//!           * For interpretation, `expre` is 2x as fast as the closest
//!             competitor (rsc).
//!           * Comparing unsafe variables with the tinyexpr C library,
//!             `expre` is 3x as fast for compiled evaluation, and
//!             1.2x as fast for interpretation.
//! ```
//!
//! ## Methodology
//! I am running Ubuntu 18.04 on an Asus G55V (a 2012 laptop with Intel Core i7-3610QM CPU @ 2.3GHz - 3.3GHz).
//!
//! All numeric results can be found in `expre/benches/bench.rs`.
//!
//! See the [detailed post about my benchmarking methology]{http://likebike.com/posts/How_To_Write_Fast_Rust_Code.html#how-to-measure}
//! on my blog.

//#![warn(missing_docs)]
pub mod builtins;
pub mod compiler;
pub mod context;
pub mod error;
pub mod evaler;
pub mod module;
pub mod parser;
pub use self::compiler::*;
pub use self::context::*;
pub use self::error::Error;
pub use self::evaler::*;

pub use self::parser::{parse, Ast, ParseExpr};
use std::fmt;

fn write_indexed_list<T>(f: &mut fmt::Formatter, lst: &[T]) -> Result<(), fmt::Error>
where
    T: fmt::Debug,
{
    let sep = '\n';
    let ident = "  ";
    let mut nonempty = false;
    for (i, x) in lst.iter().enumerate() {
        if nonempty {
            write!(f, ",")?;
        }
        nonempty = true;
        write!(f, "{}{}{}:\t{:?}", sep, ident, i, x)?;
    }
    if nonempty {
        write!(f, "{}", sep)?;
    }

    Ok(())
}

/// The `eval()` function provides a very simple way to perform expression evaluation with just one function call.
///
/// If you only need to evaluate an expression one time, then `eval()` will
/// probably be perfectly adequate.  But if you plan to evaluate the same
/// expression many times, or if you plan to evaluate many expressions, you
/// are able to achieve better performance by allocating a single `Ast` and
/// using it to perform multiple parse-compile-eval cycles yourself.
///
/// # Errors
///
/// If there are any [`Error`](../error/enum.Error.html)s during the parse-eval process, they will be returned.
///
/// # Examples
///
/// [See the `expre` top-level documentation for examples.](../index.html#easy-evaluation)
pub fn eval(expr_str: &str, ctx: &impl Context) -> Result<f64, Error> {
    CExpr::from_str(expr_str)?.eval(ctx)
}

pub fn eval2(
    expr_str: &str,
    ast: &mut Ast,
    cexpr: &mut CExpr,
    ctx: &impl Context,
) -> Result<f64, Error> {
    expr_str.parse_expr(ast)?;
    ast.compile(cexpr);
    cexpr.eval(ctx)
}
