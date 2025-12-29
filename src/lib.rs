/// A complete Lisp interpreter implemented entirely in Rust macro_rules!
///
/// File structure:
/// - src/main.rs or src/lib.rs (this file) - Compile-time macro interpreter
/// - examples/repl.rs - Interactive runtime REPL
///
/// Run the REPL with: cargo run --example repl
///
/// Supports:
/// - Arithmetic: (+ 1 2), (- 5 3), (* 2 3), (/ 10 2)
/// - Comparisons: (< 1 2), (> 3 1), (== 1 1)
/// - Logic: (and true false), (or true false), (not true)
/// - Conditionals: (if condition then-expr else-expr)
/// - Let bindings: (let x 5 (+ x 1)) or (let ((x 5) (y 10)) (+ x y))
/// - Function application
/// - Lambdas: (lambda (x y) (+ x y))
/// - Recursion
/// - Lists: (list 1 2 3), (car list), (cdr list), (cons 1 list)
// Main entry point - evaluates a Lisp expression
#[macro_export]
macro_rules! lisp {
    // Numbers
    ($n:literal) => { $n };
    // Booleans
    (true) => { true };
    (false) => { false };
    // Nil/empty list
    (nil) => { () };
    // Arithmetic operations
    ((+ $($args:tt)*)) => {
        lisp!(@add $($args)*)
    };
    ((- $a:tt $b:tt)) => {
        lisp!($a) - lisp!($b)
    };
    ((* $($args:tt)*)) => {
        lisp!(@mul $($args)*)
    };
    ((/ $a:tt $b:tt)) => {
        lisp!($a) / lisp!($b)
    };
    ((% $a:tt $b:tt)) => {
        lisp!($a) % lisp!($b)
    };
    // Comparison operations
    ((< $a:tt $b:tt)) => {
        lisp!($a) < lisp!($b)
    };
    ((> $a:tt $b:tt)) => {
        lisp!($a) > lisp!($b)
    };
    ((<= $a:tt $b:tt)) => {
        lisp!($a) <= lisp!($b)
    };
    ((>= $a:tt $b:tt)) => {
        lisp!($a) >= lisp!($b)
    };
    ((== $a:tt $b:tt)) => {
        lisp!($a) == lisp!($b)
    };
    ((!= $a:tt $b:tt)) => {
        lisp!($a) != lisp!($b)
    };
    // Logical operations
    ((and $a:tt $b:tt)) => {
        lisp!($a) && lisp!($b)
    };
    ((or $a:tt $b:tt)) => {
        lisp!($a) || lisp!($b)
    };
    ((not $a:tt)) => {
        !lisp!($a)
    };
    // If expression
    ((if $cond:tt $then:tt $else:tt)) => {
        if lisp!($cond) {
            lisp!($then)
        } else {
            lisp!($else)
        }
    };
    // Multiple let bindings (recursive nesting)
    ((let () $body:tt)) => {
        lisp!($body)
    };
    ((let (($var:ident $val:tt) $($rest:tt)*) $body:tt)) => {
        lisp!((let $var $val (let ($($rest)*) $body)))
    };
    // Single let binding
    ((let $var:ident $val:tt $body:tt)) => {{
        let $var = lisp!($val);
        lisp!($body)
    }};
    // Lambda
    ((lambda ($($params:ident)*) $body:tt)) => {
        move |$($params: i64,)*| lisp!($body)
    };
    // Begin - evaluate multiple expressions, return last
    ((begin $($exprs:tt)*)) => {
        lisp!(@begin $($exprs)*)
    };
    // Print
    ((print $expr:tt)) => {{
        let val = lisp!($expr);
        println!("{:?}", val);
        val
    }};
    // List operations
    ((list $($items:tt)*)) => {
        vec![$(lisp!($items)),*]
    };
    ((car $list:tt)) => {{
        let list = lisp!($list);
        list[0].clone()
    }};
    ((cdr $list:tt)) => {{
        let list = lisp!($list);
        list[1..].to_vec()
    }};
    ((cons $item:tt $list:tt)) => {{
        let item = lisp!($item);
        let mut list = lisp!($list);
        let mut result = vec![item];
        result.extend(list);
        result
    }};
    ((length $list:tt)) => {{
        let list = lisp!($list);
        list.len()
    }};
    ((empty? $list:tt)) => {{
        let list = lisp!($list);
        list.is_empty()
    }};
    // Variable reference (just the identifier)
    ($var:ident) => { $var };
    // General function application (supports lambdas and function ids)
    (($op:tt $($args:tt)*)) => {
        (lisp!($op))($(lisp!($args)),*)
    };
    // Helper for addition (handles multiple arguments)
    (@add $first:tt $($rest:tt)*) => {
        lisp!($first) $(+ lisp!($rest))*
    };
    // Helper for multiplication (handles multiple arguments)
    (@mul $first:tt $($rest:tt)*) => {
        lisp!($first) $(* lisp!($rest))*
    };
    // Helper for begin
    (@begin $expr:tt) => {
        lisp!($expr)
    };
    (@begin $first:tt $($rest:tt)+) => {{
        lisp!($first);
        lisp!(@begin $($rest)+)
    }};
}
// Macro for defining Lisp functions - now accepts params without commas
#[macro_export]
macro_rules! defn {
    ($name:ident ($($params:ident)*) $body:tt) => {
        fn $name($($params: i64),*) -> i64 {
            lisp!($body)
        }
    };
}
#[macro_export]
macro_rules! defn_bool {
    ($name:ident ($($params:ident)*) $body:tt) => {
        fn $name($($params: i64),*) -> bool {
            lisp!($body)
        }
    };
}
#[macro_export]
macro_rules! defn_logic {
    ($name:ident ($($params:ident)*) $body:tt) => {
        fn $name($($params: bool),*) -> bool {
            lisp!($body)
        }
    };
}
// Macro for evaluating multiple Lisp expressions
#[macro_export]
macro_rules! lisp_program {
    ($($expr:tt)*) => {{
        $(lisp!($expr);)*
    }};
}
fn main() {
    println!("=== Macro Lisp Demo ===");
    println!("See examples/repl.rs for an interactive REPL!\n");
    // Basic arithmetic
    println!("Basic Arithmetic:");
    let result = lisp!((+ 1 2 3 4));
    println!("(+ 1 2 3 4) = {}", result);
    let result = lisp!((* 2 3 4));
    println!("(* 2 3 4) = {}", result);
    let result = lisp!((- 10 3));
    println!("(- 10 3) = {}", result);
    let result = lisp!((/ 20 4));
    println!("(/ 20 4) = {}", result);
    // Comparisons
    println!("\nComparisons:");
    let result = lisp!((< 5 10));
    println!("(< 5 10) = {}", result);
    let result = lisp!((> 5 10));
    println!("(> 5 10) = {}", result);
    let result = lisp!((== 5 5));
    println!("(== 5 5) = {}", result);
    // Logical operations
    println!("\nLogical Operations:");
    let result = lisp!((and true false));
    println!("(and true false) = {}", result);
    let result = lisp!((or true false));
    println!("(or true false) = {}", result);
    let result = lisp!((not false));
    println!("(not false) = {}", result);
    // Conditionals
    println!("\nConditionals:");
    let result = lisp!((if (< 5 10) 100 200));
    println!("(if (< 5 10) 100 200) = {}", result);
    let result = lisp!((if (> 5 10) 100 200));
    println!("(if (> 5 10) 100 200) = {}", result);
    // Let bindings
    println!("\nLet Bindings:");
    let result = lisp!((let x 5 (+ x 10)));
    println!("(let x 5 (+ x 10)) = {}", result);
    let result = lisp!((let ((x 3) (y 4)) (+ (* x x) (* y y))));
    println!("(let ((x 3) (y 4)) (+ (* x x) (* y y))) = {}", result);
    // Complex expressions
    println!("\nComplex Expressions:");
    let result = lisp!((let x 10 (if (> x 5) (* x 2) (+ x 1))));
    println!("(let x 10 (if (> x 5) (* x 2) (+ x 1))) = {}", result);
    // Nested arithmetic
    let result = lisp!((+ (* 2 3) (- 10 5) (/ 20 4)));
    println!("(+ (* 2 3) (- 10 5) (/ 20 4)) = {}", result);
    // Lists
    println!("\nList Operations:");
    let list = lisp!((list 1 2 3 4 5));
    println!("(list 1 2 3 4 5) = {:?}", list);
    let list = lisp!((list 10 20 30));
    let first = lisp!((car (list 10 20 30)));
    println!("(car (list 10 20 30)) = {}", first);
    let list = lisp!((list 10 20 30));
    let rest = lisp!((cdr (list 10 20 30)));
    println!("(cdr (list 10 20 30)) = {:?}", rest);
    let list = lisp!((cons 5 (list 10 20)));
    println!("(cons 5 (list 10 20)) = {:?}", list);
    let len = lisp!((length (list 1 2 3 4)));
    println!("(length (list 1 2 3 4)) = {}", len);
    // Begin (sequential evaluation)
    println!("\nBegin (Sequential Evaluation):");
    let result = lisp!((begin
        (print 10)
        (print 20)
        (+ 30 40)
    ));
    println!("Final result: {}", result);
    // Lambda examples
    println!("\nLambda Examples:");
    let result = lisp!(((lambda (x) (* x x)) 5));
    println!("((lambda (x) (* x x)) 5) = {}", result);
    let result = lisp!((let f (lambda (x y) (+ x y)) (f 10 20)));
    println!("(let f (lambda (x y) (+ x y)) (f 10 20)) = {}", result);
    // Function definition using defn!
    println!("\nFunction Definition:");
    defn!(square (x) (* x x));
    println!("square(5) = {}", square(5));
    defn!(add_three (x y z) (+ x y z));
    println!("add_three(1, 2, 3) = {}", add_three(1, 2, 3));
    // Factorial using recursion (defined as regular Rust function)
    fn factorial(n: i64) -> i64 {
        lisp!((if (<= n 1) 1 (* n (factorial (- n 1)))))
    }
    println!("\nRecursion:");
    println!("factorial(5) = {}", factorial(5));
    println!("factorial(10) = {}", factorial(10));
    // Fibonacci
    fn fib(n: i64) -> i64 {
        lisp!((if (<= n 1)
            n
            (+ (fib (- n 1)) (fib (- n 2)))
        ))
    }
    println!("\nFibonacci:");
    println!("fib(10) = {}", fib(10));
    // Complex example: computing sum of squares
    println!("\nComplex Example:");
    let result = lisp!((let ((a 3) (b 4) (c 5))
        (+ (* a a) (* b b) (* c c))
    ));
    println!("Sum of squares of 3, 4, 5 = {}", result);
    // Nested conditionals
    let x = 15;
    let result = lisp!((if (< x 10)
        (print 1)
        (if (< x 20)
            (print 2)
            (print 3)
        )
    ));
    println!("Result: {}", result);
}
#[cfg(test)]
mod tests {
    #[test]
    fn test_arithmetic() {
        assert_eq!(lisp!((+ 1 2)), 3);
        assert_eq!(lisp!((+ 1 2 3 4)), 10);
        assert_eq!(lisp!((- 10 3)), 7);
        assert_eq!(lisp!((* 2 3)), 6);
        assert_eq!(lisp!((* 2 3 4)), 24);
        assert_eq!(lisp!((/ 10 2)), 5);
    }
    #[test]
    fn test_comparisons() {
        assert_eq!(lisp!((< 5 10)), true);
        assert_eq!(lisp!((> 5 10)), false);
        assert_eq!(lisp!((== 5 5)), true);
        assert_eq!(lisp!((<= 5 5)), true);
    }
    #[test]
    fn test_logic() {
        assert_eq!(lisp!((and true true)), true);
        assert_eq!(lisp!((and true false)), false);
        assert_eq!(lisp!((or true false)), true);
        assert_eq!(lisp!((or false false)), false);
        assert_eq!(lisp!((not true)), false);
        assert_eq!(lisp!((not false)), true);
    }
    #[test]
    fn test_conditionals() {
        assert_eq!(lisp!((if true 1 2)), 1);
        assert_eq!(lisp!((if false 1 2)), 2);
        assert_eq!(lisp!((if (< 5 10) 100 200)), 100);
    }
    #[test]
    fn test_let() {
        assert_eq!(lisp!((let x 5 x)), 5);
        assert_eq!(lisp!((let x 5 (+ x 10))), 15);
        assert_eq!(lisp!((let ((x 3) (y 4)) (+ x y))), 7);
    }
    #[test]
    fn test_nested() {
        assert_eq!(lisp!((+ (* 2 3) (- 10 5))), 11);
        assert_eq!(lisp!((let x 10 (if (> x 5) (* x 2) (+ x 1)))), 20);
    }
    #[test]
    fn test_lists() {
        let list = lisp!((list 1 2 3));
        assert_eq!(list, vec![1i64, 2, 3]);
        assert_eq!(lisp!((car (list 10 20 30))), 10);
        assert_eq!(lisp!((length (list 1 2 3 4))), 4);
    }
    #[test]
    fn test_lambda() {
        assert_eq!(lisp!(((lambda (x) (* x x)) 5)), 25);
        assert_eq!(lisp!((let f (lambda (a b) (+ a b)) (f 3 4))), 7);
    }
    #[test]
    fn test_defn() {
        defn!(square (x) (* x x));
        assert_eq!(square(5), 25);
        defn!(add_three (x y z) (+ x y z));
        assert_eq!(add_three(1, 2, 3), 6);
    }
    #[test]
    fn test_recursion() {
        fn factorial(n: i64) -> i64 {
            lisp!((if (<= n 1) 1 (* n (factorial (- n 1)))))
        }
        assert_eq!(factorial(5), 120);
        assert_eq!(factorial(0), 1);
    }
}
