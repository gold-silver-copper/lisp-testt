/// Interactive REPL for Macro Lisp
///
/// Run with: cargo run --example repl
///
/// This REPL uses a hybrid approach:
/// - Runtime interpreter for interactive user input (necessary for REPL functionality)
/// - Compile-time macros for pre-defined functions (using the macro_lisp library)
/// - Demonstrates both approaches side-by-side
use std::collections::HashMap;
use std::io::{self, Write};

// Import the macro from our library
use macro_lisp::{defn, lisp};

#[derive(Debug, Clone, PartialEq)]
enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Symbol(String),
    List(Vec<Value>),
    Function(String), // Built-in macro functions
    Nil,
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Float(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Symbol(s) => write!(f, "{}", s),
            Value::List(items) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, ")")
            }
            Value::Function(name) => write!(f, "<macro-function:{}>", name),
            Value::Nil => write!(f, "nil"),
        }
    }
}

// Pre-compiled macro functions
defn!(macro_square (x) (* x x));
defn!(macro_cube (x) (* x (* x x)));
defn!(macro_add_three (x y z) (+ x y z));

fn macro_factorial(n: i32) -> i32 {
    lisp!((if (<= n 1) 1 (* n (macro_factorial (- n 1)))))
}

fn macro_fib(n: i32) -> i32 {
    lisp!((if (<= n 1)
        n
        (+ (macro_fib (- n 1)) (macro_fib (- n 2)))
    ))
}

fn macro_sum_of_squares(a: i32, b: i32) -> i32 {
    lisp!((+ (* a a) (* b b)))
}

fn macro_is_even(n: i32) -> bool {
    lisp!((== (% n 2) 0))
}

#[derive(Debug)]
enum Token {
    LParen,
    RParen,
    Symbol(String),
    Number(String),
}

fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();

    while let Some(&ch) = chars.peek() {
        match ch {
            ' ' | '\t' | '\n' | '\r' => {
                chars.next();
            }
            '(' => {
                tokens.push(Token::LParen);
                chars.next();
            }
            ')' => {
                tokens.push(Token::RParen);
                chars.next();
            }
            _ => {
                let mut symbol = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch == '(' || ch == ')' || ch.is_whitespace() {
                        break;
                    }
                    symbol.push(ch);
                    chars.next();
                }

                if symbol
                    .chars()
                    .all(|c| c.is_numeric() || c == '-' || c == '.')
                {
                    tokens.push(Token::Number(symbol));
                } else {
                    tokens.push(Token::Symbol(symbol));
                }
            }
        }
    }

    Ok(tokens)
}

fn parse(tokens: &[Token]) -> Result<(Value, usize), String> {
    if tokens.is_empty() {
        return Err("Unexpected end of input".to_string());
    }

    match &tokens[0] {
        Token::Number(n) => {
            if n.contains('.') {
                Ok((Value::Float(n.parse().map_err(|_| "Invalid float")?), 1))
            } else {
                Ok((Value::Int(n.parse().map_err(|_| "Invalid int")?), 1))
            }
        }
        Token::Symbol(s) => {
            let val = match s.as_str() {
                "true" => Value::Bool(true),
                "false" => Value::Bool(false),
                "nil" => Value::Nil,
                _ => Value::Symbol(s.clone()),
            };
            Ok((val, 1))
        }
        Token::LParen => {
            let mut i = 1;
            let mut list = Vec::new();

            while i < tokens.len() {
                if matches!(tokens[i], Token::RParen) {
                    return Ok((Value::List(list), i + 1));
                }

                let (val, consumed) = parse(&tokens[i..])?;
                list.push(val);
                i += consumed;
            }

            Err("Unmatched '('".to_string())
        }
        Token::RParen => Err("Unexpected ')'".to_string()),
    }
}

fn eval(expr: &Value, env: &mut HashMap<String, Value>) -> Result<Value, String> {
    match expr {
        Value::Int(_) | Value::Float(_) | Value::Bool(_) | Value::Nil | Value::Function(_) => {
            Ok(expr.clone())
        }

        Value::Symbol(s) => env
            .get(s)
            .cloned()
            .ok_or_else(|| format!("Undefined symbol: {}", s)),

        Value::List(items) => {
            if items.is_empty() {
                return Ok(Value::Nil);
            }

            let first = &items[0];
            if let Value::Symbol(op) = first {
                match op.as_str() {
                    // Check for macro-compiled functions first
                    "square" => {
                        if items.len() != 2 {
                            return Err("square requires 1 argument".to_string());
                        }
                        if let Value::Int(n) = eval(&items[1], env)? {
                            Ok(Value::Int(macro_square(n as i32) as i64))
                        } else {
                            Err("square requires integer".to_string())
                        }
                    }
                    "cube" => {
                        if items.len() != 2 {
                            return Err("cube requires 1 argument".to_string());
                        }
                        if let Value::Int(n) = eval(&items[1], env)? {
                            Ok(Value::Int(macro_cube(n as i32) as i64))
                        } else {
                            Err("cube requires integer".to_string())
                        }
                    }
                    "factorial" => {
                        if items.len() != 2 {
                            return Err("factorial requires 1 argument".to_string());
                        }
                        if let Value::Int(n) = eval(&items[1], env)? {
                            Ok(Value::Int(macro_factorial(n as i32) as i64))
                        } else {
                            Err("factorial requires integer".to_string())
                        }
                    }
                    "fib" => {
                        if items.len() != 2 {
                            return Err("fib requires 1 argument".to_string());
                        }
                        if let Value::Int(n) = eval(&items[1], env)? {
                            Ok(Value::Int(macro_fib(n as i32) as i64))
                        } else {
                            Err("fib requires integer".to_string())
                        }
                    }
                    "sum-of-squares" => {
                        if items.len() != 3 {
                            return Err("sum-of-squares requires 2 arguments".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        let b = eval(&items[2], env)?;
                        if let (Value::Int(x), Value::Int(y)) = (a, b) {
                            Ok(Value::Int(macro_sum_of_squares(x as i32, y as i32) as i64))
                        } else {
                            Err("sum-of-squares requires integers".to_string())
                        }
                    }
                    "even?" => {
                        if items.len() != 2 {
                            return Err("even? requires 1 argument".to_string());
                        }
                        if let Value::Int(n) = eval(&items[1], env)? {
                            Ok(Value::Bool(macro_is_even(n as i32)))
                        } else {
                            Err("even? requires integer".to_string())
                        }
                    }

                    // Standard runtime operations
                    "+" => {
                        let mut sum = 0i64;
                        for arg in &items[1..] {
                            if let Value::Int(n) = eval(arg, env)? {
                                sum += n;
                            } else {
                                return Err("+ requires integers".to_string());
                            }
                        }
                        Ok(Value::Int(sum))
                    }
                    "-" => {
                        if items.len() != 3 {
                            return Err("- requires exactly 2 arguments".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        let b = eval(&items[2], env)?;
                        if let (Value::Int(x), Value::Int(y)) = (a, b) {
                            Ok(Value::Int(x - y))
                        } else {
                            Err("- requires integers".to_string())
                        }
                    }
                    "*" => {
                        let mut product = 1i64;
                        for arg in &items[1..] {
                            if let Value::Int(n) = eval(arg, env)? {
                                product *= n;
                            } else {
                                return Err("* requires integers".to_string());
                            }
                        }
                        Ok(Value::Int(product))
                    }
                    "/" => {
                        if items.len() != 3 {
                            return Err("/ requires exactly 2 arguments".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        let b = eval(&items[2], env)?;
                        if let (Value::Int(x), Value::Int(y)) = (a, b) {
                            if y == 0 {
                                return Err("Division by zero".to_string());
                            }
                            Ok(Value::Int(x / y))
                        } else {
                            Err("/ requires integers".to_string())
                        }
                    }
                    "%" => {
                        if items.len() != 3 {
                            return Err("% requires exactly 2 arguments".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        let b = eval(&items[2], env)?;
                        if let (Value::Int(x), Value::Int(y)) = (a, b) {
                            Ok(Value::Int(x % y))
                        } else {
                            Err("% requires integers".to_string())
                        }
                    }

                    "<" => {
                        if items.len() != 3 {
                            return Err("< requires exactly 2 arguments".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        let b = eval(&items[2], env)?;
                        if let (Value::Int(x), Value::Int(y)) = (a, b) {
                            Ok(Value::Bool(x < y))
                        } else {
                            Err("< requires integers".to_string())
                        }
                    }
                    ">" => {
                        if items.len() != 3 {
                            return Err("> requires exactly 2 arguments".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        let b = eval(&items[2], env)?;
                        if let (Value::Int(x), Value::Int(y)) = (a, b) {
                            Ok(Value::Bool(x > y))
                        } else {
                            Err("> requires integers".to_string())
                        }
                    }
                    "==" => {
                        if items.len() != 3 {
                            return Err("== requires exactly 2 arguments".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        let b = eval(&items[2], env)?;
                        Ok(Value::Bool(a == b))
                    }
                    "<=" => {
                        if items.len() != 3 {
                            return Err("<= requires exactly 2 arguments".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        let b = eval(&items[2], env)?;
                        if let (Value::Int(x), Value::Int(y)) = (a, b) {
                            Ok(Value::Bool(x <= y))
                        } else {
                            Err("<= requires integers".to_string())
                        }
                    }

                    "and" => {
                        if items.len() != 3 {
                            return Err("and requires exactly 2 arguments".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        let b = eval(&items[2], env)?;
                        if let (Value::Bool(x), Value::Bool(y)) = (a, b) {
                            Ok(Value::Bool(x && y))
                        } else {
                            Err("and requires booleans".to_string())
                        }
                    }
                    "or" => {
                        if items.len() != 3 {
                            return Err("or requires exactly 2 arguments".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        let b = eval(&items[2], env)?;
                        if let (Value::Bool(x), Value::Bool(y)) = (a, b) {
                            Ok(Value::Bool(x || y))
                        } else {
                            Err("or requires booleans".to_string())
                        }
                    }
                    "not" => {
                        if items.len() != 2 {
                            return Err("not requires exactly 1 argument".to_string());
                        }
                        let a = eval(&items[1], env)?;
                        if let Value::Bool(x) = a {
                            Ok(Value::Bool(!x))
                        } else {
                            Err("not requires boolean".to_string())
                        }
                    }

                    "if" => {
                        if items.len() != 4 {
                            return Err("if requires exactly 3 arguments".to_string());
                        }
                        let cond = eval(&items[1], env)?;
                        if let Value::Bool(b) = cond {
                            if b {
                                eval(&items[2], env)
                            } else {
                                eval(&items[3], env)
                            }
                        } else {
                            Err("if condition must be boolean".to_string())
                        }
                    }

                    "let" => {
                        if items.len() != 4 {
                            return Err("let requires exactly 3 arguments".to_string());
                        }
                        if let Value::Symbol(var) = &items[1] {
                            let val = eval(&items[2], env)?;
                            let mut new_env = env.clone();
                            new_env.insert(var.clone(), val);
                            eval(&items[3], &mut new_env)
                        } else {
                            Err("let requires symbol as first argument".to_string())
                        }
                    }

                    "define" => {
                        if items.len() != 3 {
                            return Err("define requires exactly 2 arguments".to_string());
                        }
                        if let Value::Symbol(var) = &items[1] {
                            let val = eval(&items[2], env)?;
                            env.insert(var.clone(), val.clone());
                            Ok(val)
                        } else {
                            Err("define requires symbol as first argument".to_string())
                        }
                    }

                    "list" => {
                        let mut result = Vec::new();
                        for arg in &items[1..] {
                            result.push(eval(arg, env)?);
                        }
                        Ok(Value::List(result))
                    }
                    "car" => {
                        if items.len() != 2 {
                            return Err("car requires exactly 1 argument".to_string());
                        }
                        let list = eval(&items[1], env)?;
                        if let Value::List(lst) = list {
                            lst.first()
                                .cloned()
                                .ok_or_else(|| "car on empty list".to_string())
                        } else {
                            Err("car requires list".to_string())
                        }
                    }
                    "cdr" => {
                        if items.len() != 2 {
                            return Err("cdr requires exactly 1 argument".to_string());
                        }
                        let list = eval(&items[1], env)?;
                        if let Value::List(lst) = list {
                            if lst.is_empty() {
                                Ok(Value::Nil)
                            } else {
                                Ok(Value::List(lst[1..].to_vec()))
                            }
                        } else {
                            Err("cdr requires list".to_string())
                        }
                    }
                    "cons" => {
                        if items.len() != 3 {
                            return Err("cons requires exactly 2 arguments".to_string());
                        }
                        let item = eval(&items[1], env)?;
                        let list = eval(&items[2], env)?;
                        if let Value::List(mut lst) = list {
                            let mut result = vec![item];
                            result.append(&mut lst);
                            Ok(Value::List(result))
                        } else {
                            Err("cons requires list as second argument".to_string())
                        }
                    }

                    _ => Err(format!("Unknown operator: {}", op)),
                }
            } else {
                Err("First element of list must be a symbol".to_string())
            }
        }
    }
}

fn repl() {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║           Macro Lisp REPL v2.0 (Hybrid Mode)              ║");
    println!("╠════════════════════════════════════════════════════════════╣");
    println!("║  Using compile-time macros for built-in functions!        ║");
    println!("║  Type Lisp expressions and press Enter                    ║");
    println!("║  Commands: :help, :quit, :clear, :macros                  ║");
    println!("╚════════════════════════════════════════════════════════════╝");
    println!();
    println!("🚀 Macro-compiled functions available: square, cube, factorial, fib");
    println!("   sum-of-squares, even?");
    println!();

    let mut env = HashMap::new();

    loop {
        print!("λ> ");
        io::stdout().flush().unwrap();

        let mut input = String::new();
        if io::stdin().read_line(&mut input).is_err() {
            break;
        }

        let input = input.trim();

        if input.is_empty() {
            continue;
        }

        match input {
            ":quit" | ":q" | ":exit" => {
                println!("Goodbye!");
                break;
            }
            ":help" | ":h" => {
                print_help();
                continue;
            }
            ":clear" | ":c" => {
                env.clear();
                println!("Environment cleared.");
                continue;
            }
            ":env" => {
                println!("Current environment:");
                for (key, val) in &env {
                    println!("  {} = {}", key, val);
                }
                continue;
            }
            ":macros" | ":m" => {
                print_macros();
                continue;
            }
            _ => {}
        }

        match tokenize(input) {
            Ok(tokens) => match parse(&tokens) {
                Ok((expr, _)) => match eval(&expr, &mut env) {
                    Ok(result) => println!("=> {}", result),
                    Err(e) => println!("Evaluation error: {}", e),
                },
                Err(e) => println!("Parse error: {}", e),
            },
            Err(e) => println!("Tokenize error: {}", e),
        }
    }
}

fn print_macros() {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║              MACRO-COMPILED FUNCTIONS                      ║");
    println!("╠════════════════════════════════════════════════════════════╣");
    println!("║ These functions use the compile-time macro_lisp library   ║");
    println!("║ and are compiled to native Rust code for maximum speed!   ║");
    println!("║                                                            ║");
    println!("║ (square x)           - x²                                 ║");
    println!("║ (cube x)             - x³                                 ║");
    println!("║ (factorial n)        - n! (recursive)                     ║");
    println!("║ (fib n)              - Fibonacci(n) (recursive)           ║");
    println!("║ (sum-of-squares a b) - a² + b²                            ║");
    println!("║ (even? n)            - Check if n is even                 ║");
    println!("║                                                            ║");
    println!("║ Example usage:                                             ║");
    println!("║   λ> (square 5)                                            ║");
    println!("║   => 25                                                    ║");
    println!("║   λ> (factorial 10)                                        ║");
    println!("║   => 3628800                                               ║");
    println!("╚════════════════════════════════════════════════════════════╝");
}

fn print_help() {
    println!("╔════════════════════════════════════════════════════════════╗");
    println!("║                    MACRO LISP HELP                         ║");
    println!("╠════════════════════════════════════════════════════════════╣");
    println!("║ Arithmetic:                                                ║");
    println!("║   (+ 1 2 3)      => 6                                      ║");
    println!("║   (- 10 3)       => 7                                      ║");
    println!("║   (* 2 3 4)      => 24                                     ║");
    println!("║   (/ 20 4)       => 5                                      ║");
    println!("║                                                            ║");
    println!("║ Comparisons:                                               ║");
    println!("║   (< 5 10)       => true                                   ║");
    println!("║   (> 5 10)       => false                                  ║");
    println!("║   (== 5 5)       => true                                   ║");
    println!("║                                                            ║");
    println!("║ Logic:                                                     ║");
    println!("║   (and true false)  => false                               ║");
    println!("║   (or true false)   => true                                ║");
    println!("║   (not true)        => false                               ║");
    println!("║                                                            ║");
    println!("║ Control Flow:                                              ║");
    println!("║   (if (< 5 10) 100 200)  => 100                            ║");
    println!("║                                                            ║");
    println!("║ Variables:                                                 ║");
    println!("║   (define x 42)          => 42                             ║");
    println!("║   (let x 5 (+ x 10))     => 15                             ║");
    println!("║                                                            ║");
    println!("║ Lists:                                                     ║");
    println!("║   (list 1 2 3)           => (1 2 3)                        ║");
    println!("║   (car (list 1 2 3))     => 1                              ║");
    println!("║   (cdr (list 1 2 3))     => (2 3)                          ║");
    println!("║   (cons 0 (list 1 2))    => (0 1 2)                        ║");
    println!("║                                                            ║");
    println!("║ 🚀 Macro Functions (compiled):                             ║");
    println!("║   (square 5)             => 25                             ║");
    println!("║   (factorial 5)          => 120                            ║");
    println!("║   (fib 10)               => 55                             ║");
    println!("║                                                            ║");
    println!("║ Commands:                                                  ║");
    println!("║   :help, :h    - Show this help                            ║");
    println!("║   :macros, :m  - Show macro functions                      ║");
    println!("║   :quit, :q    - Exit REPL                                 ║");
    println!("║   :clear, :c   - Clear environment                         ║");
    println!("║   :env         - Show environment                          ║");
    println!("╚════════════════════════════════════════════════════════════╝");
}

fn main() {
    repl();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_macro_functions() {
        let mut env = HashMap::new();

        let tokens = tokenize("(square 5)").unwrap();
        let (expr, _) = parse(&tokens).unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(result, Value::Int(25));

        let tokens = tokenize("(factorial 5)").unwrap();
        let (expr, _) = parse(&tokens).unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(result, Value::Int(120));
    }

    #[test]
    fn test_runtime_arithmetic() {
        let mut env = HashMap::new();
        let tokens = tokenize("(+ 1 2 3)").unwrap();
        let (expr, _) = parse(&tokens).unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(result, Value::Int(6));
    }
}
