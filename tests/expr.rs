/// A simple example illustrating a steppable computation of the kind
/// this library was designed for.
use std::collections::HashMap;
use stutter::{Output, StepFn};

/// A simple expression tree.
enum Expr {
    IntLiteral(i64),
    BoolLiteral(bool),
    Variable(String),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Value(Value),
}

/// A value which represents the outcome from evaluating an expression
/// tree in a given environment.
#[derive(Copy, Clone, PartialEq, Debug)]
enum Value {
    Int(i64),
    Bool(bool),
    Stuck,
}

/// An environment captures a mapping of variable names to their given
/// values.  Given an environment, we can evaluate a given expression
/// to produce a value.
struct Environment {
    bindings: HashMap<String, Value>,
}

impl Environment {
    pub fn new() -> Environment {
        // Construct initially empty environment.
        Self {
            bindings: HashMap::new(),
        }
    }

    pub fn set(&mut self, var: String, value: Value) {
        self.bindings.insert(var, value);
    }
}

impl StepFn<Expr, Value> for Environment {
    /// Take a single step.  Note, this is not particularly efficient,
    /// but it doesn't need to be!
    fn step(&self, expr: Expr) -> Output<Expr, Value> {
        match expr {
            Expr::IntLiteral(i) => {
                let v = Value::Int(i);
                Output::More(Expr::Value(v))
            }
            Expr::BoolLiteral(b) => {
                let v = Value::Bool(b);
                Output::More(Expr::Value(v))
            }
            Expr::Variable(n) => {
                let r = self.bindings.get(&n);
                match r {
                    Some(v) => Output::Done(*v),
                    None => Output::Done(Value::Stuck),
                }
            }
            Expr::Value(v) => Output::Done(v),
            _ => {
                // Hack for now.
                Output::Done(Value::Stuck)
            }
        }
    }
}

// ===============================================================
// Step Tests
// ===============================================================

#[test]
fn test_step_01() {
    let e = Expr::IntLiteral(1);
    eval(e, 1, Value::Int(1));
}

// ===============================================================
// Helpers
// ===============================================================

fn eval(mut expr: Expr, n: u64, expecting: Value) {
    let env = Environment::new();
    // Evaluate exactly n steps
    for i in 0..n {
        expr = env.step(expr).more();
    }
    // Final step
    let v = env.step(expr).done();
    //
    assert_eq!(v, expecting);
}
