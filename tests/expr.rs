use std::collections::HashMap;
use std::convert::From;
/// A simple example illustrating a steppable computation of the kind
/// this library was designed for.
use std::fmt;
use stutter::{Output, StepFn};

// ====================================================================
// Values
// ====================================================================

/// A value which represents the outcome from evaluating an expression
/// tree in a given environment.
#[derive(Copy, Clone, PartialEq, Debug)]
enum Value {
    Int(i64),
    Bool(bool),
    Stuck,
}

impl Value {
    pub fn add(&self, other: &Value) -> Self {
        match (self, other) {
            (Value::Int(v1), Value::Int(v2)) => Value::Int(v1 + v2),
            (_, _) => Value::Stuck,
        }
    }
    pub fn subtract(&self, other: &Value) -> Self {
        match (self, other) {
            (Value::Int(v1), Value::Int(v2)) => Value::Int(v1 - v2),
            (_, _) => Value::Stuck,
        }
    }
    pub fn negate(&self) -> Self {
        match self {
            Value::Int(v) => Value::Int(-v),
            _ => Value::Stuck,
        }
    }

    pub fn stuck_or_more(self) -> Output<Expr, Value> {
        match self {
            Value::Stuck => Output::Done(self),
            _ => Output::More(Expr::Value(self)),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{}", i),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Stuck => write!(f, "Stuck!"),
        }
    }
}

// ====================================================================
// Expressions
// ====================================================================

/// A simple expression tree.
#[derive(Clone)]
enum Expr {
    Value(Value),
    IntLiteral(i64),
    BoolLiteral(bool),
    Variable(String),
    Neg(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Value(v) => write!(f, "[{}]", v),
            Expr::IntLiteral(i) => write!(f, "{}", i),
            Expr::BoolLiteral(b) => write!(f, "{}", b),
            Expr::Variable(v) => write!(f, "{}", v),
            Expr::Neg(e) => write!(f, "-({})", e),
            Expr::Add(l, r) => write!(f, "({}+{})", l, r),
            Expr::Sub(l, r) => write!(f, "({}-{})", l, r),
        }
    }
}

/// Convert the output of a step back into an expression.
impl From<Output<Expr, Value>> for Expr {
    fn from(o: Output<Expr, Value>) -> Self {
        match o {
            Output::Done(v) => Expr::Value(v),
            Output::More(e) => e,
        }
    }
}

// ====================================================================
// Environment
// ====================================================================

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

    pub fn set(mut self, var: &str, value: Value) -> Self {
        self.bindings.insert(var.to_string(), value);
        self
    }

    /// Evaluate a sequence of zero or more expressions by exactly one step.
    pub fn step_nary<M, D>(&self, es: &[Box<Expr>], more: M, done: D) -> Output<Expr, Value>
    where
        M: Fn(&[Box<Expr>]) -> Expr,
        D: Fn(&[Value]) -> Value,
    {
        for i in 0..es.len() {
            let ith = &*es[i];
            match *ith {
                // Operand already a value, so skip.
                Expr::Value(v) => {}
                // Operan not yet a value, so reduce.
                _ => {
                    // FIXME: avoid the clone!
                    let r = Expr::from(self.step(ith.clone()));
                    // FIXME: avoid cloning to vec!
                    let vs = es.to_vec();
                    // Done
                    return Output::More(more(&vs));
                }
            }
        }
        // If we get here, then ready to produce value (or be stuck).
        let mut vals = Vec::new();
        for e in es {
            match **e {
                Expr::Value(v) => {
                    vals.push(v);
                }
                _ => {
                    panic!("dead code reached");
                }
            }
        }
        // Done
        done(&vals).stuck_or_more()
    }

    /// Evaluate a unary expression by one step.  This manages the
    /// reduction of the operand as necessary, including propagation
    /// of stuck.  This also provides a closure which will reduce the
    /// expression to a value at the appropriate point.
    pub fn step_unary<M, D>(&self, e: Box<Expr>, more: M, done: D) -> Output<Expr, Value>
    where
        M: Fn(Box<Expr>) -> Expr,
        D: Fn(Value) -> Value,
    {
        // Evaluate operand
        match *e {
            // Operand already a value, therefore apply unary operation.
            Expr::Value(v) => done(v).stuck_or_more(),
            // Operan not yet a value, therefore recursively reduce.
            _ => match self.step(*e) {
                Output::Done(v) => Output::Done(v),
                Output::More(e) => Output::More(more(Box::new(e))),
            },
        }
    }

    /// Evaluate a binary expression by one step.  This manages the
    /// reduction of the operands as necessary, including propagation
    /// of stuck.  This also provides a closure which will reduce the
    /// expression to a value at the appropriate point.
    pub fn step_binary<M, D>(
        &self,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        more: M,
        done: D,
    ) -> Output<Expr, Value>
    where
        M: Fn(Box<Expr>, Box<Expr>) -> Expr,
        D: Fn(Value, Value) -> Value,
    {
        // Evaluate operand
        match (&*lhs, &*rhs) {
            // Lhs and rhs already values, so reduce overall expression.
            (&Expr::Value(v1), &Expr::Value(v2)) => done(v1, v2).stuck_or_more(),
            // Lhs already a value, so reduce rhs.
            (&Expr::Value(v1), _) => match self.step(*rhs) {
                Output::Done(v) => Output::Done(v),
                Output::More(e) => Output::More(more(lhs, Box::new(e))),
            },
            // Neither are values, so reducen lhs first leaving rhs
            // untouched.
            (_, _) => match self.step(*lhs) {
                Output::Done(v) => Output::Done(v),
                Output::More(e) => Output::More(more(Box::new(e), rhs)),
            },
        }
    }
}

impl StepFn<Expr, Value> for Environment {
    /// Take a single step.  Note, this is not particularly efficient,
    /// but it doesn't need to be!
    fn step(&self, expr: Expr) -> Output<Expr, Value> {
        match expr {
            Expr::Value(v) => Output::Done(v),
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
                    Some(v) => Output::More(Expr::Value(*v)),
                    None => Output::Done(Value::Stuck),
                }
            }
            Expr::Neg(e) => self.step_unary(e, |b| Expr::Neg(b), |v| v.negate()),
            Expr::Add(l, r) => {
                self.step_binary(l, r, |b1, b2| Expr::Add(b1, b2), |v1, v2| v1.add(&v2))
            }
            Expr::Sub(l, r) => {
                self.step_binary(l, r, |b1, b2| Expr::Sub(b1, b2), |v1, v2| v1.subtract(&v2))
            }
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
fn test_literal_01() {
    let e = Expr::IntLiteral(1);
    eval(e, 2, Environment::new(), Value::Int(1));
}

#[test]
fn test_literal_02() {
    let e = Expr::BoolLiteral(false);
    eval(e, 2, Environment::new(), Value::Bool(false));
}

#[test]
fn test_var_01() {
    let e = Expr::Variable("x".to_string());
    let env = Environment::new().set("x", Value::Int(1));
    eval(e, 2, env, Value::Int(1));
}

#[test]
fn test_var_02() {
    let e = Expr::Variable("x".to_string());
    eval(e, 1, Environment::new(), Value::Stuck);
}

#[test]
fn test_neg_01() {
    let e1 = Expr::IntLiteral(1);
    let e2 = Expr::Neg(Box::new(e1));
    eval(e2, 3, Environment::new(), Value::Int(-1));
}

#[test]
fn test_neg_02() {
    let e1 = Expr::IntLiteral(1);
    let e2 = Expr::Neg(Box::new(e1));
    let e3 = Expr::Neg(Box::new(e2));
    eval(e3, 4, Environment::new(), Value::Int(1));
}

#[test]
fn test_neg_03() {
    let e1 = Expr::BoolLiteral(false);
    let e2 = Expr::Neg(Box::new(e1));
    eval(e2, 2, Environment::new(), Value::Stuck);
}

#[test]
fn test_neg_04() {
    let e1 = Expr::BoolLiteral(false);
    let e2 = Expr::Neg(Box::new(e1));
    let e3 = Expr::Neg(Box::new(e2));
    eval(e3, 2, Environment::new(), Value::Stuck);
}

#[test]
fn test_add_01() {
    let e1 = Expr::IntLiteral(1);
    let e2 = Expr::IntLiteral(2);
    let e3 = Expr::Add(Box::new(e1), Box::new(e2));
    eval(e3, 4, Environment::new(), Value::Int(3));
}

#[test]
fn test_add_02() {
    let e1 = Expr::Variable("x".to_string());
    let e2 = Expr::IntLiteral(2);
    let e3 = Expr::Add(Box::new(e1), Box::new(e2));
    let env = Environment::new().set("x", Value::Int(1));
    eval(e3, 4, env, Value::Int(3));
}

#[test]
fn test_sub_01() {
    let e1 = Expr::IntLiteral(3);
    let e2 = Expr::IntLiteral(1);
    let e3 = Expr::Sub(Box::new(e1), Box::new(e2));
    eval(e3, 4, Environment::new(), Value::Int(2));
}

// ===============================================================
// helpers
// ===============================================================

fn eval(mut expr: Expr, n: u64, env: Environment, expecting: Value) {
    println!("{}", expr);
    // Evaluate exactly n steps
    for i in 0..(n - 1) {
        expr = env.step(expr).more();
        println!("=> {}", expr);
    }
    // Final step
    let v = env.step(expr).done();
    //
    assert_eq!(v, expecting);
}
