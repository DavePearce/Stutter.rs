/// Captures the output from a steppable function.  In the future,
/// this should become an associated type.
pub enum Output<S, T> {
    /// Indicates the given computation has yet to reach a terminal
    /// state.
    More(S),
    /// Indicates the given computation has reached a terminal state.
    Done(T),
}

impl<S, T> Output<S, T> {
    pub fn is_more(&self) -> bool {
        match self {
            Output::More(_) => true,
            Output::Done(_) => false,
        }
    }

    pub fn is_done(&self) -> bool {
        match self {
            Output::More(_) => false,
            Output::Done(_) => true,
        }
    }

    pub fn more(self) -> S {
        match self {
            Output::More(s) => s,
            Output::Done(_) => {
                panic!("no more as computation done!");
            }
        }
    }

    pub fn done(self) -> T {
        match self {
            Output::More(_) => {
                panic!("computation is not yet done!");
            }
            Output::Done(t) => t,
        }
    }

    pub fn done_or_apply<F>(self, f: F) -> Output<S, T>
    where
        F: Fn(S) -> S,
    {
        match self {
            Output::More(t) => Output::More(f(t)),
            _ => self,
        }
    }
}

/// A trait capturing the essence of a steppable computation.  We can
/// take a single step on a computation with a given state `S` which
/// either produces an updated state `S` or a terminal state `T`.
pub trait StepFn<S, T> {
    /// Take a single step in the computation.
    fn step(&self, state: S) -> Output<S, T>;

    /// Take at most `n` steps in the computation.
    fn nstep(&self, state: S, n: u64) -> Output<S, T> {
        let mut st = state;
        // Iterate at most n steps
        for _i in 0..n {
            match self.step(st) {
                Output::More(s) => {
                    st = s;
                }
                Output::Done(t) => {
                    return Output::Done(t);
                }
            }
        }
        // Done!
        Output::More(st)
    }

    /// Take a _big step_ in the computation (i.e. attempt to reduce
    /// all the way to a terminal state).
    fn bigstep(&self, state: S) -> T {
        let mut st = state;
        // Obviously, this could cause an infinite loop.
        loop {
            match self.step(st) {
                Output::More(s) => {
                    st = s;
                }
                Output::Done(t) => {
                    return t;
                }
            }
        }
    }
}

/// A trait capturing the essence of a steppable computation over
/// _mutable_ state.  We can take a single step on a computation with
/// a given state `S` which either produces an updated state `S` or a
/// terminal state `T`.
pub trait StepMutFn<S, T> {
    /// Take a single step in the computation.
    fn step(&mut self, state: S) -> Output<S, T>;

    /// Take at most `n` steps in the computation.
    fn nstep(&mut self, state: S, n: u64) -> Output<S, T> {
        let mut st = state;
        // Iterate at most n steps
        for _i in 0..n {
            match self.step(st) {
                Output::More(s) => {
                    st = s;
                }
                Output::Done(t) => {
                    return Output::Done(t);
                }
            }
        }
        // Done!
        Output::More(st)
    }

    /// Take a _big step_ in the computation (i.e. attempt to reduce
    /// all the way to a terminal state).
    fn bigstep(&mut self, state: S) -> T {
        let mut st = state;
        // Obviously, this could cause an infinite loop.
        loop {
            match self.step(st) {
                Output::More(s) => {
                    st = s;
                }
                Output::Done(t) => {
                    return t;
                }
            }
        }
    }
}
