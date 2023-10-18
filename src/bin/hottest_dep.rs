#![allow(unused)]

// implementing https://www.youtube.com/watch?v=DEj-_k2Nx6o

#[derive(Copy, Clone)]
struct Idx(usize); // DeBruin index
#[derive(Copy, Clone)]
struct Binder<T>(T);

#[derive(Clone)]
enum Term {
    Var(Idx),
    Pi(Box<Term>, Binder<Box<Term>>),
    Sg(Box<Term>, Binder<Box<Term>>),
    Lam(Binder<Box<Term>>),
    App(Box<Term>, Box<Term>),
    Pair(Box<Term>, Box<Term>),
    Fst(Box<Term>),
    Snd(Box<Term>),
    Bool,
    True,
    False,
    BoolInd {
        motive: Binder<Box<Term>>,
        tcase: Box<Term>,
        fcase: Box<Term>,
        scrutinee: Box<Term>,
    },
}

#[derive(Copy, Clone)]
struct Lvl(usize); // DeBruijn level

#[derive(Clone)]
enum Env<Value> {
    Empty,
    Extend(Box<Self>, Value),
}
#[derive(Clone)]
struct Closure<Value> {
    binder: Binder<Box<Term>>,
    env: Env<Value>,
}
#[derive(Clone)]
enum Stuck<Value> {
    Var(Lvl),
    Fst(Box<Self>),
    Snd(Box<Self>),
    App {
        fun: Box<Self>,
        arg: Value,
        base: Value,
    },
    BoolInd {
        motive: Closure<Value>,
        tcase: Value,
        fcase: Value,
        scrutinee: Box<Self>,
    },
}

#[derive(Clone)]
enum Value {
    Pi(Box<Value>, Closure<Box<Self>>),
    Sg(Box<Value>, Closure<Box<Self>>),
    Lam(Closure<Box<Self>>),
    Bool,
    True,
    False,
    Pair(Box<Value>, Box<Value>),
    Stuck(Stuck<Box<Self>>, Box<Value>),
}

type Env1 = Env<Box<Value>>;
type C = Closure<Box<Value>>;

impl Env1 {
    fn proj(&self, i: usize) -> Value {
        match self {
            Env::Empty => unreachable!("empty environment with non-0 index"),
            Env::Extend(env, v) => {
                if i == 0 {
                    (**v).clone()
                } else {
                    // i > 0 because usize
                    env.proj(i - 1)
                }
            }
        }
    }
}

fn app(fun: Value, arg: Value) -> Value {
    match fun {
        Value::Lam(Closure {
            binder: Binder(term),
            env,
        }) => eval(&Env::Extend(Box::new(env), Box::new(arg)), &term),
        Value::Stuck(stuck, tp) => match *tp {
            Value::Pi(
                base,
                Closure {
                    binder: Binder(fam),
                    env,
                },
            ) => {
                let stuck = Stuck::App {
                    fun: Box::new(stuck),
                    arg: Box::new(arg.clone()),
                    base,
                };
                let fiber = eval(&Env::Extend(Box::new(env), Box::new(arg)), &*fam);
                Value::Stuck(stuck, Box::new(fiber))
            }
            _ => unreachable!("bad type"),
        },
        _ => unreachable!("bad type"),
    }
}

fn fst(pair: Value) -> Value {
    match pair {
        Value::Pair(u, _) => *u,
        Value::Stuck(stuck, tp) => match *tp {
            Value::Sg(base, _) => {
                let stuck = Stuck::Fst(Box::new(stuck));
                Value::Stuck(stuck, base)
            }
            _ => unreachable!("bad type"),
        },
        _ => unreachable!("bad type"),
    }
}

fn snd(pair: Value) -> Value {
    match pair.clone() {
        Value::Pair(_, v) => *v,
        Value::Stuck(stuck, tp) => match *tp {
            Value::Sg(
                _,
                Closure {
                    binder: Binder(fam),
                    env,
                },
            ) => {
                let u = fst(pair);
                let stuck = Stuck::Snd(Box::new(stuck));
                let fiber = eval(&Env::Extend(Box::new(env), Box::new(u)), &fam);
                Value::Stuck(stuck, Box::new(fiber))
            }

            _ => unreachable!("bad type"),
        },
        _ => unreachable!("bad type"),
    }
}

fn ite(env: &Env1, motive: &Term, vtcase: Value, vfcase: Value, vscrutinee: Value) -> Value {
    match vscrutinee {
        Value::True => vtcase,
        Value::False => vfcase,
        Value::Stuck(stuck, tp) => match *tp {
            Value::Bool => {
                let tp = eval(
                    &Env::Extend(
                        Box::new(env.clone()),
                        Box::new(Value::Stuck(stuck.clone(), tp.clone())),
                    ),
                    &motive,
                );
                Value::Stuck(
                    Stuck::BoolInd {
                        motive: Closure {
                            binder: Binder(Box::new(motive.clone())),
                            env: env.clone(),
                        },
                        tcase: Box::new(vtcase),
                        fcase: Box::new(vfcase),
                        scrutinee: Box::new(stuck),
                    },
                    Box::new(tp),
                )
            }
            _ => unreachable!("bad type"),
        },
        _ => unreachable!("bad type"),
    }
}

fn eval(env: &Env1, term: &Term) -> Value {
    match term {
        &Term::Var(Idx(i)) => env.proj(i),
        Term::Pi(base, fam) => {
            let vbase = eval(env, base);
            let cfam = Closure {
                binder: fam.clone(),
                env: env.clone(),
            };
            Value::Pi(Box::new(vbase), cfam)
        }
        Term::Sg(base, fam) => {
            let vbase = eval(env, base);
            let cfam = Closure {
                binder: fam.clone(),
                env: env.clone(),
            };
            Value::Sg(Box::new(vbase), cfam)
        }
        Term::Lam(binder) => Value::Lam(Closure {
            binder: binder.clone(),
            env: env.clone(),
        }),
        Term::App(fun, arg) => {
            let vfun = eval(env, fun);
            let varg = eval(env, arg);
            app(vfun, varg)
        }
        Term::Pair(lt, rt) => {
            let vlt = eval(env, lt);
            let vrt = eval(env, rt);
            Value::Pair(Box::new(vlt), Box::new(vrt))
        }
        Term::Fst(pair) => {
            let vpair = eval(env, pair);
            fst(vpair)
        }
        Term::Snd(pair) => {
            let vpair = eval(env, pair);
            snd(vpair)
        }
        Term::Bool => Value::Bool,
        Term::True => Value::True,
        Term::False => Value::False,
        Term::BoolInd {
            motive: Binder(motive),
            tcase,
            fcase,
            scrutinee,
        } => {
            let vtcase = eval(env, tcase);
            let vfcase = eval(env, fcase);
            let vscrutinee = eval(env, scrutinee);
            ite(env, motive, vtcase, vfcase, vscrutinee)
        }
    }
}

fn equate_tp(i: usize, lt: &Value, rt: &Value) -> Option<()> {
    match (lt, rt) {
        (
            Value::Pi(
                base1,
                Closure {
                    binder: Binder(fam1),
                    env: env1,
                },
            ),
            Value::Pi(
                base2,
                Closure {
                    binder: Binder(fam2),
                    env: env2,
                },
            ),
        ) => {
            equate_tp(i, base1, base2)?;
            let var = Value::Stuck(Stuck::Var(Lvl(i)), base1.clone());
            let fiber1 = eval(
                &Env::Extend(Box::new(env1.clone()), Box::new(var.clone())),
                fam1,
            );
            let fiber2 = eval(&Env::Extend(Box::new(env2.clone()), Box::new(var)), fam2);
            equate_tp(i + 1, &fiber1, &fiber2)
        }
        (Value::Sg(base1, fam1), Value::Sg(base2, fam2)) => {
            equate_tp(i, base1, base2)?;
            todo!()
        }
        (Value::Bool, Value::Bool) => Some(()),
        _ => None,
    }
}

fn equate(i: usize, tp: &Value, lt: &Value, rt: &Value) -> Option<()> {
    match tp {
        Value::Pi(
            base,
            Closure {
                binder: Binder(fam),
                env,
            },
        ) => {
            let var = Value::Stuck(Stuck::Var(Lvl(i)), base.clone());
            let lres = app(lt.clone(), var.clone());
            let rres = app(rt.clone(), var.clone());
            let fiber = eval(&Env::Extend(Box::new(env.clone()), Box::new(var)), fam);
            equate(i + 1, &fiber, &lres, &rres)
        }
        Value::Sg(
            base,
            Closure {
                binder: Binder(fam),
                env,
            },
        ) => {
            let fst1 = fst(lt.clone());
            let fst2 = fst(rt.clone());
            equate(i, base, &fst1, &fst2)?;
            let snd1 = snd(lt.clone());
            let snd2 = snd(rt.clone());
            let fiber = eval(&Env::Extend(Box::new(env.clone()), Box::new(fst1)), fam);
            equate(i, &fiber, &snd1, &snd2)
        }
        _ => match (lt, rt) {
            (Value::True, Value::True) => Some(()),
            (Value::False, Value::False) => Some(()),
            (Value::Stuck(stuck1, tp1), Value::Stuck(stuck2, tp2)) => {
                equate_tp(i, tp1, tp2)?;
                equate_stuck(i, stuck1, stuck2)
            }
            _ => None,
        },
    }
}

fn equate_stuck(i: usize, stuck1: &Stuck<Box<Value>>, stuck2: &Stuck<Box<Value>>) -> Option<()> {
    match (stuck1, stuck2) {
        (Stuck::Var(Lvl(l1)), Stuck::Var(Lvl(l2))) if l1 == l2 => Some(()),
        (Stuck::Fst(stuck1), Stuck::Fst(stuck2)) => equate_stuck(i, stuck1, stuck2),
        (Stuck::Snd(stuck1), Stuck::Snd(stuck2)) => equate_stuck(i, stuck1, stuck2),
        (
            Stuck::App {
                fun: fun1,
                arg: arg1,
                base: base1,
            },
            Stuck::App {
                fun: fun2,
                arg: arg2,
                base: base2,
            },
        ) => {
            equate_stuck(i, fun1, fun2)?;
            equate_tp(i, base1, base2)?;
            equate(i, base1, arg1, arg2)
        }
        (
            Stuck::BoolInd {
                motive:
                    Closure {
                        binder: Binder(fam1),
                        env: env1,
                    },
                tcase: tcase1,
                fcase: fcase1,
                scrutinee: scrut1,
            },
            Stuck::BoolInd {
                motive:
                    Closure {
                        binder: Binder(fam2),
                        env: env2,
                    },
                tcase: tcase2,
                fcase: fcase2,
                scrutinee: scrut2,
            },
        ) => {
            equate_stuck(i, scrut1, scrut2)?;
            // XXX: we are always using (env, True |- mot), can we eval ttp and just save it in Stuck::BoolInd?
            let tfiber1 = eval(
                &Env::Extend(Box::new(env1.clone()), Box::new(Value::True)),
                fam1,
            );
            let tfiber2 = eval(
                &Env::Extend(Box::new(env2.clone()), Box::new(Value::True)),
                fam2,
            );
            equate_tp(i, &tfiber1, &tfiber2)?;
            equate(i, &tfiber1, &tcase1, &tcase2)?;
            let ffiber1 = eval(
                &Env::Extend(Box::new(env1.clone()), Box::new(Value::False)),
                fam1,
            );
            let ffiber2 = eval(
                &Env::Extend(Box::new(env2.clone()), Box::new(Value::False)),
                fam2,
            );
            equate_tp(i, &ffiber1, &ffiber2)?;
            equate(i, &ffiber1, fcase1, fcase2)
        }
        _ => None,
    }
}

fn main() {}
