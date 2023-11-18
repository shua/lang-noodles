#![allow(dead_code)]

use log::debug;
use std::fmt::{Display, Formatter, Result as FmtResult};

// types

#[derive(Clone)]
enum Expr {
    /// ()
    Unit,
    /// x \\in Vars
    Var(usize),
    /// n \\in Nat
    Nat(u64),
    /// x = e1 in e2
    Let(Box<Self>, Box<Self>),
    /// \\x@c.e
    Fun(Box<Type>, Option<Cap>, Box<Self>),
    /// e e
    Apply(Box<Self>, Box<Self>),
}

#[derive(Clone, PartialEq)]
enum Type {
    Unit,
    Nat,
    Arrow(Box<Self>, Option<Cap>, Box<Self>),
}

#[derive(Clone, Debug)]
enum CapOpt {
    Inherit,
    Set(Box<Cap>),
}
#[derive(Clone, Debug, Default)]
struct Cap {
    /// apply()
    apply: bool,
    /// bind = _
    bind: bool,
    /// fun() { _ }
    fun: Option<CapOpt>,
}

#[derive(Clone)]
struct Ctx(Vec<Type>);

#[derive(Clone)]
enum SynExpr {
    Unit,
    Var(&'static str),
    Nat(u64),
    Let(&'static str, Box<Self>, Box<Self>),
    Fun(&'static str, Type, Box<Self>),
    Apply(Box<Self>, Box<Self>),
}

macro_rules! cap {
    (@ $c:expr ; $(,)*) => { $c };
    (@ $c:expr ; bind = _ , $($tl:tt)*) => {
        cap!(@ $c.with_bind() ; $($tl)*)
    };
    (@ $c:expr ; apply() , $($tl:tt)*) => {
        cap!(@ $c.with_apply() ; $($tl)*)
    };
    (@ $c:expr ; fun() { _ } , $($tl:tt)*) => {
        cap!(@ $c.with_fun(None) ; $($tl)*)
    };
    (@ $c:expr ; fun() { $($fun:tt)* } , $($tl:tt)*) => {
        cap!(@ $c.with_fun(Some(cap![$($fun)*])) ; $($tl)*)
    };
    (($($c:tt)*)) => { cap![ $($c)* ] };
    (#$c:expr) => { $c };
    ($($c:tt)*) => { cap!(@ Cap::default() ; $($c)* , ) };
}

macro_rules! typ {
    () => { Type::Unit };
    (1) => { Type::Unit };
    ($t1:tt -> $t2:tt @$c:tt) => { Type::Arrow(Box::new(typ!($t1)), Some(cap![$c]), Box::new(typ!($t2))) };
    ($t1:tt -> $t2:tt) => { Type::Arrow(Box::new(typ!($t1)), None, Box::new(typ!($t2)))};
    (nat) => { Type::Nat };
    (#$v:expr) => { $v };
    (($($t:tt)*)) => { typ!($($t)*) };
}

macro_rules! expr {
    () => { SynExpr::Unit };
    (fun($x:ident : $t:tt) $b:tt) => {
        SynExpr::Fun(stringify!($x), typ!($t), Box::new(expr!($b)))
    };
    (let $x:ident = $e1:tt in $($tl:tt)*) => {
        SynExpr::Let(stringify!($x), Box::new(expr!($e1)), Box::new(expr!($($tl)*)))
    };
    (#$v:expr) => { $v };
    ($e1:tt $e2:tt) => {
        SynExpr::Apply(Box::new(expr!($e1)), Box::new(expr!($e2)))
    };
    ($x:ident) => {
        SynExpr::Var(stringify!($x))
    };
    ($n:literal) => {
        SynExpr::Nat($n)
    };
    (($($e:tt)*)) => { expr!($($e)*) };
    ({$($e:tt)*}) => { expr!($($e)*) };
}

// impls

impl Ctx {
    fn get(&self, i: usize) -> Option<&Type> {
        if i < self.0.len() {
            self.0.get(self.0.len() - i - 1)
        } else {
            None
        }
    }
}

impl Cap {
    fn with_bind(mut self) -> Self {
        self.bind = true;
        self
    }
    fn with_apply(mut self) -> Self {
        self.apply = true;
        self
    }
    fn with_fun(mut self, c: Option<Cap>) -> Self {
        self.fun = Some(match c {
            Some(c) => CapOpt::Set(Box::new(c)),
            None => CapOpt::Inherit,
        });
        self
    }
    fn permits(&self, c: &Cap) -> bool {
        debug!("permits {c} <: {self}");
        if c.apply && !self.apply {
            return false;
        }
        if c.bind && !self.bind {
            return false;
        }
        if let Some(c2) = &c.fun {
            let Some(c1) = &self.fun else {
                return false;
            };
            match (c1, c2) {
                (CapOpt::Inherit, CapOpt::Inherit) => true,
                (CapOpt::Set(c1), CapOpt::Inherit) => c1.permits(c),
                (CapOpt::Set(c1), CapOpt::Set(c2)) => c1.permits(&c2),
                (CapOpt::Inherit, CapOpt::Set(c2)) => self.permits(&c2),
            }
        } else {
            true
        }
    }

    fn least_upper_bound(&self, rhs: &Cap) -> Cap {
        let mut ret = Cap::default();
        if self.bind || rhs.bind {
            ret = ret.with_bind();
        }
        if self.apply || rhs.apply {
            ret = ret.with_apply();
        }
        match (&self.fun, &rhs.fun) {
            (cfun, None) | (None, cfun) => ret.fun = cfun.clone(),
            (Some(c1), Some(c2)) => match (c1, c2) {
                (CapOpt::Inherit, CapOpt::Inherit) => ret.fun = Some(CapOpt::Inherit),
                (CapOpt::Inherit, CapOpt::Set(c2)) => {
                    ret.fun = Some(CapOpt::Set(Box::new(self.least_upper_bound(&c2))))
                }
                (CapOpt::Set(c1), CapOpt::Inherit) => {
                    ret.fun = Some(CapOpt::Set(Box::new(c1.least_upper_bound(rhs))))
                }
                (CapOpt::Set(c1), CapOpt::Set(c2)) => {
                    ret.fun = Some(CapOpt::Set(Box::new(c1.least_upper_bound(&c2))))
                }
            },
        }
        ret
    }
}

impl std::cmp::PartialEq for Cap {
    fn eq(&self, other: &Self) -> bool {
        self.permits(other) && other.permits(self)
    }
}

fn cap_check(c: &Cap, e: &Expr) -> Option<()> {
    match e {
        Expr::Unit => Some(()),
        Expr::Var(_) => Some(()),
        Expr::Nat(_) => Some(()),
        Expr::Let(e1, e2) => {
            c.permits(&Cap::default().with_bind()).then_some(())?;
            cap_check(c, e1)?;
            cap_check(c, e2)?;
            Some(())
        }
        Expr::Fun(_, c1, _) => {
            c.permits(&Cap::default().with_fun(c1.clone()))
                .then_some(())?;
            cap_check(c1.as_ref().unwrap_or(c), e)?;
            Some(())
        }
        Expr::Apply(e1, e2) => {
            c.permits(&Cap::default().with_apply()).then_some(())?;
            cap_check(c, e1)?;
            cap_check(c, e2)?;
            Some(())
        }
    }
}

fn cap_synth(e: &Expr) -> Option<Cap> {
    match e {
        // c |- () -| {}
        // c |- x -| {}
        // c |- n -| {}
        Expr::Unit | Expr::Var(_) | Expr::Nat(_) => Some(Cap::default()),
        // c0 |- e1 -| c1
        // c0 |- e2 -| c2
        // c <: c1
        // c <: c2
        // --------------------
        // c,bind=_ |- x=e1; e2
        Expr::Let(e1, e2) => {
            let c1 = cap_synth(e1)?;
            let c2 = cap_synth(e2)?;
            let c = c1.least_upper_bound(&c2);
            Some(c.with_bind())
        }
        // c2 |- e      c2 <: c1
        // ---------------------------
        // fun() { c1 } |- fun_:t@c1.e
        //
        // c |- e
        // -----------------------
        // fun() { c } |- fun_:t.e
        Expr::Fun(_, c1, e) => {
            if let Some(c1) = c1 {
                cap_check(c1, e)?;
                Some(Cap::default().with_fun(Some(c1.clone())))
            } else {
                let ce = cap_synth(e)?;
                Some(Cap::default().with_fun(Some(ce)))
            }
        }
        // c0 |- e1 -| c1
        // c0 |- e2 -| c2
        // c <: c1
        // c <: c2
        // ------------------
        // c,apply() |- e1 e2
        Expr::Apply(e1, e2) => {
            let c1 = cap_synth(e1)?;
            let c2 = cap_synth(e2)?;
            let c = c1.least_upper_bound(&c2);
            Some(c.with_apply())
        }
    }
}

fn type_sub(c: &Cap, t1: &Type, t2: &Type) -> Option<()> {
    debug!("type_sub {c} |- {t1}  <:  {t2}");
    match (t1, t2) {
        // ---------------
        // |- () <: ()
        (Type::Unit, Type::Unit) => Some(()),
        // c |- t1 <: t3
        // |- c1 <: c2
        // c2 |- t4 <: t2
        // -------------------------------------
        // c |- t1 -> t2 @c1  <:  t3 -> t4 @c2
        (Type::Arrow(t1, c1, t2), Type::Arrow(t3, c2, t4)) => {
            type_sub(c, t1, t3)?;
            let c1 = c1.as_ref().unwrap_or(c);
            let c2 = c2.as_ref().unwrap_or(c);
            c2.permits(c1).then(|| ())?;
            type_sub(c2, t4, t2)?;
            Some(())
        }
        _ => None,
    }
}

fn type_synth(g: &Ctx, c: &Cap, e: &Expr) -> Option<Type> {
    debug!("type_synth {g};{c:#} |- {e:#} : ?");
    match e {
        // G;c |- ():()
        Expr::Unit => Some(typ!()),
        // x:t \in G
        // ----------
        // G;c |- x:t
        Expr::Var(x) => g.get(*x).cloned(),
        // G;c |- n:N
        Expr::Nat(_) => Some(Type::Nat),
        // bind = _ <: c
        // G;c |- e1:t1
        // G,x:t1;c |- e2:t2
        // ----------------------
        // G;c |- x = e1; e2 : t2
        Expr::Let(e1, e2) => {
            c.permits(&Cap::default().with_bind()).then_some(())?;
            let t1 = type_synth(g, c, e1)?;
            let mut g = g.clone();
            g.0.push(t1);
            type_synth(&g, c, e2)
        }
        // c1 |- e
        // fun() { c1 } <: c
        // G,x:t;c |- e:t1
        // ----------------------------------
        // G;c |- fun(x:t)@c1.e : t -> t1 @c1
        // G;c |- fun(x:t).e : t -> t1 @c1
        Expr::Fun(t, c1, e) => {
            let c1 = if let Some(c1) = c1 {
                c1.clone()
            } else {
                cap_synth(&e)?
            };
            c.permits(&Cap::default().with_fun(Some(c1.clone())))
                .then_some(())?;
            let mut g = g.clone();
            g.0.push((**t).clone());
            let t2 = type_synth(&g, &c1, &*e)?;
            let t1 = g.0.pop().unwrap();
            Some(typ!((#t1) -> (#t2) @(#c1)))
        }
        // apply <: c
        // G;c |- e1: t1 -> t @c2
        // c2 <: c
        // G;c |- e2: t2
        // c |- t2 <: t1
        // ------------------
        // G;c |- e1 e2 : t
        Expr::Apply(e1, e2) => {
            let t1 = type_synth(g, c, e1)?;
            let t2 = type_synth(g, c, e2)?;
            debug!("type_synth:apply {g};{c:#} |- (e1, e2) : (\n\t{t1},\n\t{t2}\n)");
            match t1 {
                Type::Arrow(t1, c1, t) => {
                    c.permits(&Cap::default().with_apply()).then_some(())?;
                    let c1 = c1.as_ref().unwrap_or(c);
                    c.permits(c1).then(|| ())?;
                    debug!("type_synth:apply g;c |- t2 <: t1");
                    type_sub(c, &t2, &t1)?;
                    Some(*t)
                }
                _ => None,
            }
        }
    }
}

fn eval(e: Expr) -> Expr {
    fn subst(x: usize, v: Expr, e: Expr) -> Expr {
        match e {
            Expr::Var(y) if y == x => v,
            Expr::Let(e1, e2) => {
                let e1 = subst(x, v.clone(), *e1);
                let e2 = subst(x + 1, v, *e2);
                Expr::Let(Box::new(e1), Box::new(e2))
            }
            Expr::Fun(t, c, e) => {
                let e = subst(x + 1, v, *e);
                Expr::Fun(t, c, Box::new(e))
            }
            Expr::Apply(e1, e2) => {
                let e1 = subst(x, v.clone(), *e1);
                let e2 = subst(x, v, *e2);
                Expr::Apply(Box::new(e1), Box::new(e2))
            }
            e => e,
        }
    }
    match e {
        Expr::Let(e1, e2) => {
            let e1 = eval(*e1);
            let e2 = subst(0, e1, *e2);
            eval(e2)
        }
        Expr::Apply(e1, e2) => {
            let e1 = eval(*e1);
            match e1 {
                Expr::Fun(_, _, e) => {
                    let e2 = eval(*e2);
                    let e = subst(0, e2, *e);
                    eval(e)
                }
                _ => panic!("bad type"),
            }
        }
        e => e,
    }
}

// Display impls

struct DebugDisplay<'a>(&'a dyn Display);
impl std::fmt::Debug for DebugDisplay<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        self.0.fmt(f)
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Expr::Unit => f.write_str("()"),
            Expr::Var(x) => write!(f, "#{x}"),
            Expr::Nat(n) => write!(f, "{n}"),
            Expr::Let(e1, e2) if f.alternate() => write!(f, "_={e1:#};\n{e2:#}"),
            Expr::Let(e1, e2) => write!(f, "_={e1}; {e2}"),
            Expr::Fun(t, Some(c), e) if f.alternate() => {
                write!(f, "fun_:{t}@{c}.")?;
                f.debug_set().entry(&DebugDisplay(&e)).finish()
            }
            Expr::Fun(t, Some(c), e) => write!(f, "fun_:{t}@{c}.{e}"),
            Expr::Fun(t, None, e) if f.alternate() => {
                write!(f, "fun_:{t}.")?;
                f.debug_set().entry(&DebugDisplay(&e)).finish()
            }
            Expr::Fun(t, None, e) => write!(f, "fun_:{t}.{e}"),
            Expr::Apply(e1, e2) if f.alternate() => f
                .debug_tuple("")
                .field(&DebugDisplay(&e1))
                .field(&DebugDisplay(&e2))
                .finish(),
            Expr::Apply(e1, e2) => write!(f, "({e1} {e2})"),
        }
    }
}

impl Display for Cap {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        enum C<'c> {
            Bind,
            Apply,
            FunRec,
            Fun(&'c Cap),
        }
        fn inner(c: &Cap, f: &mut Formatter<'_>) -> FmtResult {
            let mut f = f.debug_set();
            if c.bind {
                f.entry(&C::Bind);
            }
            if c.apply {
                f.entry(&C::Apply);
            }
            match &c.fun {
                Some(CapOpt::Inherit) => f.entry(&C::FunRec),
                Some(CapOpt::Set(c)) => f.entry(&C::Fun(c)),
                None => &mut f,
            };
            f.finish()
        }
        impl std::fmt::Debug for C<'_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
                match self {
                    C::Bind => f.write_str("bind = _"),
                    C::Apply => f.write_str("apply()"),
                    C::FunRec => f.write_str("fun() { _ }"),
                    C::Fun(c) => {
                        f.write_str("fun() ")?;
                        inner(c, f)
                    }
                }
            }
        }

        inner(self, f)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Type::Unit => f.write_str("()"),
            Type::Nat => f.write_str("nat"),
            Type::Arrow(t1, Some(c), t2) => write!(f, "({t1} -> {t2} @{c})"),
            Type::Arrow(t1, None, t2) => write!(f, "({t1} -> {t2})"),
        }
    }
}

impl Display for Ctx {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.0.len() == 0 {
            f.write_str("{}")
        } else {
            write!(f, "{}", &self.0[0])?;
            for t in &self.0[1..] {
                write!(f, ",{t}")?;
            }
            Ok(())
        }
    }
}

// builders and macros

impl SynExpr {
    fn lower(self) -> Expr {
        fn inner(stack: &mut Vec<&'static str>, e: SynExpr) -> Expr {
            match e {
                SynExpr::Unit => Expr::Unit,
                SynExpr::Var(x) => Expr::Var(
                    (stack.iter().rev().enumerate())
                        .find_map(|(i, y)| (x == *y).then(|| i))
                        .unwrap(),
                ),
                SynExpr::Nat(n) => Expr::Nat(n),
                SynExpr::Let(x, e1, e2) => {
                    let e1 = inner(stack, *e1);
                    stack.push(x);
                    let e2 = inner(stack, *e2);
                    Expr::Let(Box::new(e1), Box::new(e2))
                }
                SynExpr::Fun(x, t, e) => {
                    stack.push(x);
                    let e = inner(stack, *e);
                    stack.pop();
                    Expr::Fun(Box::new(t), None, Box::new(e))
                }
                SynExpr::Apply(e1, e2) => {
                    Expr::Apply(Box::new(inner(stack, *e1)), Box::new(inner(stack, *e2)))
                }
            }
        }
        inner(&mut vec![], self)
    }
}

fn main() {
    env_logger::init();
    let f = expr! { fun(x: ((1 -> 1) -> (1 -> 1))) {
        fun(y: (1 -> 1)) (x y)
    } };
    let h = expr! { fun(z: (1 -> 1)) z };
    let e = expr! {
        let f = (#f.clone()) in
        let h = (#h.clone()) in
        f h
    }
    .lower();
    let g: Ctx = Ctx(vec![]);
    let c = cap![apply(), bind = _, fun() { _ }];

    // let f = f.lower();
    // println!(
    //     "{{}} |- {f:#} : {:#}",
    //     type_synth(&g, &c, &f).expect("bad type")
    // );
    // let h = h.lower();
    // println!(
    //     "{{}} |- {h:#} : {:#}",
    //     type_synth(&g, &c, &h).expect("bad type")
    // );
    println!(
        "{{}} |- {e:#} : {:#}",
        type_synth(&g, &c, &e).expect("bad type")
    );
    print!("eval({e:#}) = ");
    println!("{:#}", eval(e));
}
