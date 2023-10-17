#![allow(unused)]

// my own attempts at combining `let` lex scopes and record types
// I guess this is "modules" but I'm not really familiar with
// module typing rules or languages.

// the combo of Bind and Comma types can be thought of as creating
// an anonymous record type. For field access `e.x` to type check
// `e` must type check as a record containing a binding of `x = ?`.

// I thought of trying to identify bindings using DeBruijn indices,
// but I'm not actually doing that much in terms of type-equality,
// so I don't need the alpha-equivalence. Replacing string idents
// with numeric indices turns the record types into tuples. So
// `e.x` would become `e.n`. Maybe something to try next.
// The current rules ignore any types that aren't `x:t` when
// constructing comma types `t1,t2`, but if we leave them in, we
// could probably index both by number and string ident.
//    {x = {}}.x == {x = {}}.0
//    {x = {}, {}}.1 == {}
// This doesn't cover cases where I actually want the order of
// fields to matter, for example with C structs
//    struct { int i; char c; }  !=  struct { char c; int i; }
// even if `e.i : int` for both. Generally I want anonymous structs
// about as much as a I want tuples: nice for moving things around
// in a contained lexical scope, but I don't really want to be
// passing them all around a program, because it's not obvious
// what `e` has available just by looking at it, and having a type
// of `x0:t0,x1:t1,x2:y1:t2,...` is not that much more helpful.

use log::debug;
use std::collections::HashMap as Map;
use std::rc::Rc;

#[derive(Clone, Debug)]
enum Term {
    Unit,
    Nat(usize),
    Var(String),
    Let(String, Rc<Term>),
    Par(Rc<Term>),
    Comma(Rc<Term>, Rc<Term>),
    Period(Rc<Term>, Rc<Term>),
    Sub(Rc<Term>, String),
    Fun(Rc<Type>, Rc<Term>),
    Apply(Rc<Term>, Rc<Term>),
}

#[derive(Clone, Debug)]
enum Type {
    UnitT,
    NatT,
    Bind(String, Rc<Type>),
    Pair(Rc<Type>, Rc<Type>),
    Arrow(Rc<Type>, Rc<Type>),
}

#[derive(Clone, Debug)]
struct Ctx(Map<String, Rc<Type>>);

impl Ctx {
    fn new() -> Self {
        Ctx(Map::new())
    }
    fn proj(&self, x: &str) -> Option<&Type> {
        self.0.get(x).map(|x| x.as_ref())
    }

    fn extend(&self, t: Type) -> Self {
        fn bind(ctx: &mut Ctx, t: &Type) {
            match t {
                Type::Bind(x, t) => {
                    ctx.0.insert(x.clone(), t.clone());
                }
                _ => {}
            }
        }
        match t {
            Type::Bind(_, _) => {
                let mut g = self.clone();
                bind(&mut g, &t);
                g
            }
            Type::Pair(hd, tl) => {
                let mut g = self.clone();
                bind(&mut g, &hd);
                let g = g.extend((*tl).clone());
                g
            }
            _ => self.clone(),
        }
    }
}

fn type_synth(g: &Ctx, e: &Term) -> Option<Type> {
    debug!("type_synth {g} |- {e} : ??");
    match e {
        //
        // ------------
        // G |- {} : {}
        Term::Unit => Some(Type::UnitT),
        // ----------
        // G |- n : N
        Term::Nat(_) => Some(Type::NatT),
        // x:t \in G
        // ----------
        // G |- x : t
        Term::Var(x) => g.proj(x).cloned(),
        // G |- e : t
        // -------------------
        // G |- x = e : x:t
        Term::Let(x, e) => {
            let t = type_synth(g, e)?;
            Some(Type::Bind(x.clone(), Rc::new(t)))
        }
        // G |- e : t
        // ------------
        // G |- {e} : t
        Term::Par(e) => type_synth(g, e),
        // G |- e1 : t1
        // G,t1 |- e2 : t2
        // --------------------
        // G |- e1, e2 : t1, t2
        Term::Comma(e1, e2) => {
            let t1 = type_synth(g, e1)?;
            let g2 = g.extend(t1.clone());
            let t2 = type_synth(&g2, e2)?;
            Some(Type::Pair(Rc::new(t1), Rc::new(t2)))
        }
        // G |- e1 : t1
        // G,t1 |- e2 : t2
        // ----------------
        // G |- e1. e2 : t2
        Term::Period(e1, e2) => {
            let t1 = type_synth(g, e1)?;
            let g2 = g.extend(t1);
            let t2 = type_synth(&g2, e2)?;
            Some(t2)
        }
        // G |- e : t1
        // x:t \in t1
        // ------------
        // G |- e.x : t
        Term::Sub(e, x) => {
            let t = type_synth(g, e)?;
            fn proj(t: &Type, x: &str) -> Option<Type> {
                match t {
                    Type::Bind(y, t) if y == x => Some((**t).clone()),
                    Type::Pair(hd, tl) => proj(hd, x).or_else(|| proj(tl, x)),
                    _ => None,
                }
            }
            proj(&t, x)
        }

        // G,t1 |- e: t2
        // --------------------
        // G |- \t1.e: t1 -> t2
        Term::Fun(t, e) => {
            let g = g.extend((**t).clone());
            let t2 = type_synth(&g, e)?;
            Some(Type::Arrow(t.clone(), Rc::new(t2)))
        }
        // G |- e1: t1 -> t
        // G |- e2: t2
        // |- t1 := t2
        // ----------------
        // G |- e1(e2) : t
        Term::Apply(e1, e2) => {
            let t1 = type_synth(g, e1)?;
            if let Type::Arrow(t1, t) = t1 {
                let t2 = type_synth(g, e2)?;
                type_coerce(&t1, &t2)?;
                Some((*t).clone())
            } else {
                None
            }
        }
    }
}

/// this is not transitive
/// x:t := t and t := x:t, but 'y:t := x:t' is not true
fn type_coerce(t1: &Type, t2: &Type) -> Option<()> {
    match (t1, t2) {
        // |- {} := {}
        (Type::UnitT, Type::UnitT) => Some(()),
        (Type::NatT, Type::NatT) => Some(()),
        // |- t1 := t2
        // -------------------
        // |- x: t1 := x := t2
        (Type::Bind(x, t1), Type::Bind(y, t2)) => {
            if (x == y) {
                type_coerce(t1, t2)
            } else {
                None
            }
        }
        // |- t1 := t3
        // |- t2 := t4
        // -----------------
        // |- t1,t2 := t3,t4
        (Type::Pair(t1, t2), Type::Pair(t3, t4)) => {
            type_coerce(t1, t3)?;
            type_coerce(t2, t4)
        }
        // |- t3 := t1
        // |- t2 := t4
        // -------------------------
        // |- t1 -> t2  :=  t3 -> t4
        //
        // |- x:{} -> y:{}  :=  {} -> {}
        // . |- {} := x:{}
        // . |- y:{} := {}
        (Type::Arrow(t1, t2), Type::Arrow(t3, t4)) => {
            type_coerce(t3, t1)?;
            type_coerce(t2, t4)
        }
        // t2 != x: t3      t1 != x: t3
        // |- t1 := t2      |- t1 := t2
        // --------------   --------------
        // |- x: t1 := t2   |- t1 := x: t2
        (Type::Bind(x, t1), t2) => type_coerce(t1, t2),
        (t1, Type::Bind(x, t2)) => type_coerce(t1, t2),
        _ => None,
    }
}

#[derive(Clone)]
struct Scope(Map<String, Term>);

impl Scope {
    fn new() -> Self {
        Scope(Map::new())
    }

    fn proj(&self, x: &str) -> Option<&Term> {
        self.0.get(x)
    }

    fn bind(mut self, x: String, e: Term) -> Self {
        self.0.insert(x, e);
        self
    }

    fn extend(mut self, rhs: Scope) -> Self {
        self.0.extend(rhs.0);
        self
    }
}

impl Term {
    fn proj(&self, x: &str) -> Option<&Term> {
        match self {
            Term::Let(y, e) if x == y => Some(e),
            Term::Comma(hd, tl) => match tl.proj(x) {
                Some(e) => Some(e),
                None => match &**hd {
                    Term::Let(y, e) if x == y => Some(e),
                    _ => None,
                },
            },
            _ => None,
        }
    }
}

fn eval(s: &Scope, e: &Term) -> (Scope, Term) {
    debug!("eval {s}({e}) --> ??");
    let mut s1 = Scope::new();
    match e {
        //
        // ------------------
        // s({}) --> ({}; {})
        Term::Unit => (s1, Term::Unit),
        //
        Term::Nat(n) => (s1, Term::Nat(*n)),
        // x=v \in s           x=v \nin s
        // ----------------    ----------------
        // s(x) --> ({}; v)    s(x) --> ({}; x)
        Term::Var(x) => (
            s1,
            match s.proj(x) {
                Some(e) => e.clone(),
                None => Term::Var(x.clone()),
            },
        ),
        // s(e) --> (s_e; v)
        // ----------------------
        // s(x=e) --> (x=v ; x=v)
        Term::Let(x, e) => {
            let (_, v) = eval(s, e);
            let s1 = s1.bind(x.clone(), v.clone());
            (s1, Term::Let(x.clone(), Rc::new(v)))
        }
        // s(e) --> (s_e; v)
        // ------------------
        // s({e}) --> ({}; v)
        Term::Par(e) => {
            let (_, v) = eval(s, e);
            (s1, v)
        }
        // s(e1) --> (s1 ; v1)
        // (s,s1)(e2) --> (s2 ; v2)
        // -----------------------------
        // s(e1,e2) --> (s1,s2 ; v1,v2)
        Term::Comma(e1, e2) => {
            let (s1, v1) = eval(s, e1);
            let s = s.clone().extend(s1.clone());
            let (s2, v2) = eval(&s, e2);
            (s1.extend(s2), Term::Comma(Rc::new(v1), Rc::new(v2)))
        }
        // s(e1) --> (s1 ; v1)
        // (s,s1)(e2) --> (s2 ; v2)
        // ------------------------
        // s(e1. e2) --> (s2 ; v2)
        Term::Period(e1, e2) => {
            let (s1, v1) = eval(s, e1);
            let s = s.clone().extend(s1.clone());
            eval(&s, e2)
        }
        // s(e) --> (s_e ; v_e)
        // x=v \in v_e
        // --------------------
        // s(e.x) --> ({} ; v)
        Term::Sub(e, x) => {
            let (se, ve) = eval(s, e);
            let v = ve.proj(x).expect("bad type");
            (s1, v.clone())
        }

        // (s-t)(e) --> (s1, e1)
        // -----------------------
        // s(\t.e) --> ({} ; \t.e1)
        Term::Fun(t, e) => {
            fn rmvars<'t>(s: &mut Scope, t: &'t Type) {
                match t {
                    Type::Bind(x, _) => {
                        s.0.remove(x);
                    }
                    Type::Pair(t1, t2) => {
                        rmvars(s, t1);
                        rmvars(s, t2);
                    }
                    _ => {}
                }
            }
            let mut s = s.clone();
            rmvars(&mut s, t);
            let (_, e1) = eval(&s, e);
            (s1, Term::Fun(t.clone(), Rc::new(e1)))
        }
        // s(e1) --> (s1 ; \t.e)
        // s(e2) --> (s2 ; v2)
        // vc = val_coerce(t, v2)
        // ({},vc)(e) --> (sv, v)
        // ----------------------
        // s(e1(e2)) --> ({}, v)
        Term::Apply(e1, e2) => {
            let (s1, v1) = eval(s, e1);
            match v1 {
                Term::Fun(t, e) => {
                    let (s2, v2) = eval(s, e2);
                    (Scope::new(), fun_apply(&t, &e, &v2).1)
                }
                _ => unreachable!("bad type"),
            }
        }
    }
}

fn fun_apply(t: &Type, e1: &Term, e2: &Term) -> (Scope, Term) {
    debug!("fun_apply {t} {e1} {e2}");
    fn inner(mut s: Scope, e: &Term, t: &Type) -> Scope {
        match t {
            Type::Bind(x, t) => match e {
                Term::Let(y, v) => {
                    if x == y {
                        s.bind(y.clone(), (**v).clone())
                    } else {
                        unreachable!("bad type");
                    }
                }
                e => s.bind(x.clone(), e.clone()),
            },
            Type::Pair(t1, t2) => match e {
                Term::Comma(e1, e2) => {
                    let mut s = inner(s, e1, t1);
                    inner(s, e2, t2)
                }
                _ => unreachable!("bad type: pair ({t}) expected comma, got {e}"),
            },
            _ => s,
        }
    }
    let s = inner(Scope::new(), e2, t);
    eval(&s, &e1)
}

use std::fmt::Display;

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn disp(e: &Term, f: &mut std::fmt::Formatter, par: bool) -> std::fmt::Result {
            match e {
                Term::Unit => f.write_str("{}"),
                Term::Nat(n) => write!(f, "{n}"),
                Term::Var(x) => f.write_str(x),
                Term::Let(x, e) if par => write!(f, "({x} = {})", Par(e)),
                Term::Let(x, e) => write!(f, "{x} = {}", Par(e)),
                Term::Par(e) => write!(f, "{{{e}}}"),
                Term::Comma(e1, e2) if par && matches!(**e1, Term::Comma(_, _)) => {
                    write!(f, "({}, {e2})", Par(e1))
                }
                Term::Comma(e1, e2) if par => write!(f, "({e1}, {e2})"),
                Term::Comma(e1, e2) if matches!(**e1, Term::Comma(_, _)) => {
                    write!(f, "{}, {e2}", Par(e1))
                }
                Term::Comma(e1, e2) => write!(f, "{e1}, {e2}"),
                Term::Period(e1, e2) => {
                    if par {
                        f.write_str("(")?;
                    }
                    let par1 = !matches!(&**e1, Term::Let(_, _) | Term::Comma(_, _));
                    disp(e1, f, par1)?;
                    f.write_str(". ")?;
                    let par2 = !matches!(
                        &**e2,
                        Term::Let(_, _) | Term::Period(_, _) | Term::Comma(_, _)
                    );
                    disp(e2, f, par2)?;
                    if par {
                        f.write_str(")")?;
                    }
                    Ok(())
                }
                Term::Sub(e, x) => write!(f, "{}_{x}", Par(e)),
                Term::Fun(t, e) => write!(f, "λ{{{t}. {e}}}"),
                Term::Apply(e1, e2) => write!(f, "{e1}({e2})"),
            }
        }
        struct Par<'e>(&'e Term);
        impl Display for Par<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                disp(self.0, f, true)
            }
        }
        disp(self, f, false)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn disp(t: &Type, f: &mut std::fmt::Formatter, par: bool) -> std::fmt::Result {
            match t {
                Type::UnitT => f.write_str("{}"),
                Type::NatT => f.write_str("ℕ"),
                Type::Bind(x, t) => {
                    write!(f, "{x}:{t}")
                }
                Type::Pair(hd, tl) => {
                    if par {
                        f.write_str("(")?;
                    }
                    disp(hd, f, !matches!(&**hd, Type::Bind(_, _)))?;
                    write!(f, ", ")?;
                    disp(tl, f, !matches!(&**tl, Type::Bind(_, _) | Type::Pair(_, _)))?;
                    if par {
                        f.write_str(")")?;
                    }
                    Ok(())
                }
                Type::Arrow(t1, t2) => {
                    if par {
                        f.write_str("(")?;
                    }
                    disp(t1, f, true)?;
                    f.write_str(" -> ")?;
                    disp(t2, f, false)?;
                    if par {
                        f.write_str(")")?
                    }
                    Ok(())
                }
            }
        }
        disp(self, f, false)
    }
}

impl Display for Ctx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.len() == 0 {
            return f.write_str("{}");
        }
        for (c, (x, t)) in std::iter::once("")
            .chain(std::iter::repeat(","))
            .zip(self.0.iter())
        {
            write!(f, "{c}{x}:({t})")?;
        }
        Ok(())
    }
}

impl Display for Scope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.len() == 0 {
            return f.write_str("{}");
        }
        for (c, (x, e)) in std::iter::once("")
            .chain(std::iter::repeat(","))
            .zip(self.0.iter())
        {
            write!(f, "{c}{x}={e}")?;
        }
        Ok(())
    }
}

fn main() {
    env_logger::init();

    use {Ctx as G, Scope as S, Term::*, Type::*};
    fn rc<T>(v: T) -> Rc<T> {
        Rc::new(v)
    }
    let g = G::new();
    let e = Par(rc(Comma(
        rc(Let(
            "x".to_string(),
            rc(Par(rc(Let("y".to_string(), rc(Unit))))),
        )),
        rc(Sub(rc(Var("x".to_string())), "y".to_string())),
    )));
    let t = type_synth(&g, &e).expect("bad type");
    println!("{g} |- {e} : {t}");

    let s = Scope::new();
    let (s1, v) = eval(&s, &e);
    println!("{s}({e}) --> ({} ; {})", s1, v);

    let f = Fun(
        rc(Pair(
            rc(Bind("x".to_string(), rc(UnitT))),
            rc(Arrow(
                rc(Bind("y".to_string(), rc(UnitT))),
                rc(Bind("z".to_string(), rc(NatT))),
            )),
        )),
        rc(Comma(
            rc(Let("x".to_string(), rc(Var("x".to_string())))),
            rc(Nat(7)),
        )),
    );
    let e = Period(
        rc(Comma(
            rc(Let("f".to_string(), rc(f))),
            rc(Let(
                "y".to_string(),
                rc(Comma(
                    rc(Let("x".to_string(), rc(Unit))),
                    rc(Fun(rc(UnitT), rc(Let("z".to_string(), rc(Nat(42)))))),
                )),
            )),
        )),
        rc(Apply(rc(Var("f".to_string())), rc(Var("y".to_string())))),
    );
    println!("{e}");
    let t = type_synth(&g, &e).expect("bad type");
    println!("{t}");
    let s = Scope::new();
    let (s, v) = eval(&s, &e);
    println!("{{}}({e}) --> ({s} ; {v})");
}
