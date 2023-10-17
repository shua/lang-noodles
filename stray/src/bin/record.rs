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
    Var(String),
    Let(String, Rc<Term>),
    Par(Rc<Term>),
    Comma(Rc<Term>, Rc<Term>),
    Dot(Rc<Term>, String),
}

#[derive(Clone, Debug)]
enum Type {
    Unit,
    Comma(Rc<Type>, Rc<(String, Type)>),
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
        match t {
            Type::Unit => self.clone(),
            Type::Comma(hd, tl) => {
                let mut g = self.extend((*hd).clone());
                g.0.insert(tl.0.clone(), Rc::new(tl.1.clone()));
                g
            }
        }
    }
}

impl Type {
    fn cons(self, x: String, t: Type) -> Type {
        Type::Comma(Rc::new(self), Rc::new((x, t)))
    }

    fn append(self, rhs: &Type) -> Type {
        match rhs {
            Type::Unit => self,
            Type::Comma(hd, tl) => Type::Comma(Rc::new(self.append(hd)), tl.clone()),
        }
    }
}

fn type_synth(g: &Ctx, e: &Term) -> Option<Type> {
    debug!("type_synth {g} |- {e} : ??");
    match e {
        //
        // ------------
        // G |- {} : {}
        Term::Unit => Some(Type::Unit),
        // x:t \in G
        // ----------
        // G |- x : t
        Term::Var(x) => g.proj(x).cloned(),
        // G |- e : t
        // -------------------
        // G |- x = e : {},x:t
        Term::Let(x, e) => {
            let t = type_synth(g, e)?;
            Some(Type::Comma(Rc::new(Type::Unit), Rc::new((x.clone(), t))))
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
            Some(t1.append(&t2))
        }
        // G |- e : t1
        // x:t \in t1
        // ------------
        // G |- e.x : t
        Term::Dot(e, x) => {
            let t = type_synth(g, e)?;
            fn proj(t: &Type, x: &str) -> Option<Type> {
                match t {
                    Type::Unit => None,
                    Type::Comma(_, tl) if tl.0 == x => Some(tl.1.clone()),
                    Type::Comma(hd, _) => proj(hd, x),
                }
            }
            proj(&t, x)
        }
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
        // s(e1,e2) --> s(s1,s2 ; v1,v2)
        Term::Comma(e1, e2) => {
            let (s1, v1) = eval(s, e1);
            let s = s.clone().extend(s1.clone());
            let (s2, v2) = eval(&s, e2);
            (s1.extend(s2), Term::Comma(Rc::new(v1), Rc::new(v2)))
        }
        // s(e) --> (s_e ; v_e)
        // x=v \in v_e
        // --------------------
        // s(e.x) --> ({} ; v)
        Term::Dot(e, x) => {
            let (se, ve) = eval(s, e);
            let v = ve.proj(x).expect("bad type");
            (s1, v.clone())
        }
    }
}

use std::fmt::Display;

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn disp(e: &Term, f: &mut std::fmt::Formatter, par: bool) -> std::fmt::Result {
            match e {
                Term::Unit => f.write_str("{}"),
                Term::Var(x) => f.write_str(x),
                Term::Let(x, e) if par => write!(f, "({x} = {})", Par(e)),
                Term::Let(x, e) => write!(f, "{x} = {}", Par(e)),
                Term::Par(e) => write!(f, "{{{e}}}"),
                Term::Comma(e1, e2) if par && matches!(**e1, Term::Comma(_, _)) => {
                    write!(f, "({},{})", Par(e1), Par(e2))
                }
                Term::Comma(e1, e2) if par => write!(f, "({e1},{})", Par(e2)),
                Term::Comma(e1, e2) if matches!(**e1, Term::Comma(_, _)) => {
                    write!(f, "{},{}", Par(e1), Par(e2))
                }
                Term::Comma(e1, e2) => write!(f, "{e1},{}", Par(e2)),
                Term::Dot(e, x) => write!(f, "{}.{x}", Par(e)),
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
                Type::Unit => f.write_str("{}"),
                Type::Comma(hd, tl) => {
                    if par {
                        f.write_str("(")?;
                    }
                    disp(hd, f, true)?;
                    write!(f, ",{}:", tl.0)?;
                    disp(&tl.1, f, true)?;
                    if par {
                        f.write_str(")")?;
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

    use {Ctx as G, Scope as S, Term as E, Type as T};
    fn rc<T>(v: T) -> Rc<T> {
        Rc::new(v)
    }
    let g = G::new();
    let e = E::Par(rc(E::Comma(
        rc(E::Let(
            "x".to_string(),
            rc(E::Par(rc(E::Let("y".to_string(), rc(E::Unit))))),
        )),
        rc(E::Dot(rc(E::Var("x".to_string())), "y".to_string())),
    )));
    let t = type_synth(&g, &e).expect("bad type");
    println!("{g} |- {e} : {t}");

    let s = Scope::new();
    let (s1, v) = eval(&s, &e);
    println!("{s}({e}) --> ({} ; {})", s1, v);
}
