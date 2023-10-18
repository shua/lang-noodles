#![allow(unused)]

use std::rc::Rc;

#[derive(Clone)]
struct Record<V>(String, Rc<V>, Vec<(String, Rc<V>)>);

#[derive(Clone)]
enum Term {
    /// {}
    Unit,
    /// n
    Nat(usize),
    /// x
    Var(String),
    /// {x_i:t_i}_(i in I)
    Record(Record<Self>),
    /// e.x
    Proj(Rc<Self>, String),
    /// \x:t+c.e
    Fun(String, Rc<Type>, Cap, Rc<Self>),
    /// e(e)
    Apply(Rc<Self>, Rc<Self>),
}

#[derive(Clone)]
enum Type {
    Unit,
    Nat,
    Record(Record<Self>),
    Arrow(Rc<Self>, Cap, Rc<Self>),
}

#[derive(Clone)]
enum Cap0 {
    Bind,
    Apply,
    Fun(Rc<Cap>),
}

#[derive(Clone)]
enum Cap {
    Empty,
    Inherit,
    Cons(Cap0, Rc<Self>),
}

impl<V> Record<V> {
    fn new<I: Iterator<Item = (String, V)>>(x0: String, v0: V, it: I) -> Self {
        Record(x0, Rc::new(v0), it.map(|(x, v)| (x, Rc::new(v))).collect())
    }
    fn push(&mut self, x: String, e: V) {
        self.2.push((x, Rc::new(e)));
    }

    fn get(&self, x: &str) -> Option<Rc<V>> {
        if x == self.0 {
            Some(self.1.clone())
        } else {
            let e = self.2.iter().find(|(y, e)| y == x)?.1.clone();
            Some(e)
        }
    }

    fn try_map<T, F: FnMut(&str, Rc<V>) -> Option<T>>(&self, mut f: F) -> Option<Record<T>> {
        let t0 = f(&self.0, self.1.clone())?;
        let mut tl = vec![];
        for (x, v) in self.2.iter() {
            let t = f(x, v.clone())?;
            tl.push((x.to_string(), t));
        }
        Some(Record::new(self.0.to_string(), t0, tl.into_iter()))
    }

    fn map_reduce<
        T,
        F0: for<'s> FnOnce(&'s str, Rc<V>) -> T,
        F: for<'s> Fn(T, &'s str, Rc<V>) -> T,
    >(
        &self,
        f0: F0,
        f: F,
    ) -> T {
        let mut ret = f0(&self.0, self.1.clone());
        for (x, e) in &self.2 {
            ret = f(ret, x, e.clone())
        }
        ret
    }

    fn iter(&self) -> impl Iterator<Item = (&str, Rc<V>)> {
        std::iter::once((self.0.as_str(), self.1.clone()))
            .chain(self.2.iter().map(|(x, v)| (x.as_str(), v.clone())))
    }
}

impl Cap {
    fn empty_tail() -> Rc<Self> {
        static mut EMPTY: std::mem::MaybeUninit<Rc<Cap>> = std::mem::MaybeUninit::uninit();
        static EMPTY_ONCE: std::sync::Once = std::sync::Once::new();

        EMPTY_ONCE.call_once(|| unsafe {
            EMPTY.write(Rc::new(Cap::Empty));
        });
        unsafe { EMPTY.assume_init_ref().clone() }
    }

    fn bind() -> Self {
        Cap::Cons(Cap0::Bind, Self::empty_tail())
    }

    fn apply() -> Self {
        Cap::Cons(Cap0::Apply, Self::empty_tail())
    }

    fn fun(c: &Cap) -> Self {
        Cap::Cons(Cap0::Fun(Rc::new(c.clone())), Rc::new(Self::Inherit))
    }

    fn grounded(&self) -> bool {
        match self {
            Cap::Empty => true,
            Cap::Inherit => false,
            Cap::Cons(_, tl) => tl.grounded(),
        }
    }
}

#[derive(Clone)]
enum Ctx {
    Empty,
    Bind(String, Rc<Type>, Rc<Self>),
}

impl Ctx {
    fn bind(&self, x: String, t: Type) -> Self {
        Ctx::Bind(x, Rc::new(t), Rc::new(self.clone()))
    }

    fn proj(&self, x: &str) -> Option<&Type> {
        match self {
            Ctx::Empty => None,
            Ctx::Bind(y, t, tl) => {
                if x == y {
                    Some(t.as_ref())
                } else {
                    tl.proj(x)
                }
            }
        }
    }
}

/// c |- c1 <= c2
fn cap_sub(amb: &Cap, c1: &Cap, c2: &Cap) -> Option<()> {
    fn cap_sub0(amb: &Cap, c1: &Cap, c0: &Cap0) -> Option<()> {
        match (c1, c0) {
            (Cap::Empty, _) => None,
            (Cap::Inherit, c0) => {
                if !amb.grounded() {
                    panic!("ambient capability must be grounded");
                }
                cap_sub0(amb, amb, c0)
            }
            (Cap::Cons(Cap0::Bind, _), Cap0::Bind) => Some(()),
            (Cap::Cons(Cap0::Apply, _), Cap0::Apply) => Some(()),
            (Cap::Cons(Cap0::Fun(c1), _), Cap0::Fun(c2)) => cap_sub(amb, c1, &c2),
            (Cap::Cons(_, tl), c0) => cap_sub0(amb, tl, c0),
        }
    }
    match (c1, c2) {
        (_, Cap::Empty) => Some(()),
        (Cap::Empty, Cap::Cons(_, _)) => None,
        (Cap::Inherit, Cap::Inherit) => Some(()),
        (Cap::Inherit, c2) => {
            if !amb.grounded() {
                panic!("ambient capability must be grounded");
            }
            cap_sub(amb, amb, c2)
        }
        (c1, Cap::Inherit) => {
            if !amb.grounded() {
                panic!("ambient capability must be grounded");
            }
            cap_sub(amb, c1, amb)
        }
        (c1, Cap::Cons(hd, tl)) => {
            cap_sub0(amb, c1, hd)?;
            cap_sub(amb, c1, tl)
        }
    }
}

fn type_synth(g: &Ctx, c: &Cap, e: &Term) -> Option<Type> {
    match e {
        Term::Unit => Some(Type::Unit),
        Term::Nat(_) => Some(Type::Nat),
        Term::Var(x) => g.proj(x).cloned(),
        Term::Record(r) => {
            let mut g = g.clone();
            let tr = r.try_map(|x0: &str, e0| {
                let t = type_synth(&g, c, &e0)?;
                let g2 = g.bind(x0.to_string(), t.clone());
                g = g2;
                Some(t)
            })?;
            Some(Type::Record(tr))
        }
        Term::Proj(e, x) => {
            let t = type_synth(g, c, e)?;
            match t {
                Type::Record(r) => r.get(x).map(|t| (*t).clone()),
                _ => None,
            }
        }
        Term::Fun(x, t, c1, e) => {
            cap_sub(c, &Cap::fun(c1), c)?;
            let g2 = g.bind(x.clone(), (**t).clone());
            let t2 = type_synth(&g2, c1, e)?;
            Some(Type::Arrow(t.clone(), c1.clone(), Rc::new(t2)))
        }
        // G;c |- e1 : t2 c1-> t
        // G;c |- e2 : t3
        // G;c |- t3 <: t2
        // ----------------------
        // G;c |- e1(e2) : t
        Term::Apply(e1, e2) => {
            cap_sub(c, &Cap::apply(), c)?;
            let t1 = type_synth(g, c, e1)?;
            match t1 {
                Type::Arrow(t2, c1, t) => {
                    let t3 = type_synth(g, c, e2)?;
                    type_sub(g, c, &t3, &t2)?;
                    Some((*t).clone())
                }
                _ => None,
            }
        }
    }
}

fn type_sub(g: &Ctx, c: &Cap, t1: &Type, t2: &Type) -> Option<()> {
    match (t1, t2) {
        //
        // -------------
        // G;c |- 1 <: 1
        // G;c |- N <: N
        (Type::Unit, Type::Unit) => Some(()),
        (Type::Nat, Type::Nat) => Some(()),
        // this is not a packed struct like C
        // where order matters
        //
        // for all x_i:t1_i \in t1
        //   . x_i:t2_i \in t2
        //     /\ G;c |- t1_i <: t2_i
        // -------------------------------------------
        // G;c |- {x_i:t1_i} <: {y_j:t2_j}
        (Type::Record(r1), Type::Record(r2)) => r1
            .try_map(|x, t1| -> Option<_> {
                let t2 = r2.get(x)?;
                type_sub(g, c, &t1, &t2)
            })
            .and(Some(())),
        // G;c |- t3 <: t1
        // c |- c1 <: c2
        // G;c |- t2 <: t4
        // ---------------------------------
        // G;c |- t1 c1-> t2  <:  t3 c2-> t4
        (Type::Arrow(t1, c1, t2), Type::Arrow(t3, c2, t4)) => {
            type_sub(g, c, t3, t1)?;
            cap_sub(c, c1, c2)?;
            type_sub(g, c, t2, t4)
        }
        _ => None,
    }
}

use std::collections::HashMap as Map;

#[derive(Clone)]
struct Env(Map<String, Term>, Cap);

impl Env {
    fn new() -> Self {
        Env(Map::new(), Cap::Empty)
    }
    fn bind(self, x: String, e: Term) -> Self {
        let mut ret = self.clone();
        ret.0.insert(x, e);
        ret
    }

    fn extend(mut self, rhs: Self) -> Self {
        self.0.extend(rhs.0);
        // ignore caps
        self
    }
}

fn term_eval(s: &Env, e: Term) -> Term {
    fn cap_ground(s: &Env, c: Cap) -> Cap {
        match c {
            Cap::Empty => Cap::Empty,
            Cap::Inherit => s.1.clone(),
            Cap::Cons(c0, tl) => Cap::Cons(c0, Rc::new(cap_ground(s, (*tl).clone()))),
        }
    }
    match e {
        // (s,c)({}) --> {}
        Term::Unit => Term::Unit,
        // (s,c)(n) --> n
        Term::Nat(n) => Term::Nat(n),
        // x=v \in s
        // --------------
        // (s,c)(x) --> v
        Term::Var(x) => s.0.get(&x).unwrap().clone(),
        // (s,c)(e_0) --> v_0
        // (s,x_0=v_0,...x_j=v_j,c)(e_j+1) --> v_j+1
        // -----------------------------------------
        // (s,c)({x_i=e_i}) --> {x_i=v_i}
        Term::Record(r) => {
            let mut s = s.clone();
            let r = r
                .try_map(|x, e| {
                    let v = term_eval(&s, (*e).clone());
                    s = s.clone().bind(x.to_string(), v.clone());
                    Some(v)
                })
                .expect("bad type");
            Term::Record(r)
        }
        // (s,c)(e) --> {x_i=v_i}
        // x=v \in {x_i=v_i}
        // ----------------------
        // (s,c)(e.x) --> v
        Term::Proj(e, x) => {
            let v = term_eval(s, (*e).clone());
            match v {
                Term::Record(r) => (*r.get(&x).expect("bad type")).clone(),
                _ => panic!("bad type"),
            }
        }
        // c(c1) --> c2
        // ------------------------------
        // (s,c)(\x:t+c1.e) --> \x:t+c2.e
        Term::Fun(x, t, c, e) => {
            let c = cap_ground(s, c.clone());
            Term::Fun(x, t, c, e)
        }
        // (s,c)(e1) --> \x:t+c1.e
        // (s,c)(e2) --> v2
        // c1 \subset c
        // (s,x=v2,c1)(e) --> v
        // -----------------------
        // (s,c)(e1(e2)) --> v
        Term::Apply(e1, e2) => {
            let v1 = term_eval(s, (*e1).clone());
            match v1 {
                Term::Fun(x, _t, _c, e) => {
                    let v2 = term_eval(s, (*e2).clone());
                    let mut s1 = s.clone().bind(x, v2);
                    // do we want to update s1.1 to c from function? This changes ambient capabilities inside e
                    // and affects mostly how caps in fun values are grounded
                    let v = term_eval(&s1, (*e).clone());
                    v
                }
                _ => panic!("bad type"),
            }
        }
    }
}

fn main() {}
