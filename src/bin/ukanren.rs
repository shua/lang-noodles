#![allow(unused)]

// http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf

use std::any::Any;
use std::cmp::PartialEq;
use std::fmt::Debug;
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq)]
enum Var {
    N(usize),
    X(&'static str),
}
impl Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Var::N(x) => write!(f, "_{x}"),
            Var::X(n) => write!(f, "'{n}'"),
        }
    }
}
trait Term: Debug {
    fn any(&self) -> &dyn Any;
    fn eq_term(&self, rhs: &dyn Term) -> bool;
}
impl<T: Debug + Any + PartialEq> Term for T {
    fn any(&self) -> &dyn Any {
        self
    }
    fn eq_term(&self, rhs: &dyn Term) -> bool {
        rhs.any().downcast_ref::<Self>() == Some(self)
    }
}
type RcTerm = Rc<dyn Term>;
type Subst = (Var, RcTerm);
type State = (Vec<Subst>, usize);
enum Stream {
    Nil,
    Now(State, Box<Self>),
    Later(Box<dyn FnOnce() -> Self>),
}

impl Stream {
    fn join(self, s2: Stream) -> Stream {
        match (self, s2) {
            (Stream::Nil, s) | (s, Stream::Nil) => s,
            (Stream::Now(hd, s1), s2) | (s2, Stream::Now(hd, s1)) => {
                Stream::Now(hd, Box::new(s1.join(s2)))
            }
            (Stream::Later(s1), Stream::Later(s2)) => {
                Stream::Later(Box::new(move || s1().join(s2())))
            }
        }
    }

    fn flat_map<F: (Fn(State) -> Stream) + 'static>(self, f: F) -> Stream {
        match self {
            Stream::Nil => Stream::Nil,
            Stream::Now(sc, s2) => {
                let s1 = f(sc);
                s1.join((*s2).flat_map(f))
            }
            Stream::Later(s) => Stream::Later(Box::new(move || s().flat_map(f))),
        }
    }
}

impl std::iter::Iterator for Stream {
    type Item = State;
    fn next(&mut self) -> Option<State> {
        match std::mem::replace(self, Stream::Nil) {
            Stream::Nil => None,
            Stream::Now(sc, s) => {
                *self = *s;
                Some(sc)
            }
            Stream::Later(s) => {
                *self = s();
                self.next()
            }
        }
    }
}

enum Goal {
    Fresh(Rc<dyn Fn(Var) -> Self>),
    Disj(Rc<Self>, Rc<Self>),
    Conj(Rc<Self>, Rc<Self>),
    Equal(RcTerm, RcTerm),
    Fn(Rc<dyn Fn(State) -> Stream>),
}

fn as_var(u: &dyn Term) -> Option<Var> {
    u.any().downcast_ref().copied()
}
fn walk(u: &RcTerm, s: &State) -> RcTerm {
    let f = || {
        let v: Var = as_var(&**u)?;
        let (_, t) = s.0.iter().find(|&&(w, _)| (w == v))?;
        Some(walk(t, s))
    };
    f().unwrap_or_else(|| u.clone())
}

impl Goal {
    fn query(&self, sc: State) -> Stream {
        match self {
            Goal::Fresh(f) => {
                let (s, c) = sc;
                f(Var::N(c)).query((s, c + 1))
            }
            Goal::Disj(g1, g2) => g1.query(sc.clone()).join(g2.query(sc)),
            Goal::Conj(g1, g2) => {
                let s = g1.query(sc);
                let g2 = g2.clone();
                s.flat_map(move |sc| g2.query(sc))
            }
            Goal::Equal(u, v) => {
                fn unify(u: &RcTerm, v: &RcTerm, mut s: State) -> Option<State> {
                    let (u, v) = (walk(u, &s), walk(v, &s));
                    let ext_s = |v, t, mut s: State| {
                        s.0.push((v, t));
                        s
                    };
                    match (as_var(&*u), as_var(&*v)) {
                        _ if u.eq_term(&*v) => Some(s),
                        (Some(u), _) => Some(ext_s(u, v, s)),
                        (_, Some(v)) => Some(ext_s(v, u, s)),
                        _ => None,
                    }
                }
                if let Some(sc) = unify(u, v, sc) {
                    Stream::Now(sc, Box::new(Stream::Nil))
                } else {
                    Stream::Nil
                }
            }
            Goal::Fn(gfn) => {
                let gfn = gfn.clone();
                Stream::Later(Box::new(move || gfn(sc)))
            }
        }
    }
}

fn disj(g1: Goal, g2: Goal) -> Goal {
    Goal::Disj(Rc::new(g1), Rc::new(g2))
}
fn conj(g1: Goal, g2: Goal) -> Goal {
    Goal::Conj(Rc::new(g1), Rc::new(g2))
}
fn fresh<F: Fn(Var) -> Goal + 'static>(f: F) -> Goal {
    Goal::Fresh(Rc::new(f))
}
fn rc_term<U: Term + 'static>(u: U) -> RcTerm {
    (u.any().downcast_ref::<RcTerm>())
        .cloned()
        .unwrap_or_else(|| Rc::new(u))
}
fn equal_o<U: Term + 'static, V: Term + 'static>(u: U, v: V) -> Goal {
    Goal::Equal(rc_term(u), rc_term(v))
}
fn goal<F: Fn(State) -> Stream + 'static>(f: F) -> Goal {
    Goal::Fn(Rc::new(f))
}
macro_rules! query {
    (|$x:ident $(, $xs:ident)*| $g:expr) => {{
        let ($x $(, $xs)*) = (Var::X(stringify!($x)) $(, Var::X(stringify!($xs)))*);
        let s = $g.query((vec![], 0));
        s.map(move |sc| {
            [($x, walk(&rc_term($x), &sc)) $(, ($xs, walk(&rc_term($xs), &sc)))*]
        })
    }};
}
macro_rules! disj {
    ($g1:expr) => { $g1 };
    ($g1:expr, $($g:expr),*) => { disj($g1, disj!($($g),*)) };
}
macro_rules! conj {
    ($g1:expr) => { $g1 };
    ($g1:expr, $($g:expr),*) => {conj($g1, conj!($($g),*)) };
}

// -- relational queries --
trait TupTerm<const N: usize> {
    fn into_terms(self) -> [RcTerm; N];
}
impl<T1: Term + 'static, T2: Term + 'static> TupTerm<2> for (T1, T2) {
    fn into_terms(self) -> [RcTerm; 2] {
        [rc_term(self.0), rc_term(self.1)]
    }
}
impl<T1: Term + 'static, T2: Term + 'static, T3: Term + 'static> TupTerm<3> for (T1, T2, T3) {
    fn into_terms(self) -> [RcTerm; 3] {
        [rc_term(self.0), rc_term(self.1), rc_term(self.2)]
    }
}
fn lookup<const N: usize, R: TupTerm<N>, Q: TupTerm<N>, Rel: IntoIterator<Item = R>>(
    rel: Rel,
    q: Q,
) -> Goal {
    let rel: Vec<_> = rel.into_iter().map(TupTerm::into_terms).collect();
    let q = q.into_terms();
    goal(move |sc| {
        let mut vars = vec![];
        let mut rel = rel.clone();
        for (i, u) in q.iter().enumerate() {
            let u = walk(u, &sc);
            match as_var(&*u) {
                Some(v) => vars.push((i, v)),
                None => rel = rel.into_iter().filter(|r| (*r[i]).eq_term(&*u)).collect(),
            }
        }
        if rel.is_empty() {
            Stream::Nil
        } else if vars.is_empty() {
            Stream::Now(sc, Box::new(Stream::Nil))
        } else {
            let conj = |r: [RcTerm; N], mut sc: State| {
                for &(i, v) in &vars {
                    sc.0.push((v, r[i].clone()));
                }
                sc
            };
            let mut s = Stream::Nil;
            for r in rel {
                s = Stream::Now(conj(r, sc.clone()), Box::new(s));
            }
            s
        }
    })
}

fn main() {
    fn parent(u: impl Term + 'static, v: impl Term + 'static) -> Goal {
        const REL: [(&'static str, &'static str); 4] = [
            ("bob", "sally"),
            ("sharon", "sally"),
            ("sally", "edith"),
            ("sally", "toby"),
        ];
        lookup(REL, (u, v))
    }
    fn ancestor(u: impl Term + Clone + 'static, v: impl Term + Clone + 'static) -> Goal {
        disj(
            parent(u.clone(), v.clone()),
            fresh(move |x| conj(parent(u.clone(), x), ancestor(x, v.clone()))),
        )
    }
    let s = query!(|x| ancestor(x, "toby"));
    for vs in s {
        println!("{vs:?}")
    }
}
