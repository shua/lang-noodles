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

type Query = Rc<dyn Fn(State) -> Goal>;
// the original paper uses a recursive Stream type, like
//     enum Stream<T> { Nil, Mature(T, Box<Self>), Immature(Box<dyn Fn() -> Self>) }
// this may be easier for proofs because it lends itself to mutual recursion,
// but I thought I'd try just keeping two sets as vecs: matures, and immatures.
// Joining two goals is just joining the two sets (not, in the case of Stream::Immature,
// moving closures inside other closures), and mapping a query (in the conj case),
// is pretty much equivalent to Stream.
#[derive(Default)]
struct Goal(Vec<State>, Vec<(Rc<dyn Fn() -> Goal>, Vec<Query>)>);
impl Iterator for Goal {
    type Item = State;
    fn next(&mut self) -> Option<State> {
        if let Some(v) = self.0.pop() {
            return Some(v);
        }
        let (g, qs) = self.1.pop()?;
        let mut g = g();
        for q in qs {
            g = g.map_query(&q);
        }
        self.join_eq(g);
        self.next()
    }
}
impl Goal {
    fn join_eq(&mut self, rhs: Goal) {
        self.0.extend(rhs.0);
        self.1.extend(rhs.1);
    }
    fn join(mut self, rhs: Goal) -> Goal {
        self.join_eq(rhs);
        self
    }
    fn map_query(mut self, q: &Query) -> Goal {
        let mut sret = Goal(vec![], vec![]);
        // if mature state is too big, we can always defer
        // some of this work to an immature state.
        for sc in self.0 {
            sret.join_eq(q(sc));
        }
        sret.1 = self.1;
        for (f, qs) in sret.1.iter_mut() {
            qs.push(q.clone());
        }
        sret
    }
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

fn lazy_goal<F: Fn() -> Query + 'static>(f: F) -> Query {
    let f = Rc::new(f);
    Rc::new(move |sc| {
        let f = f.clone();
        let f = Rc::new(move || f()(sc.clone()));
        Goal(vec![], vec![(f, vec![])])
    })
}
fn goal<F: Fn(State) -> Goal + 'static>(f: F) -> Query {
    Rc::new(move |sc| f(sc))
}
fn fresh<F: Fn(Var) -> Query + 'static>(f: F) -> Query {
    goal(move |(s, c)| f(Var::N(c))((s, c + 1)))
}
fn disj(q1: Query, q2: Query) -> Query {
    goal(move |sc| q1(sc.clone()).join(q2(sc)))
}
fn conj(q1: Query, q2: Query) -> Query {
    goal(move |sc| q1(sc).map_query(&q2))
}
fn equal_o<U: Term + 'static, V: Term + 'static>(u: U, v: V) -> Query {
    let (u, v) = (rc_term(u), rc_term(v));
    goal(move |sc| {
        unify(&u, &v, sc)
            .map(|sc| Goal(vec![sc], vec![]))
            .unwrap_or_default()
    })
}
fn unify(u: &RcTerm, v: &RcTerm, mut s: State) -> Option<State> {
    let (u, v) = (walk(u, &s), walk(v, &s));
    match (as_var(&*u), as_var(&*v)) {
        _ if u.eq_term(&*v) => Some(s),
        (Some(u), _) => Some({
            s.0.push((u, v.clone()));
            s
        }),
        (_, Some(_)) => unify(&v, &u, s),
        _ => None,
    }
}
fn rc_term<U: Term + 'static>(u: U) -> RcTerm {
    Rc::new(u)
}
macro_rules! query {
    (|$x:ident $(, $xs:ident)*| $g:expr) => {{
        let ($x $(, $xs)*) = (Var::X(stringify!($x)) $(, Var::X(stringify!($xs)))*);
        ($g)((vec![], 0)).map(move |sc| {
            [($x, walk(&rc_term($x), &sc)) $(, ($xs, walk(&rc_term($xs), &sc)))*]
        })
    }};
}
macro_rules! disj {
    ($g1:expr) => { $g1 };
    ($g1:expr, $($g:expr),* $(,)?) => { disj($g1, disj!($($g),*)) };
}
macro_rules! conj {
    ($g1:expr) => { $g1 };
    ($g1:expr, $($g:expr),* $(,)?) => {conj($g1, conj!($($g),*)) };
}

fn main() {
    fn fives(x: Var) -> Query {
        disj(equal_o(x, 5), lazy_goal(move || fives(x)))
    }
    for vs in query!(|x| fives(x)).take(5) {
        println!("{vs:?}");
    }
    fn parent(u: impl Term + Copy + 'static, v: impl Term + Copy + 'static) -> Query {
        disj![
            conj(equal_o(u, "bob"), equal_o(v, "sally")),
            conj(equal_o(u, "sharon"), equal_o(v, "sally")),
            conj(equal_o(u, "sally"), equal_o(v, "edith")),
            conj(equal_o(u, "sally"), equal_o(v, "toby")),
        ]
    }
    fn ancestor(u: impl Term + Copy + 'static, v: impl Term + Copy + 'static) -> Query {
        disj(
            parent(u, v),
            fresh(move |x| conj(parent(u, x), ancestor(x, v))),
        )
    }
    let s = query!(|x| ancestor(x, "toby"));
    for vs in s {
        println!("{vs:?}")
    }
}
