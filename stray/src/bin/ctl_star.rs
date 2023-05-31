#![allow(unused)]

use std::{
    collections::{HashSet, VecDeque},
    fmt::Debug,
    hash::Hash,
};

#[derive(Clone, PartialEq, PartialOrd)]
enum L<P> {
    False,
    True,
    Pred(P),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Iff(Box<Self>, Box<Self>),
    All(Box<T<P>>),
}

impl<P: Debug> L<P> {
    fn fmt_debug(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            L::False => f.write_str("false"),
            L::True => f.write_str("true"),
            L::Pred(p) => p.fmt(f),
            L::Not(l) => f.write_str("¬").and_then(|_| l.fmt_inner(f, L::fmt_debug)),
            L::And(l, r) => l
                .fmt_inner(f, L::fmt_debug)
                .and_then(|_| f.write_str(" ∧ "))
                .and_then(|_| l.fmt_inner(f, L::fmt_debug)),
            L::Iff(l, r) => l
                .fmt_inner(f, L::fmt_debug)
                .and_then(|_| f.write_str(" ⇐⇒ "))
                .and_then(|_| r.fmt_inner(f, L::fmt_debug)),
            L::All(t) => write!(f, "All({t:?})"),
        }
    }
    fn fmt_inner(
        &self,
        f: &mut std::fmt::Formatter,
        fmt: impl Fn(&Self, &mut std::fmt::Formatter) -> std::fmt::Result,
    ) -> std::fmt::Result {
        match self {
            L::False | L::True | L::Pred(_) | L::Not(_) | L::All(_) => fmt(self, f),
            L::And(_, _) | L::Iff(_, _) => {
                f.write_str("(")?;
                fmt(self, f)?;
                f.write_str(")")
            }
        }
    }
}
impl<P: Debug> Debug for L<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("L(")?;
        self.fmt_debug(f)?;
        f.write_str(")")
    }
}

#[derive(Clone, PartialEq, PartialOrd)]
enum T<P> {
    Pred(L<P>),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Iff(Box<Self>, Box<Self>),

    Next(Box<Self>),
    Until(Box<Self>, Box<Self>),
}

impl<P: Debug> T<P> {
    fn fmt_debug(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            T::Pred(l) => l.fmt_debug(f),
            T::Not(t) => f.write_str("¬").and_then(|_| t.fmt_inner(f, T::fmt_debug)),
            T::And(l, r) => l
                .fmt_inner(f, T::fmt_debug)
                .and_then(|_| f.write_str(" ∧ "))
                .and_then(|_| r.fmt_inner(f, T::fmt_debug)),
            T::Iff(l, r) => l
                .fmt_inner(f, T::fmt_debug)
                .and_then(|_| f.write_str(" ⇐⇒ "))
                .and_then(|_| r.fmt_inner(f, T::fmt_debug)),
            T::Next(t) => f.write_str("◯").and_then(|_| t.fmt_inner(f, T::fmt_debug)),
            T::Until(l, r) => l
                .fmt_inner(f, T::fmt_debug)
                .and_then(|_| f.write_str(" U "))
                .and_then(|_| r.fmt_inner(f, T::fmt_debug)),
        }
    }
    fn fmt_inner(
        &self,
        f: &mut std::fmt::Formatter,
        fmt: impl Fn(&Self, &mut std::fmt::Formatter) -> std::fmt::Result,
    ) -> std::fmt::Result {
        match self {
            T::Pred(l) => l.fmt_inner(f, L::fmt_debug),
            T::Not(_) | T::Next(_) => fmt(self, f),
            T::And(_, _) | T::Iff(_, _) | T::Until(_, _) => {
                f.write_str("(")?;
                fmt(self, f)?;
                f.write_str(")")
            }
        }
    }
}
impl<P: Debug> Debug for T<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("T(")?;
        self.fmt_debug(f)?;
        f.write_str(")")
    }
}

impl<P: PartialOrd> L<P> {
    fn bool(b: bool) -> L<P> {
        if b {
            L::True
        } else {
            L::False
        }
    }

    fn pred(p: P) -> L<P> {
        L::Pred(p)
    }
    fn not(self) -> L<P> {
        match (self) {
            L::True => L::False,
            L::False => L::True,
            L::Not(l) => *l,
            L::Iff(l, r) => l.not().iff(*r),
            l => L::Not(Box::new(l)),
        }
    }
    fn and(self, rhs: Self) -> L<P> {
        match if self < rhs { (self, rhs) } else { (rhs, self) } {
            (l @ L::False, _) | (_, l @ L::False) => l,
            (L::True, l) | (l, L::True) => l,

            // e /\ e <=> e
            (l, r) if l == r => l,
            (l1, L::And(l2, l3)) | (L::And(l2, l3), l1) if l1 == *l2 || l1 == *l3 => L::And(l2, l3),
            // e /\ !e <=> f
            (l, L::Not(r)) if l == *r => L::False,

            (L::And(l1, l2), l3) => l1.and(l2.and(l3)),
            (l, r) => L::And(Box::new(l), Box::new(r)),
        }
    }
    fn or(self, rhs: Self) -> L<P> {
        self.not().and(rhs.not()).not()
    }
    fn implies(self, rhs: Self) -> L<P> {
        rhs.or(self.not())
    }
    fn iff(self, rhs: Self) -> Self {
        match if self < rhs { (self, rhs) } else { (rhs, self) } {
            (L::True, l) | (l, L::True) => l,
            (L::False, l) | (l, L::False) => l.not(),
            (L::Not(l), L::Not(r)) => l.iff(*r),
            (l, r) if l == r => L::True,
            (l, L::Not(r)) if l == *r => L::False,
            (l, r) => L::Iff(Box::new(l), Box::new(r)),
        }
    }
    fn all_paths(t: T<P>) -> L<P> {
        L::All(Box::new(t))
    }
    fn any_paths(t: T<P>) -> L<P> {
        Self::all_paths(t.not()).not()
    }
}

// for the constructors, we want to move nots down and nexts up
impl<P: PartialOrd> T<P> {
    fn bool(b: bool) -> Self {
        T::raise(L::bool(b))
    }
    fn pred(p: P) -> Self {
        T::raise(L::pred(p))
    }
    fn raise(l: L<P>) -> Self {
        T::Pred(l)
    }
    fn not(self) -> Self {
        match (self) {
            T::Pred(l) => T::Pred(l.not()),
            T::Not(t) => *t,
            T::Iff(l, r) => l.not().iff(*r),
            // !Xe <=> X!e
            T::Next(t) => t.not().next(),
            t => T::Not(Box::new(t)),
        }
    }
    fn and(self, rhs: Self) -> Self {
        match if self < rhs { (self, rhs) } else { (rhs, self) } {
            (T::Pred(l), T::Pred(r)) => T::Pred(l.and(r)),
            (t @ T::Pred(L::False), _) => t,
            (T::Pred(L::True), t) => t,

            // e /\ e <=> e
            (l, r) if l == r => l,
            (t1, T::And(t2, t3)) | (T::And(t2, t3), t1) if t1 == *t2 || t1 == *t3 => T::And(t2, t3),
            // e /\ !e <=> f
            (l, T::Not(r)) if l == *r => T::Pred(L::False),

            // X(e /\ e) <=> Xe /\ Xe
            (T::Next(l), T::Next(r)) => l.and(*r).next(),
            // (e1 /\ e2) U e3 <=> (e1 U e3) /\ (e2 U e3)
            (T::Until(e1, e2), T::Until(e3, e4)) if e2 == e4 => e1.and(*e3).until(*e2),

            (l, r) => T::And(Box::new(l), Box::new(r)),
        }
    }
    fn or(self, rhs: Self) -> Self {
        self.not().and(rhs.not()).not()
    }
    fn iff(self, rhs: Self) -> Self {
        match if self < rhs { (self, rhs) } else { (rhs, self) } {
            (T::Pred(l), T::Pred(r)) => T::Pred(l.iff(r)),
            (T::Pred(L::False), t) => t.not(),
            (T::Pred(L::True), t) => t,
            (T::Next(l), T::Next(r)) => l.iff(*r).next(),
            (l, r) if l == r => T::Pred(L::True),
            (l, T::Not(r)) if l == *r => T::Pred(L::False),
            (l, r) => T::Iff(Box::new(l), Box::new(r)),
        }
    }
    fn next(self) -> Self {
        match self {
            t @ T::Pred(L::True | L::False) => t,
            t => T::Next(Box::new(t)),
        }
    }
    fn until(self, rhs: Self) -> Self {
        match (self, rhs) {
            // e2 \/ (f /\ _) <=> e2
            (T::Pred(L::False), t) => t,

            // e1 U e2 : e2 must eventually become true
            // this allows Fe <=> t U e
            //(t @ T::Pred(L::True), _) => t, <- only true for e1 W e2
            //
            // p |= e1 U e2  <=> \En>=0. p[n] |= e2 /\ \A0<=k<n. p[k] |= e1)
            //               <=> \En>=0. (M,p[n]_0) |= e2 /\ ..
            // p |!= e U f   <=> \An>=0. (M,p[n]_0) |!= f \/ !..
            (_, t @ T::Pred(L::False)) => t,
            // p |= e U t    <=> \En>=0. (M,p[n]_0) |= t /\ ..  (by n=0)
            (_, t @ T::Pred(L::True)) => t,

            // X(e1 U e2) <=> Xe1 U Xe2
            (T::Next(l), T::Next(r)) => l.until(*r).next(),
            // e1 U e2 <=> e1 U (e1 U e2)
            (t1, T::Until(t2, t3)) if t1 == *t2 => T::Until(t2, t3),

            (l, r) => T::Until(Box::new(l), Box::new(r)),
        }
    }
    fn release(self, rhs: Self) -> Self {
        self.not().until(rhs.not()).not()
    }
    fn anon(self) -> Self {
        T::Pred(L::True).until(self)
    }
    fn ever(self) -> Self {
        self.not().anon().not()
    }
}

#[derive(Debug, Clone, PartialEq)]
struct State<P> {
    props: Vec<P>,
}
trait BaseSat: Debug + Clone + PartialEq + PartialOrd {
    type State: Debug + PartialEq;
    fn sat(&self, state: &Self::State) -> bool;

    fn state_sat(s: &Self::State, m: &Model<Self>, f: &L<Self>) -> T<Self> {
        match f {
            L::False => T::bool(false),
            L::True => T::bool(true),
            L::Pred(p) => {
                println!("  state_sat({s:?}, {p:?})");
                T::bool(p.sat(s))
            }
            L::Not(e) => Self::state_sat(s, m, &*e).not(),
            L::And(e1, e2) => Self::state_sat(s, m, e1).and(Self::state_sat(s, m, e2)),
            L::Iff(e1, e2) => Self::state_sat(s, m, e1).iff(Self::state_sat(s, m, e2)),
            L::All(e) => todo!("all paths starting from self satisfy {e:?}"),
        }
    }

    fn path_sat(s: &Self::State, m: &Model<Self>, f: &T<Self>) -> T<Self> {
        println!("  path_sat {s:?} {f:?}");
        match f {
            // p |= e  <=  (M,p0) |= e
            T::Pred(e) => Self::state_sat(s, m, e),
            T::Not(e) => Self::path_sat(s, m, e).not(),
            T::And(e1, e2) => Self::path_sat(s, m, e1).and(Self::path_sat(s, m, e2)),
            T::Iff(e1, e2) => Self::path_sat(s, m, e1).iff(Self::path_sat(s, m, e2)),
            // p |= Xe  <=  p[1] |= e
            T::Next(e) => (**e).clone(), // this doesn't feel right
            // p |= e1 U e2  <=  (p |= e2) \/ ((p |= e1) /\ (p[1] |= e1 U e2))
            T::Until(e1, e2) => Self::path_sat(s, m, e2)
                // shortcut because e1.until(e2) == Self::path_sat(s, e1.until(e2).next())
                .or(Self::path_sat(s, m, e1).and(e1.clone().until(*e2.clone()))),
        }
    }
}

type Invariant<P> = (&'static str, T<P>);

struct Model<P: BaseSat> {
    states: Vec<P::State>,
    init: usize,
    fnext: Box<dyn Fn(&P::State) -> Vec<P::State>>,
    working: VecDeque<(usize, Vec<Invariant<P>>, Vec<usize>)>,
}

impl<P: BaseSat> State<P> {}

impl<P: BaseSat> Model<P> {
    fn new(
        init: Vec<P::State>,
        next: impl Fn(&P::State) -> Vec<P::State> + 'static,
        inv: Vec<Invariant<P>>,
    ) -> Self {
        let mut states = init;
        let init = states.len();
        let fnext = Box::new(next);
        let working = (0..init).map(|i| (i, inv.clone(), vec![])).collect();
        Model {
            states,
            init,
            fnext,
            working,
        }
    }
    fn work(&mut self) -> bool {
        let mut w = None;
        while let Some(w2) = self.working.pop_front() {
            if !w2.1.is_empty() {
                w = Some(w2);
                break;
            }
        }
        let (sid, mut t, mut p) = match w {
            Some(w) => w,
            None => return false,
        };
        let s = &self.states[sid];
        for (name, t2) in t.iter_mut() {
            let t = P::path_sat(s, self, t2);
            if (t == T::Pred(L::False)) {
                println!("state [{sid}] violated {name} ({t2:?})");
                println!("State {}: {s:?}", p.len());
                for (i, s) in p
                    .iter()
                    .enumerate()
                    .map(|(i, sid)| (i, &self.states[*sid]))
                    .rev()
                {
                    println!("State {i}: {s:?}");
                }
                return false;
            }
            *t2 = t;
        }
        t = t
            .into_iter()
            .filter(|(name, t)| *t != T::Pred(L::True))
            .collect();
        p.push(sid);
        for snext in &self.next(sid) {
            self.working.push_back((*snext, t.clone(), p.clone()));
        }
        true
    }

    fn next(&mut self, sid: usize) -> Vec<usize> {
        let s = &self.states[sid];
        let ss = (self.fnext)(s);
        let mut ret = vec![];
        for s in ss {
            if let Some(i) = self.states.iter().position(|s2| &s == s2) {
                ret.push(i);
            } else {
                self.states.push(s);
                ret.push(self.states.len() - 1);
            }
        }
        ret
    }
}

impl<P: BaseSat> std::fmt::Debug for Model<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut fs = f.debug_struct("Model");
        fs.field("init", &self.states[..self.init].iter().collect::<Vec<_>>());
        match self.working.front() {
            Some((sid, invs, path)) => fs.field(
                "working",
                &format_args!(
                    "[({:?}, {:?}, [_;{}]), .. ; {}]",
                    &self.states[*sid],
                    invs,
                    path.len(),
                    self.working.len()
                ),
            ),
            None => fs.field("working", &format_args!("[]")),
        };
        fs.finish()
    }
}

#[derive(Clone, PartialEq, PartialOrd)]
struct PBits<T>(T);
impl Debug for PBits<u8> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:b}", self.0)
    }
}
impl<T: std::ops::BitOr<T, Output = T> + Debug + Clone + PartialEq + PartialOrd> BaseSat
    for PBits<T>
where
    PBits<T>: Debug,
{
    type State = Self;
    fn sat(&self, state: &Self) -> bool {
        (state.0.clone() | self.0.clone()) == self.0
    }
}

fn main() {
    let mut m: Model<PBits<u8>> = Model::new(
        vec![PBits(1 << 1)],
        |s| vec![PBits(s.0 << 1)],
        vec![
            ("trivial", T::Pred(L::True)),
            //("eventually10", T::Pred(L::Pred(10)).anon()),
            (
                "<>(2 U 7)",
                T::pred(PBits(1 << 2)).until(T::pred(PBits(1 << 7))).anon(),
            ),
        ],
    );

    println!("{m:?}");
    let mut i = 0;
    while (m.work()) {
        println!("{m:?}");
        if i > 12 {
            return;
        }
        i += 1;
    }
}
