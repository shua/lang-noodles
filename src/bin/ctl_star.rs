#![allow(unused)]

use std::{
    collections::{HashSet, VecDeque},
    fmt::{Debug, Display},
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

impl<P> L<P> {
    fn fmt_debug(
        &self,
        f: &mut std::fmt::Formatter,
        mut inv: bool,
        pfmt: &dyn Fn(&P, &mut std::fmt::Formatter) -> std::fmt::Result,
    ) -> std::fmt::Result {
        let mut infix =
            |f: &mut std::fmt::Formatter, l: &Self, linv: bool, c, r: &Self, rinv: bool| {
                l.fmt_inner(f, linv, pfmt)?;
                f.write_str(c)?;
                r.fmt_inner(f, rinv, pfmt)
            };

        match (self, inv) {
            (L::False, false) | (L::True, true) => f.write_str("false"),
            (L::True, false) | (L::False, true) => f.write_str("true"),
            (L::Pred(p), false) => pfmt(p, f),
            (L::Not(l), inv) => l.fmt_debug(f, !inv, pfmt),
            (L::And(l, r), false) => infix(f, l, false, " ∧ ", r, false),
            (L::And(l, r), true) => infix(f, l, true, " ∨ ", r, true),
            (L::Iff(l, r), inv) => infix(f, l, false, " ⇐⇒ ", r, inv),
            (L::All(t), false) => {
                f.write_str("All(")?;
                t.fmt_debug(f, false, pfmt)?;
                f.write_str(")")
            }
            (L::All(t), true) => {
                f.write_str("Any(")?;
                t.fmt_debug(f, true, pfmt)?;
                f.write_str(")")
            }
            (l @ (L::Pred(_)), true) => {
                f.write_str("¬")?;
                l.fmt_inner(f, false, pfmt)
            }
        }
    }

    fn fmt_inner(
        &self,
        f: &mut std::fmt::Formatter,
        inv: bool,
        pfmt: &dyn Fn(&P, &mut std::fmt::Formatter) -> std::fmt::Result,
    ) -> std::fmt::Result {
        match self {
            L::False | L::True | L::Pred(_) | L::Not(_) | L::All(_) => self.fmt_debug(f, inv, pfmt),
            L::And(_, _) | L::Iff(_, _) => {
                f.write_str("(")?;
                self.fmt_debug(f, inv, pfmt)?;
                f.write_str(")")
            }
        }
    }
}
impl<P: Debug> Debug for L<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !f.alternate() {
            f.write_str("L(")?;
            self.fmt_debug(f, false, &P::fmt)?;
            f.write_str(")")
        } else {
            match self {
                L::False => f.debug_tuple("False").finish(),
                L::True => f.debug_tuple("True").finish(),
                L::Pred(p) => f.debug_tuple("Pred").field(p).finish(),
                L::Not(l) => f.debug_tuple("Not").field(l).finish(),
                L::And(l, r) => f.debug_tuple("And").field(l).field(r).finish(),
                L::Iff(l, r) => f.debug_tuple("Iff").field(l).field(r).finish(),
                L::All(t) => f.debug_tuple("All").field(t).finish(),
            }
        }
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

impl<P> T<P> {
    fn fmt_debug(
        &self,
        f: &mut std::fmt::Formatter,
        mut inv: bool,
        pfmt: &dyn Fn(&P, &mut std::fmt::Formatter) -> std::fmt::Result,
    ) -> std::fmt::Result {
        let mut prefix = |f: &mut std::fmt::Formatter, c, t: &Self, inv| {
            f.write_str(c)?;
            t.fmt_inner(f, inv, pfmt)
        };
        let mut infix =
            |f: &mut std::fmt::Formatter, l: &Self, linv: bool, c, r: &Self, rinv: bool| {
                l.fmt_inner(f, linv, pfmt)?;
                f.write_str(c)?;
                r.fmt_inner(f, rinv, pfmt)
            };
        match (self, inv) {
            (T::Pred(l), inv) => l.fmt_debug(f, inv, pfmt),
            (T::Not(t), inv) => t.fmt_debug(f, !inv, pfmt),
            (T::And(l, r), false) => infix(f, l, false, " ∧ ", r, false),
            (T::And(l, r), true) => infix(f, l, true, " ∨ ", r, true),
            (T::Iff(l, r), inv) => infix(f, l, false, " ⇐⇒ ", r, inv),
            (T::Next(t), inv) => prefix(f, "◯", t, inv),
            (T::Until(l, r), false) if matches!(**l, T::Pred(L::True)) => prefix(f, "⋄", r, false),
            (T::Until(l, r), true) if matches!(**l, T::Pred(L::True)) => prefix(f, "☐", r, true),
            (T::Until(l, r), false) => infix(f, l, false, " U ", r, false),
            (T::Until(l, r), true) => infix(f, l, true, " R ", r, true),
        }
    }

    fn fmt_inner(
        &self,
        f: &mut std::fmt::Formatter,
        inv: bool,
        pfmt: &dyn Fn(&P, &mut std::fmt::Formatter) -> std::fmt::Result,
    ) -> std::fmt::Result {
        match self {
            T::Pred(l) => l.fmt_inner(f, inv, pfmt),
            T::Not(_) | T::Next(_) => self.fmt_debug(f, inv, pfmt),
            T::Until(l, _) if matches!(**l, T::Pred(L::True)) => self.fmt_debug(f, inv, pfmt),
            T::And(_, _) | T::Iff(_, _) | T::Until(_, _) => {
                f.write_str("(")?;
                self.fmt_debug(f, inv, pfmt)?;
                f.write_str(")")
            }
        }
    }
}
impl<P: Debug> Debug for T<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !f.alternate() {
            f.write_str("T(")?;
            self.fmt_debug(f, false, &P::fmt)?;
            f.write_str(")")
        } else {
            match self {
                T::Pred(l) => f.debug_tuple("Pred").field(l).finish(),
                T::Not(t) => f.debug_tuple("Not").field(t).finish(),
                T::And(l, r) => f.debug_tuple("And").field(l).field(r).finish(),
                T::Iff(l, r) => f.debug_tuple("Iff").field(l).field(r).finish(),
                T::Next(t) => f.debug_tuple("Next").field(t).finish(),
                T::Until(l, r) => f.debug_tuple("Until").field(l).field(r).finish(),
            }
        }
    }
}

impl<P: Theory> L<P> {
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
            L::Pred(p) => p.not(),
            l => L::Not(Box::new(l)),
        }
    }
    fn and(self, rhs: Self) -> L<P> {
        match if self < rhs { (self, rhs) } else { (rhs, self) } {
            (L::False, _) => L::bool(false),
            (L::True, l) => l,

            // e /\ e <=> e
            (l, r) if l == r => l,
            (l1, L::And(l2, l3)) | (L::And(l2, l3), l1) if l1 == *l2 || l1 == *l3 => L::And(l2, l3),
            // e /\ !e <=> f
            (L::Not(l), r) | (r, L::Not(l)) if *l == r => L::False,

            (L::And(l1, l2), l3) => l1.and(l2.and(l3)),
            (L::Pred(l), L::Pred(r)) => l.and(r),
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
            (L::False, l) => l.not(),
            (L::True, l) => l,
            (L::Not(l), L::Not(r)) => l.iff(*r),
            (l, r) if l == r => L::True,
            (l, L::Not(r)) if l == *r => L::False,
            (L::Pred(l), L::Pred(r)) => l.iff(r),
            (l, r) => L::Iff(Box::new(l), Box::new(r)),
        }
    }
    fn all_paths(t: T<P>) -> L<P> {
        L::All(Box::new(t))
    }
    fn any_paths(t: T<P>) -> L<P> {
        Self::all_paths(t.not()).not()
    }

    fn unchanging(self) -> T<P> {
        match self {
            L::All(t) => *t,
            l => T::raise(l),
        }
    }
}

impl<P: Theory> T<P> {
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
            T::Next(t) => t.not().next(),
            t => T::Not(Box::new(t)),
        }
    }
    fn and(self, rhs: Self) -> Self {
        match if self < rhs { (self, rhs) } else { (rhs, self) } {
            (T::Pred(l), T::Pred(r)) => T::Pred(l.and(r)),
            (T::Pred(L::False), _) => T::bool(false),
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
    fn implies(self, rhs: Self) -> Self {
        rhs.or(self.not())
    }
    fn iff(self, rhs: Self) -> Self {
        match if self < rhs { (self, rhs) } else { (rhs, self) } {
            (T::Pred(l), T::Pred(r)) => T::Pred(l.iff(r)),
            (T::Pred(L::False), t) => t.not(),
            (T::Pred(L::True), t) => t,
            (T::Not(l), T::Not(r)) => l.iff(*r),
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

    fn unchanging(self) -> Self {
        match self {
            T::Pred(l) => l.unchanging(),
            T::Not(t) => t.unchanging().not(),
            T::And(l, r) => l.unchanging().and(r.unchanging()),
            T::Iff(l, r) => l.unchanging().iff(r.unchanging()),
            T::Next(t) => *t,
            T::Until(_, _) => T::bool(false),
        }
    }
}

trait Theory: Debug + Clone + PartialEq + PartialOrd {
    type State: Debug + PartialEq;
    fn sat(&self, state: &Self::State) -> bool;

    // can override if theory supports equivalent statements
    // eg for sets  "e \in S1 /\ e \in S2" <=> "e \in S1 \cap S2"
    fn not(self) -> L<Self> {
        L::Not(Box::new(L::pred(self)))
    }
    fn and(self, rhs: Self) -> L<Self> {
        L::And(Box::new(L::pred(self)), Box::new(L::pred(rhs)))
    }
    fn iff(self, rhs: Self) -> L<Self> {
        L::Iff(Box::new(L::pred(self)), Box::new(L::pred(rhs)))
    }
    fn simp(self) -> Self {
        self
    }
}

type Invariant<P> = (&'static str, T<P>);
type StateID = usize;
type PathID = usize;
type Work<P> = (StateID, Vec<Invariant<P>>, Vec<StateID>);

struct Model<P: Theory> {
    states: Vec<P::State>,
    init: usize,
    fnext: Box<dyn Fn(&P::State) -> Vec<P::State>>,
    working: VecDeque<Work<P>>,
    paths: Vec<Vec<PathID>>,
}

impl<P: Theory> Model<P> {
    fn new(
        init: Vec<P::State>,
        next: impl Fn(&P::State) -> Vec<P::State> + 'static,
        inv: Vec<Invariant<P>>,
    ) -> Self {
        let mut states = init;
        let init = states.len();
        let fnext = Box::new(next);
        let working = (0..init).map(|i| (i, inv.clone(), vec![])).collect();
        let paths = vec![vec![0]; init];
        Model {
            states,
            init,
            fnext,
            working,
            paths,
        }
    }

    fn state_sat(&self, s: StateID, f: &L<P>) -> T<P> {
        match f {
            L::False => T::bool(false),
            L::True => T::bool(true),
            L::Pred(p) => {
                //println!("  state_sat({s:?}, {p:?})");
                T::bool(p.sat(&self.states[s]))
            }
            L::Not(e) => self.state_sat(s, &*e).not(),
            L::And(e1, e2) => self.state_sat(s, e1).and(self.state_sat(s, e2)),
            L::Iff(e1, e2) => self.state_sat(s, e1).iff(self.state_sat(s, e2)),
            L::All(t) => *t.clone(),
        }
    }

    fn path_sat(&self, s: StateID, f: &T<P>) -> T<P> {
        //println!("  path_sat {s:?} {f:?}");
        match f {
            // p |= e  <=  (M,p0) |= e
            T::Pred(e) => self.state_sat(s, e),
            T::Not(e) => self.path_sat(s, e).not(),
            T::And(e1, e2) => self.path_sat(s, e1).and(self.path_sat(s, e2)),
            T::Iff(e1, e2) => self.path_sat(s, e1).iff(self.path_sat(s, e2)),
            // p |= Xe  <=  p[1] |= e
            T::Next(e) => (**e).clone(),
            // p |= e1 U e2  <=  (p |= e2) \/ ((p |= e1) /\ (p[1] |= e1 U e2))
            T::Until(e1, e2) => self
                .path_sat(s, e2)
                // shortcut because e1.until(e2) == self.path_sat(s1.until(e2).next())
                .or(self.path_sat(s, e1).and(e1.clone().until(*e2.clone()))),
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
        let (s, mut t, mut p) = match w {
            Some(w) => w,
            None => return false,
        };
        let mut tequiv = true;
        for (name, t2) in t.iter_mut() {
            let t = self.path_sat(s, t2);
            tequiv = tequiv && (t == *t2 || t == T::bool(true));
            if (t == T::Pred(L::False)) {
                println!("state [{s}] violated {name} ({t2:?})");
                println!("{}: State {:?}", p.len(), self.states[s]);
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
        p.push(s);
        if tequiv {
            let tunchanging: Vec<_> = t
                .iter()
                .map(|(n, t)| (*n, t.clone().unchanging()))
                .collect();
            for snext in self.next(s) {
                if snext == s {
                    println!(
                        "  potential deadlock: {:?} {t:?} ({tunchanging:?})",
                        self.states[s]
                    );
                    self.working
                        .push_back((snext, tunchanging.clone(), p.clone()));
                } else {
                    self.working.push_back((snext, t.clone(), p.clone()));
                }
            }
        }
        for snext in &self.next(s) {
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

impl<P: Theory> std::fmt::Debug for Model<P> {
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
macro_rules! impl_pbits_debug {
    ($($f:tt)*) => {$(
        impl Debug for PBits<$f> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:b}", self.0)
            }
        }
    )*};
}
impl_pbits_debug! { u8 u16 u32 }

impl<T: std::ops::BitOr<T, Output = T> + Debug + Clone + PartialEq + PartialOrd> Theory for PBits<T>
where
    PBits<T>: Debug,
{
    type State = Self;
    fn sat(&self, state: &Self) -> bool {
        (state.0.clone() | self.0.clone()) == self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
enum Queens<const N: usize> {
    Safe,
    Placed,
}
impl<const N: usize> Theory for Queens<N> {
    // 1 queen per-row
    type State = [usize; N];

    fn sat(&self, state: &Self::State) -> bool {
        match self {
            Queens::Safe => {
                let len = state.iter().filter(|i| **i < N).count();
                for i in 0..len {
                    for j in 0..i {
                        // check cols
                        if state[j] == state[i] {
                            return false;
                        }
                        // check diagonal
                        if j.abs_diff(i) == state[j].abs_diff(state[i]) {
                            return false;
                        }
                    }
                }
                true
            }
            Queens::Placed => state.iter().all(|i| *i < N),
        }
    }
}

fn main() {
    /*
    let mut m: Model<PBits<u8>> = Model::new(
        vec![PBits(1 << 1)],
        |s| vec![PBits(s.0 << 1)],
        vec![
            ("trivial", T::Pred(L::True)),
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
    */

    const N: usize = 3;
    let mut m: Model<Queens<N>> = Model::new(
        vec![[N; N]],
        |s| {
            if let Some(i) = (0..N).find(|i| s[*i] == N) {
                // deadlock if queen is unsafe
                if !Queens::Safe.sat(s) {
                    return vec![s.clone()];
                }
                let mut s = s.clone();
                (0..N)
                    .map(|j| {
                        let mut s = s.clone();
                        s[i] = j;
                        s
                    })
                    .collect()
            } else {
                vec![s.clone()]
            }
        },
        vec![(
            "<>(safe && placed)",
            T::raise(L::any_paths(
                T::pred(Queens::Safe).and(T::pred(Queens::Placed)).anon(),
            )),
        )],
    );

    // since the 'next state' function is opaque, there's no chance of pruning a !safe state
    // which will never transition to a safe state, eg [0,0,_]
    // is there some way of telling the solver that the state state graph is one direction (except the leaves)?
    // is that a lattice?
    // I guess I could deadlock on !safe states?
    println!("{m:?}");
    let mut i = 0;
    while m.work() {
        println!("{i}: {m:?}");
        if i > 200 {
            return;
        }
        i += 1;
    }
}
