#![allow(dead_code)]

// https://ecommons.cornell.edu/server/api/core/bitstreams/3b34b390-c307-42ae-a6d5-c25db60f0d7c/content
// Abstraction-Safe Effect Handlers via Tunneling

use std::marker::PhantomData;
use subst::{Subst, SubstAny};

type Index = usize;
type Lbl = usize;
type Lbls = Vec<Lbl>;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Cap {
    A(Index),
    L(Lbl),
    H(Index),
}
#[derive(Clone, PartialEq)]
struct Caps(Vec<Cap>);
#[derive(Debug, Clone, PartialEq, SubstAny)]
#[subst_any(Box<Self>, Caps)]
enum Type {
    Unit,
    Fn(Box<Self>, Box<Self>, Caps),
    FFn(#[subst_bind] Box<Self>),
    HFn(EffName, #[subst_bind] Box<Self>, #[subst_bind] Caps),
}
type EffName = String;
#[derive(SubstAny, Clone)]
#[subst_any(HDef)]
enum Hdlr {
    H(Index),
    HH(HDef),
}
#[derive(Debug, Clone)]
struct HDef(EffName, Box<Term>, Lbl);
#[derive(Clone, SubstAny)]
#[subst_any(Val, Box<Self>, Type, Caps, Hdlr)]
enum Term {
    V(Val),
    X(Index),
    App(Box<Self>, Box<Self>),
    Let(Type, Box<Self>, #[subst_bind] Box<Self>),
    FApp(Box<Self>, Caps),
    HApp(Box<Self>, Hdlr),
    UpH(Index),
    Dn(Lbl, Type, Caps, Box<Self>),
}
#[derive(SubstAny, Debug, Clone)]
#[subst_any(Type, Box<Term>, HDef)]
enum Val {
    Unit,
    Fn(Type, #[subst_bind] Box<Term>),
    FFn(#[subst_bind] Box<Term>),
    HFn(EffName, #[subst_bind] Box<Term>),
    UpHH(HDef),
}

impl<T> SubstAny<T> for HDef
where
    Term: Subst<T>,
{
    fn subst_any(&mut self, x: Index, v: T) {
        self.1.subst(x + 2, v)
    }
}
impl<T> SubstAny<T> for Caps {
    fn subst_any(&mut self, _x: Index, _v: T) {}
}

impl Subst<Val> for Val {}
impl Subst<Lbls> for Val {}
impl Subst<Hdlr> for Val {}
impl Subst<Val> for Term {
    fn subst(&mut self, x: Index, v: Val) {
        match self {
            Term::X(y) if *y == x => *self = Term::V(v),
            _ => self.subst_any(x, v),
        }
    }
}
impl Subst<Lbls> for Term {}
impl Subst<Hdlr> for Term {
    fn subst(&mut self, x: Index, v: Hdlr) {
        match self {
            Term::UpH(h) if *h == x => {
                *self = match v {
                    Hdlr::H(h) => Term::UpH(h),
                    Hdlr::HH(v) => Term::V(Val::UpHH(v)),
                }
            }
            _ => self.subst_any(x, v),
        }
    }
}
impl<T: Clone> Subst<T> for Type where Caps: Subst<T> {}

impl Subst<Val> for Hdlr {}
impl Subst<Lbls> for Hdlr {}
impl Subst<Hdlr> for Hdlr {
    fn subst(&mut self, x: Index, v: Hdlr) {
        match self {
            Hdlr::H(h) if *h == x => *self = v,
            _ => self.subst_any(x, v),
        }
    }
}
impl<T> Subst<T> for HDef where Term: Subst<T> {}
impl Subst<Val> for Caps {}
impl Subst<Hdlr> for Caps {
    fn subst(&mut self, x: Index, v: Hdlr) {
        for c in &mut self.0 {
            match c {
                Cap::H(h) if *h == x => {
                    *c = match &v {
                        Hdlr::H(h) => Cap::H(*h),
                        Hdlr::HH(HDef(_, _, l)) => Cap::L(*l),
                    }
                }
                _ => {}
            }
        }
    }
}
impl Subst<Caps> for Caps {
    fn subst(&mut self, x: usize, v: Caps) {
        if self.0.is_empty() {
            return;
        }
        let mut found = false;
        let mut i = 0;
        while i < self.0.len() - 1 {
            match &self.0[i] {
                Cap::A(a) if *a == x => {
                    found = true;
                    self.0.swap_remove(i);
                }
                _ => i += 1,
            }
        }
        if let Some(Cap::A(a)) = self.0.last() {
            if *a == x {
                found = true;
                self.0.pop();
            }
        }
        if found {
            self.0.extend(v.0)
        }
    }
}
impl Subst<Lbls> for Caps {
    fn subst(&mut self, x: Index, v: Lbls) {
        let v = v.into_iter().map(Cap::L).collect::<Vec<_>>();
        self.subst(x, Caps(v));
    }
}

impl std::fmt::Debug for Cap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Cap::A(a) => write!(f, "{a}:A"),
            Cap::L(l) => write!(f, "{l}:L"),
            Cap::H(h) => write!(f, "{h}:H"),
        }
    }
}
impl std::fmt::Debug for Caps {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            f.write_str("[]")
        } else {
            write!(f, "[{:?}", self.0[0])?;
            for c in &self.0[1..] {
                write!(f, ",{c:?}")?;
            }
            write!(f, "]")
        }
    }
}
impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        #[derive(Debug)]
        enum DbgT<'t> {
            App(&'t Term, &'t Term),
            Let(&'t Type, &'t Term, &'t Term),
            HApp(&'t Term, &'t Hdlr),
            FApp(&'t Term, &'t Caps),
        }
        match self {
            Term::V(v) => std::fmt::Debug::fmt(v, f),
            Term::X(x) => write!(f, "{x}:X"),
            Term::App(e1, e2) => DbgT::App(e1, e2).fmt(f),
            Term::Let(t, e1, e2) => DbgT::Let(t, e1, e2).fmt(f),
            Term::FApp(e, f2) => DbgT::FApp(e, f2).fmt(f),
            Term::HApp(e, h) => DbgT::HApp(e, h).fmt(f),
            Term::UpH(h) => write!(f, "UpH({h})"),
            Term::Dn(l, t, c, e) => f
                .debug_tuple("Dn")
                .field(&Cap::L(*l))
                .field(t)
                .field(c)
                .field(e)
                .finish(),
        }
    }
}
impl std::fmt::Debug for Hdlr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Hdlr::H(h) => write!(f, "{h}:H"),
            Hdlr::HH(hh) => std::fmt::Debug::fmt(hh, f),
        }
    }
}

#[derive(Debug)]
enum EvalCtx {
    Hole,
    AppL(Box<Self>, Box<Term>),
    AppR(Val, Box<Self>),
    FApp(Box<Self>, Lbls),
    HApp(Box<Self>, HDef),
    Let(Type, Box<Self>, Box<Term>),
    Dn(Lbl, Type, Caps, Box<Self>),
}

impl EvalCtx {
    fn fill(self, e: Term) -> Term {
        match self {
            EvalCtx::Hole => e,
            EvalCtx::AppL(kk, e2) => Term::App(Box::new(kk.fill(e)), e2),
            EvalCtx::AppR(v, kk) => Term::App(Box::new(Term::V(v)), Box::new(kk.fill(e))),
            EvalCtx::FApp(kk, f) => Term::FApp(
                Box::new(kk.fill(e)),
                Caps(f.into_iter().map(Cap::L).collect()),
            ),
            EvalCtx::HApp(kk, hh) => Term::HApp(Box::new(kk.fill(e)), Hdlr::HH(hh)),
            EvalCtx::Let(t, kk, e2) => Term::Let(t, Box::new(kk.fill(e)), e2),
            EvalCtx::Dn(l, t, f, kk) => Term::Dn(l, t, f, Box::new(kk.fill(e))),
        }
    }
}

type Map<K, V> = std::collections::HashMap<K, V>;
type Sigs = Map<EffName, (Type, Type)>;
fn op<'s>(sigs: &'s Sigs, ff: &EffName) -> Option<&'s (Type, Type)> {
    sigs.get(ff)
}
fn eval(sigs: &Sigs, e: Term) -> Result<Val, (EvalCtx, Term)> {
    fn eval_dnup(
        sigs: &Sigs,
        l: Lbl,
        t: Type,
        f: Caps,
        kk: EvalCtx,
        e1: Term,
        e2: Term,
    ) -> Result<Val, (EvalCtx, Term)> {
        let eval = |e| eval(sigs, e);
        // let eval = |e| dbg!(eval(dbg!(e)));
        match (e1, e2) {
            (Term::V(Val::UpHH(HDef(ff, mut e, hl))), Term::V(v))
                if hl == l && op(sigs, &ff).is_some() =>
            {
                let Some((_, t2)) = op(sigs, &ff) else {
                    unreachable!()
                };
                let k = Val::Fn(
                    t2.clone(),
                    Box::new(Term::Dn(l, t, f, Box::new(kk.fill(Term::X(0))))),
                );
                e.subst(0, k);
                e.subst(1, v);
                eval(*e)
            }
            (e1, e2) => Err((
                EvalCtx::Dn(l, t, f, Box::new(kk)),
                Term::App(Box::new(e1), Box::new(e2)),
            )),
        }
    }
    let eval = |e| eval(sigs, e);
    // let eval = |e| dbg!(eval(dbg!(e)));
    match e {
        Term::V(v) => Ok(v),
        Term::Let(t, e1, mut e2) => match eval(*e1) {
            Ok(v) => {
                e2.subst(0, v);
                eval(*e2)
            }
            Err((kk, e)) => Err((EvalCtx::Let(t, Box::new(kk), e2), e)),
        },
        Term::App(e1, e2) => match eval(*e1) {
            Ok(Val::Fn(t, mut e1)) => match eval(*e2) {
                Ok(v) => {
                    e1.subst(0, v);
                    eval(*e1)
                }
                Err((kk, e)) => Err((EvalCtx::AppR(Val::Fn(t, e1), Box::new(kk)), e)),
            },
            // evaluating the second arg makes checking for `K [(UP H^l) v]` easier
            Ok(v @ Val::UpHH(_)) => match eval(*e2) {
                Ok(w) => Err((
                    EvalCtx::Hole,
                    Term::App(Box::new(Term::V(v)), Box::new(Term::V(w))),
                )),
                Err((kk, e)) => Err((EvalCtx::AppR(v, Box::new(kk)), e)),
            },
            Ok(v) => Err((EvalCtx::Hole, Term::App(Box::new(Term::V(v)), e2))),
            Err((kk, e)) => Err((EvalCtx::AppL(Box::new(kk), e2), e)),
        },
        Term::FApp(e, f) if f.0.iter().all(|c| matches!(c, Cap::L(_))) => {
            let ls: Lbls =
                f.0.into_iter()
                    .map(|c| match c {
                        Cap::L(l) => l,
                        _ => unreachable!(),
                    })
                    .collect();
            match eval(*e) {
                Ok(Val::FFn(mut v)) => {
                    v.subst(0, ls);
                    eval(*v)
                }
                Ok(v) => Err((
                    EvalCtx::Hole,
                    Term::FApp(
                        Box::new(Term::V(v)),
                        Caps(ls.into_iter().map(Cap::L).collect()),
                    ),
                )),
                Err((kk, e)) => Err((EvalCtx::FApp(Box::new(kk), ls), e)),
            }
        }
        Term::HApp(e, hh @ Hdlr::HH(_)) => match eval(*e) {
            Ok(Val::HFn(_, mut v)) => {
                v.subst(0, hh);
                eval(*v)
            }
            Ok(v) => Err((EvalCtx::Hole, Term::HApp(Box::new(Term::V(v)), hh))),
            Err((kk, e)) => match hh {
                Hdlr::HH(hh) => Err((EvalCtx::HApp(Box::new(kk), hh), e)),
                Hdlr::H(_) => unreachable!(),
            },
        },
        Term::Dn(l, t, f, e) => match eval(*e) {
            Ok(v) => Ok(v),
            Err((kk, Term::App(e1, e2))) => eval_dnup(sigs, l, t, f, kk, *e1, *e2),
            Err((kk, e)) => Err((kk, e)),
        },
        e => Err((EvalCtx::Hole, e)),
    }
}

#[derive(Debug)]
enum EvalStep {
    Complete(Val),
    Progress(EvalCtx, Term),
    Stuck(EvalCtx, Term),
}
fn eval_step(sigs: &Sigs, e: EvalStep) -> EvalStep {
    use EvalStep::*;
    fn kk_step(sigs: &Sigs, kk: EvalCtx, v: Val) -> EvalStep {
        let kk_step = |kk, v| kk_step(sigs, kk, v);
        match kk {
            EvalCtx::Hole => Complete(v),
            EvalCtx::AppL(kk, e) => match kk_step(*kk, v) {
                Complete(v) => Progress(EvalCtx::AppR(v, Box::new(EvalCtx::Hole)), *e),
                Progress(kk, e1) | Stuck(kk, e1) => Progress(EvalCtx::AppL(Box::new(kk), e), e1),
            },
            EvalCtx::AppR(v1, kk) => match kk_step(*kk, v) {
                Complete(v2) => match v1 {
                    Val::Fn(_t, mut e) => {
                        e.subst(0, v2);
                        Progress(EvalCtx::Hole, *e)
                    }
                    v1 => Stuck(
                        EvalCtx::Hole,
                        Term::App(Box::new(Term::V(v1)), Box::new(Term::V(v2))),
                    ),
                },
                Progress(kk, e) | Stuck(kk, e) => Progress(EvalCtx::AppR(v1, Box::new(kk)), e),
            },
            EvalCtx::FApp(kk, c) => match kk_step(*kk, v) {
                Complete(Val::FFn(mut e)) => {
                    e.subst(0, c);
                    Progress(EvalCtx::Hole, *e)
                }
                Complete(v) => Stuck(
                    EvalCtx::Hole,
                    Term::FApp(
                        Box::new(Term::V(v)),
                        Caps(c.into_iter().map(Cap::L).collect()),
                    ),
                ),
                Progress(kk, e) | Stuck(kk, e) => Progress(EvalCtx::FApp(Box::new(kk), c), e),
            },
            EvalCtx::HApp(kk, h) => match kk_step(*kk, v) {
                Complete(Val::HFn(_ff, mut e)) => {
                    e.subst(0, Hdlr::HH(h));
                    Progress(EvalCtx::Hole, *e)
                }
                Complete(v) => Stuck(EvalCtx::Hole, Term::HApp(Box::new(Term::V(v)), Hdlr::HH(h))),
                Progress(kk, e) | Stuck(kk, e) => Progress(EvalCtx::HApp(Box::new(kk), h), e),
            },
            EvalCtx::Let(t, kk, mut e2) => match kk_step(*kk, v) {
                Complete(v) => {
                    e2.subst(0, v);
                    Progress(EvalCtx::Hole, *e2)
                }
                Progress(kk, e) | Stuck(kk, e) => Progress(EvalCtx::Let(t, Box::new(kk), e2), e),
            },
            EvalCtx::Dn(l, t, c, kk) => match kk_step(*kk, v) {
                Complete(v) => Complete(v),
                Stuck(kk, Term::App(e1, e2))
                    if match &*e1 {
                        Term::V(Val::UpHH(HDef(ff, _, hl))) => *hl == l && op(sigs, ff).is_some(),
                        _ => false,
                    } =>
                {
                    let Term::V(Val::UpHH(HDef(ff, mut e, _))) = *e1 else {
                        unreachable!()
                    };
                    let Some((_, t2)) = op(sigs, &ff) else {
                        unreachable!()
                    };
                    let k = Val::Fn(
                        t2.clone(),
                        Box::new(Term::Dn(l, t, c, Box::new(kk.fill(Term::X(0))))),
                    );
                    e.subst(0, k);
                    Progress(EvalCtx::AppL(Box::new(EvalCtx::Hole), e2), *e)
                }
                Progress(kk, e) | Stuck(kk, e) => Progress(EvalCtx::Dn(l, t, c, Box::new(kk)), e),
            },
        }
    }
    fn e_step(e: Term) -> EvalStep {
        match e {
            Term::V(v) => Complete(v),
            Term::X(x) => Stuck(EvalCtx::Hole, Term::X(x)),
            Term::App(e1, e2) => Progress(EvalCtx::AppL(Box::new(EvalCtx::Hole), e2), *e1),
            Term::Let(t, e1, e2) => Progress(EvalCtx::Let(t, Box::new(EvalCtx::Hole), e2), *e1),
            Term::FApp(e, c) if c.0.iter().all(|c| matches!(c, Cap::L(_))) => Progress(
                EvalCtx::FApp(
                    Box::new(EvalCtx::Hole),
                    c.0.into_iter()
                        .map(|c| match c {
                            Cap::L(l) => l,
                            _ => unreachable!(),
                        })
                        .collect(),
                ),
                *e,
            ),
            Term::HApp(e, Hdlr::HH(h)) => Progress(EvalCtx::HApp(Box::new(EvalCtx::Hole), h), *e),
            Term::Dn(l, t, c, e) => Progress(EvalCtx::Dn(l, t, c, Box::new(EvalCtx::Hole)), *e),
            e @ (Term::UpH(_) | Term::FApp(_, _) | Term::HApp(_, Hdlr::H(_))) => {
                Stuck(EvalCtx::Hole, e)
            }
        }
    }
    fn kk_fill(kk1: &mut EvalCtx, kk2: EvalCtx) {
        if matches!(kk2, EvalCtx::Hole) {
            return;
        }
        match kk1 {
            EvalCtx::Hole => *kk1 = kk2,
            EvalCtx::AppL(kk, _)
            | EvalCtx::AppR(_, kk)
            | EvalCtx::FApp(kk, _)
            | EvalCtx::HApp(kk, _)
            | EvalCtx::Let(_, kk, _)
            | EvalCtx::Dn(_, _, _, kk) => kk_fill(kk, kk2),
        }
    }
    match e {
        e @ Complete(_) => e,
        Progress(mut kk, e) | Stuck(mut kk, e) => match e_step(e) {
            Complete(v) => kk_step(sigs, kk, v),
            Progress(kk2, e) => {
                kk_fill(&mut kk, kk2);
                Progress(kk, e)
            }
            Stuck(kk2, e) => {
                kk_fill(&mut kk, kk2);
                Stuck(kk, e)
            }
        },
    }
}

struct MI<T>(usize, PhantomData<T>);
impl<T> Clone for MI<T> {
    fn clone(&self) -> Self {
        MI(self.0, PhantomData)
    }
}
impl<T> Copy for MI<T> {}
macro_rules! impl_from_mi {
    ($($t2:ty as $t1:ty $(= $p:expr)?),* $(,)?) => {$(
        impl From<(usize, $t2)> for $t1 {
            fn from(v: (usize, $t2)) -> Self {
                impl_from_mi!(@ v $(=> $p)?)
            }
        }
    )*};
    (@ $v:ident => $p:expr) => { $p($v.0 - $v.1.0 - 1) };
    (@ $v:ident) => { $v.1 };
}
impl_from_mi! {
    MI<Term> as Term = Term::X,
    MI<Hdlr> as Hdlr = Hdlr::H,
    MI<Cap> as Cap = Cap::A,
    MI<Hdlr> as Cap = Cap::H,
    Term as Term,
    Cap as Cap,
}

impl Term {
    fn up(h: Hdlr) -> Term {
        match h {
            Hdlr::H(h) => Term::UpH(h),
            Hdlr::HH(h) => Term::V(Val::UpHH(h)),
        }
    }
}

fn genlbl() -> Lbl {
    use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};
    static LBL: AtomicUsize = AtomicUsize::new(0);
    let r = LBL.load(SeqCst);
    LBL.compare_exchange(r, r + 1, SeqCst, SeqCst).unwrap();
    r
}

macro_rules! val {
    ($i:tt ()) => { Val::Unit };
    ($i:tt fn($x:ident : $($t:tt)*) $($e:tt)*) => { Val::Fn(typ_!($i $($t)*), Box::new({ let $x = MI($i, PhantomData::<Term>); expr_!(($i+1) $($e)*) })) };
    ($i:tt fn[$h:ident : $op:tt] $($e:tt)*) => { Val::HFn($op.to_string(), Box::new({ let $h = MI($i, PhantomData::<Hdlr>); expr_!(($i+1) $($e)*) })) };
    ($i:tt fn^[$a:ident] $($v:tt)*) => { Val::FFn(Box::new({ let $a = MI::<Cap>($i, PhantomData); expr_!(($i+1) $($v)*) })) };
    ($i:tt UP handler^$l:ident $op:ident ($x:ident, $k:ident) $($e:tt)+) => { Val::UpHH(HDef(stringify!($op).to_string(), Box::new({
        let ($x, $k) = (MI($i), MI($i+1));
        expr_!(($i+2) $($e)*)
    })), $l) }
}
macro_rules! expr_ {
    ($i:tt $x:ident) => { Term::from(($i, $x)) };
    ($i:tt ()) => { Term::V(val!($i ())) };
    ($i:tt ($($e:tt)+)) => { expr_!($i $($e)*) };
    ($i:tt let $x:ident : $t:tt = $e1:tt ; $($e2:tt)*) => { Term::Let(typ_!($i $t), Box::new(expr_!($i $e1)), Box::new({ let $x = MI($i, PhantomData::<Term>); expr_!(($i+1) $($e2)*)})) };
    ($i:tt let _ : $t:tt = $e1:tt ; $($e2:tt)*) => { Term::Let(typ_!($i $t), Box::new(expr_!($i $e1)), Box::new(expr_!(($i+1) $($e2)*))) };
    ($i:tt fn $($e:tt)*) => { Term::V(val!($i fn $($e)*)) };
    ($i:tt UP $($h:tt)*) => { Term::up(hdlr!($i $($h)*)) };
    ($i:tt DN^$l:ident : $t:tt ^[$($c:tt)*] . $($e:tt)*) => {{
        let $l = genlbl();
        Term::Dn($l, typ_!($i $t), caps_!($i [$($c)*]), Box::new(expr_!($i $($e)*)))
    }};
    ($i:tt $e1:tt $e2:tt $($e3:tt)*) => { exprapp_!($i (expr_!($i $e1)) $e2 $($e3)*) };
}
macro_rules! exprapp_ {
    ($i:tt $e1:tt) => { $e1 };
    ($i:tt $e1:tt ^[$($c:tt)*] $($e:tt)*) => { exprapp_!($i (Term::FApp(Box::new($e1), caps_!($i [$($c)*]))) $($e)*)  };
    ($i:tt $e1:tt [$($h:tt)*] $($e:tt)*) => { exprapp_!($i (Term::HApp(Box::new($e1), hdlr!($i $($h)*))) $($e)*) };
    ($i:tt $e1:tt $e2:tt $($e:tt)*) => { exprapp_!($i (Term::App(Box::new($e1), Box::new(expr_!($i $e2)))) $($e)*)  };
}
macro_rules! expr { ($($e:tt)*) => { expr_!(0 $($e)*) }; }
macro_rules! typ_ {
    ($i:tt ()) => { Type::Unit };
    ($i:tt $x:ident) => { Type::from($x) };
    ($i:tt ($($t:tt)+)) => { typ_!($i $($t)*) };
    ($i:tt fn($($s:tt)*)^$c:tt $($t:tt)*) => { Type::Fn(Box::new(typ_!($i ($($s)*))), Box::new(typ_!($i $($t)*)), caps_!($i $c)) };
    ($i:tt fn($($s:tt)*) $($t:tt)*) => { typ_!($i fn($($s)*)^[] $($t)*) };
    ($i:tt fn^[$a:ident] $($t:tt)*) => { Type::FFn(Box::new({ let $a = MI($i, PhantomData::<Cap>); typ_!(($i+1) $($t)*) })) };
    //($i:tt fn^[$a:ident] $($t:tt)*) => { Type::FFn(Box::new(Type::Unit)) };
    ($i:tt fn[$h:tt: $F:tt]^$c:tt $($t:tt)*) => {{
        let $h = MI($i, PhantomData::<Hdlr>);
        Type::HFn($F.to_string(), Box::new(typ_!(($i+1) $($t)*)), caps_!(($i+1) $c))
    }};
    ($i:tt fn[$h:tt: $F:tt] $($t:tt)*) => { typ_!($i fn[$h: $F]^[] $($t)*) };
}
macro_rules! typ { ($($t:tt)*) => { typ_!(0 $($t)*) }; }
macro_rules! caps_ {
    ($i:tt $c:ident) => { $c };
    ($i:tt [$($c:expr),*]) => { Caps(vec![$(Cap::from(($i, $c))),*]) };
}
macro_rules! caps { ($($c:tt)*) => { caps_!(0 [$($c)*]) }; }
macro_rules! hdlr {
    ($i:tt $h:ident) => { Hdlr::from(($i, $h)) };
    ($i:tt handler^$l:tt $op:tt ($x:ident, $k:ident) $($e:tt)+) => {
        Hdlr::HH(HDef($op.to_string(), Box::new({
            let ($x, $k) = (MI($i, PhantomData::<Term>), MI($i+1, PhantomData::<Term>));
            expr_!(($i+2) $($e)*)
            /*Term::V(Val::Unit)*/
        }), $l))
    };
}

#[derive(Debug, Clone, PartialEq)]
enum CtxBinding {
    Eff,
    Hdlr(EffName),
    Term(Type),
}
#[derive(Clone)]
struct WFCtx<'s>(Vec<CtxBinding>, Map<Lbl, (Type, Caps)>, &'s Sigs);
impl std::fmt::Debug for WFCtx<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("{}")?;
        for c in &self.0 {
            match c {
                CtxBinding::Eff => write!(f, ", a")?,
                CtxBinding::Hdlr(ff) => write!(f, ", h:{ff:?}")?,
                CtxBinding::Term(t) => write!(f, ", x:{t:?}")?,
            }
        }
        f.write_str(" | ")?;
        f.write_str("{}")?;
        for (k, v) in &self.1 {
            write!(f, ", {k}:L : {:?}^{:?}", v.0, v.1)?;
        }
        Ok(())
    }
}
impl WFCtx<'_> {
    fn get(&self, x: usize) -> Option<&CtxBinding> {
        if x < self.0.len() {
            self.0.get(self.0.len() - x - 1)
        } else {
            None
        }
    }
    fn get_e(&self, x: usize) -> Option<&Type> {
        self.get(x).and_then(|x| match x {
            CtxBinding::Term(e) => Some(e),
            _ => None,
        })
    }
    fn get_l(&self, x: usize) -> Option<&(Type, Caps)> {
        self.1.get(&x)
    }
    fn get_h(&self, x: usize) -> Option<&EffName> {
        self.get(x).and_then(|x| match x {
            CtxBinding::Hdlr(ff) => Some(ff),
            _ => None,
        })
    }
    fn get_c(&self, x: usize) -> Option<()> {
        self.get(x).and_then(|x| match x {
            CtxBinding::Eff => Some(()),
            _ => None,
        })
    }
    fn get_op(&self, ff: &EffName) -> Option<&(Type, Type)> {
        self.2.get(ff)
    }
}

/// G |- T
fn t_wf(ctx: &WFCtx, t: &Type) -> Option<()> {
    match t {
        Type::Unit => Some(()),
        Type::Fn(t, s, c) => {
            t_wf(ctx, t)?;
            t_wf(ctx, s)?;
            c_wf(ctx, c)?;
            Some(())
        }
        Type::FFn(t) => {
            let mut ctx = ctx.clone();
            ctx.0.push(CtxBinding::Eff);
            t_wf(&ctx, t)
        }
        Type::HFn(ff, t, c) => {
            let mut ctx = ctx.clone();
            ctx.0.push(CtxBinding::Hdlr(ff.clone()));
            t_wf(&ctx, t)?;
            c_wf(&ctx, c)?;
            Some(())
        }
    }
}

/// G |- T1 <: T2
fn t_sub<'a, 's>(ctx: &WFCtx<'s>, t1: &Type, t2: &Type) -> Result<(), TySynErr<'a, 's>> {
    match (t1, t2) {
        (Type::Unit, Type::Unit) => Ok(()),
        (Type::Fn(t1, s1, c1), Type::Fn(t2, s2, c2)) => {
            t_sub(ctx, t2, t1)?;
            t_sub(ctx, s1, s2)?;
            c_sub(ctx, c1, c2)
                .ok_or_else(|| TySynErr::CSub(ctx.clone(), c1.clone(), c2.clone()))?;
            Ok(())
        }
        (Type::FFn(t1), Type::FFn(t2)) => {
            let mut ctx = ctx.clone();
            ctx.0.push(CtxBinding::Eff);
            t_sub(&ctx, t1, t2)
        }
        (Type::HFn(ff1, t1, c1), Type::HFn(ff2, t2, c2)) if ff1 == ff2 => {
            let mut ctx = ctx.clone();
            ctx.0.push(CtxBinding::Hdlr(ff1.clone()));
            t_sub(&ctx, t1, t2)?;
            c_sub(&ctx, c1, c2)
                .ok_or_else(|| TySynErr::CSub(ctx.clone(), c1.clone(), c2.clone()))?;
            Ok(())
        }
        // they also permit a transitive closure, but I don't see any
        // way for that to extend the sub-typing rules. Maybe they
        // use it in proofs?
        _ => Err(TySynErr::TSub(ctx.clone(), t1.clone(), t2.clone())),
    }
}

/// G |- h: FF | c
fn h_fsyn<'a, 's>(ctx: &WFCtx<'s>, h: &'a Hdlr) -> Result<(EffName, Cap), TySynErr<'a, 's>> {
    match h {
        // T-HVAR
        Hdlr::H(h) => h_fsyn_h(ctx, *h),
        // T-HDEF
        Hdlr::HH(hh) => h_fsyn_hh(ctx, hh),
    }
}
// h_fsyn but Hdlr::H case broken out for lifetimes in the error
fn h_fsyn_h<'a, 's>(ctx: &WFCtx<'s>, h: Index) -> Result<(EffName, Cap), TySynErr<'a, 's>> {
    // dbg!(("h_fsyn_h", ctx, h));
    ctx.get_h(h)
        .map(|ff| (ff.clone(), Cap::H(h)))
        .ok_or_else(|| TySynErr::FSyn(ctx.clone(), Hdlr::H(h)))
}
/// h_fsyn but the Hdlr::HH case broken out to avoid cloning
fn h_fsyn_hh<'a, 's>(
    ctx: &WFCtx<'s>,
    hh @ HDef(op, e, l): &'a HDef,
) -> Result<(EffName, Cap), TySynErr<'a, 's>> {
    let (s, c) = ctx
        .get_l(*l)
        .ok_or_else(|| TySynErr::FSyn(ctx.clone(), Hdlr::HH(hh.clone())))?;
    // XXX: any indices in s that reach past l should be raised?
    let (t1, t2) = ctx
        .get_op(op)
        .ok_or_else(|| TySynErr::FSyn(ctx.clone(), Hdlr::HH(hh.clone())))?;
    // XXX: I think t1 and t2 can't have any indices because they are static signatures
    let mut ctx: WFCtx<'s> = ctx.clone();
    // XXX: this doesn't seem correct, at least c should be lowered if it's being put inside something
    ctx.0.push(CtxBinding::Term(t1.clone()));
    let (t2, cc, ss) = (t2.clone(), c.clone(), s.clone());
    ctx.0.push(CtxBinding::Term(typ!(fn(t2)^cc ss)));
    let (s2, c2) = e_tysyn(&ctx, e)?;
    t_sub(&ctx, &s2, s)?;
    c_sub(&ctx, &c2, c).ok_or_else(|| TySynErr::CSub(ctx.clone(), c2, c.clone()))?;
    Ok((op.clone(), Cap::L(*l)))
}

/// find c st.  c1 <: c  and  c2 <: c
/// basically least-upper-bound or union of two sets
fn c_merge(c1: Caps, c2: Caps) -> Caps {
    let Caps(mut c) = c1;
    c.extend(c2.0);
    c.sort();
    c.dedup();
    Caps(c)
}

/// G |- c
fn c_wf(ctx: &WFCtx, c: &Caps) -> Option<()> {
    for c in &c.0 {
        match *c {
            Cap::A(a) => {
                ctx.get_c(a)?;
            }
            Cap::L(l) => {
                ctx.get_l(l)?;
            }
            Cap::H(h) => {
                ctx.get_h(h)?;
            }
        }
    }
    Some(())
}

/// G |- c1<:c2
///
/// (all j, exists i) e1(j) = e2(i)
/// (all i) G |- e2(i)
fn c_sub(ctx: &WFCtx, c1: &Caps, c2: &Caps) -> Option<()> {
    for c in &c1.0 {
        c2.0.contains(c).then(|| ())?;
    }
    c_wf(ctx, c2)
}

#[derive(Debug)]
enum TySynErr<'a, 's> {
    Var(WFCtx<'s>, Index),
    TWF(WFCtx<'s>, &'a Type),
    CWF(WFCtx<'s>, &'a Caps),
    TySyn(WFCtx<'s>, &'a Term),
    FSyn(WFCtx<'s>, Hdlr),
    TSub(WFCtx<'s>, Type, Type),
    CSub(WFCtx<'s>, Caps, Caps),
    TUp(WFCtx<'s>, EffName, Cap),
    // In(Box<Self>, &'a Term),
}
/// G |- e: [T]_c
fn e_tysyn<'a, 's>(ctx: &WFCtx<'s>, e: &'a Term) -> Result<(Type, Caps), TySynErr<'a, 's>> {
    fn raise<'a, 's>(ctx: &WFCtx<'s>, t: &mut Type, c: &mut Caps) {
        let mut j = 0;
        for (i, b) in ctx.0.iter().rev().enumerate() {
            match b {
                CtxBinding::Eff => {
                    // dbg!(("raise_a", i, j));
                    t.subst(i, Caps(vec![Cap::A(j)]));
                    c.subst(i, Caps(vec![Cap::A(j)]));
                    j += 1;
                }
                CtxBinding::Hdlr(_) => {
                    // dbg!(("raise_h", i, j, &t, &c));
                    t.subst(i, Hdlr::H(j));
                    c.subst(i, Hdlr::H(j));
                    j += 1;
                }
                CtxBinding::Term(_) => {}
            }
        }
    }
    fn t_up<'a, 's>(
        ctx: &WFCtx<'s>,
        ff: EffName,
        c: Cap,
    ) -> Result<(Type, Caps), TySynErr<'a, 's>> {
        let (t, s) = (ctx.get_op(&ff).cloned()).ok_or_else(|| TySynErr::TUp(ctx.clone(), ff, c))?;
        let c = Caps(vec![c]);
        Ok((typ!(fn(t)^c s), caps![]))
    }

    // let h_fsyn_hh = |ctx, hh| dbg!(h_fsyn_hh(ctx, hh));
    // let e_tysyn = |ctx, e| dbg!(e_tysyn(ctx, e));
    // let t_up = |ctx, ff, c| dbg!(t_up(ctx, ff, c));
    // let t_sub = |ctx, t1, t2| dbg!(t_sub(ctx, t1, t2));
    // let c_sub = |ctx, c1, c2| dbg!(c_sub(ctx, c1, c2));
    fn inner<'a, 's>(ctx: &WFCtx<'s>, e: &'a Term) -> Result<(Type, Caps), TySynErr<'a, 's>> {
        match e {
            // T-UNIT
            Term::V(Val::Unit) => Ok((typ!(()), caps![])),
            // T-VAR
            // TODO: this should lower any vars in t by (ctx.0.len() - x)
            // TODO: this should raise any vars in t over ctx term vars
            Term::X(x) => ctx
                .get_e(*x)
                .map(|t| (t.clone(), caps![]))
                .ok_or_else(|| TySynErr::Var(ctx.clone(), *x)),
            // T-ABS
            Term::V(Val::Fn(t, e)) => {
                t_wf(ctx, t).ok_or_else(|| TySynErr::TWF(ctx.clone(), t))?;
                let mut ctx: WFCtx<'s> = ctx.clone();
                ctx.0.push(CtxBinding::Term(t.clone()));
                let (mut t2, mut cs) = e_tysyn(&ctx, e)?;
                raise(&ctx, &mut t2, &mut cs);
                let t = t.clone();
                Ok((typ!(fn(t)^cs t2), caps![]))
            }
            // T-APP
            Term::App(e1, e2) => {
                let (t1, c1) = e_tysyn(ctx, e1)?;
                let Type::Fn(t1, t2, c2) = t1 else {
                    return Err(TySynErr::TySyn(ctx.clone(), e));
                };
                // want [S->[T]_c']_c'  but  [S->[T]_e2']_e1' is okay if
                // S->[T]_e2' <: S->[T]_c'  and  e1' <: c'
                // S<:S  T<:T  e2' <: c'
                //
                // so c' = union(e1, e2) would give such a c
                let c = c_merge(c1, c2);
                let (t3, c3) = e_tysyn(ctx, e2)?;
                t_sub(ctx, &t3, &t1)?;
                let c = c_merge(c, c3);
                Ok((*t2, c))
            }
            // T-LET
            Term::Let(t, e1, e2) => {
                t_wf(ctx, t).ok_or_else(|| TySynErr::TWF(ctx.clone(), t))?;
                let (t1, c1) = e_tysyn(ctx, e1)?;
                t_sub(ctx, &t1, t)?;
                let mut ctx = ctx.clone();
                ctx.0.push(CtxBinding::Term(t.clone()));
                let (t2, c2) = e_tysyn(&ctx, e2)?;
                Ok((t2, c_merge(c1, c2)))
            }
            // T-EABS
            e0 @ Term::V(Val::FFn(e)) => {
                let mut ctx = ctx.clone();
                ctx.0.push(CtxBinding::Eff);
                let (t, c) = e_tysyn(&ctx, e)?;
                // no way to get t:[T]_{}  from  t:[T]_c'
                // because T-SUB requires c'<:{} which cannot be true
                // so only accept t:[T]_{} here
                if !c.0.is_empty() {
                    return Err(TySynErr::TySyn(ctx.clone(), e0));
                };
                Ok((typ!(fn^[_a] t), c))
            }
            // T-EAPP
            e0 @ Term::FApp(e, c) => {
                c_wf(ctx, c).ok_or_else(|| TySynErr::CWF(ctx.clone(), c))?;
                let (t1, c1) = e_tysyn(ctx, e)?;
                let Type::FFn(mut t1) = t1 else {
                    return Err(TySynErr::TySyn(ctx.clone(), e0));
                };
                t1.subst(0, c.clone());
                Ok((*t1, c1))
            }
            // T-HABS
            Term::V(Val::HFn(ff, e)) => {
                let mut ctx = ctx.clone();
                ctx.0.push(CtxBinding::Hdlr(ff.clone()));
                let (t, c) = e_tysyn(&ctx, e)?;
                let ff = ff.clone();
                Ok((typ!(fn[_: ff]^c t), caps![]))
            }
            // T-HAPP
            e0 @ Term::HApp(e, h) => {
                let (t, c1) = e_tysyn(ctx, e)?;
                let Type::HFn(ff, mut t2, mut c2) = t else {
                    Err(TySynErr::TySyn(ctx.clone(), e0))?
                };
                let (ff1, _c3) = h_fsyn(ctx, h)?;
                if ff != ff1 {
                    return Err(TySynErr::TySyn(ctx.clone(), e0));
                }
                c2.subst(0, h.clone());
                t2.subst(0, h.clone());
                Ok((*t2, c_merge(c1, c2)))
            }
            // T-UP
            Term::UpH(h) => {
                let (ff, c) = h_fsyn_h(ctx, *h)?;
                t_up(ctx, ff, c)
            }
            Term::V(Val::UpHH(hh)) => {
                let (ff, c) = h_fsyn_hh(ctx, hh)?;
                t_up(ctx, ff, c)
            }
            // T-DOWN
            Term::Dn(l, t, c, e) => {
                t_wf(ctx, t).ok_or_else(|| TySynErr::TWF(ctx.clone(), t))?;
                c_wf(ctx, c).ok_or_else(|| TySynErr::CWF(ctx.clone(), c))?;
                // say ctx.len() == 4, l == 0, c == [1:H]
                // then
                let mut ctx = ctx.clone();
                ctx.1.insert(*l, (t.clone(), c.clone()));
                let (t1, c1) = e_tysyn(&ctx, e)?;
                t_sub(&ctx, &t1, t)?;
                let c2 = c_merge(c.clone(), Caps(vec![Cap::L(*l)]));
                c_sub(&ctx, &c1, &c2).ok_or_else(|| TySynErr::CSub(ctx.clone(), c1, c2))?;
                Ok((t.clone(), c.clone()))
            }
        }
    }
    let res = inner(ctx, e);
    // dbg!((ctx, e, &res));
    res
}

fn main() {
    let mut sigs = Map::new();
    sigs.insert("yield".to_string(), (typ!(()), typ!(())));
    /*
    let unit = Term::X(4);
    let cap = Cap::A(5);
    let e = expr!(((fn^[_a] fn(x: ()) x) ^[cap]) unit);
    println!("{e:?}");
    let try_with = expr! {
        (DN^l : ()^[] . ((fn[h: "yield"] (UP h) ()) [handler^l "yield"(_x, k) k ()]))
    };
    println!("{try_with:?}");
    */
    // println!("{:?}", eval(&sigs, try_with));

    let fiterate = expr! {
        fn[h: "yield"] fn^[a] fn(tr: ()) fn(f: fn(())^[h,a] ())
            let _ : () = (f ());
            (UP h) tr
    };
    let fsize1 = expr! {
        fn^[a]
        fn(tr: ())
        fn(f: fn()^[a] ())
            let num: () = ();
            let _ : () = (DN^l : ()^[] .
                (fn[hi:"yield"]
                    fiterate [hi] ^[a] tr f)
                [handler^l "yield"(_x, k) k()] );
            num
    };
    let fsize2 = expr! {
        fn^[a]
        fn(tr: ())
        fn(f: fn()^[a] ())
            f tr
    };
    let ex3a = expr! {
        let g: (fn[h: "yield"] fn()^[h] ()) = (fn[h: "yield"] fn(x: ())
            let _ : () = ((UP h) ()); x);
        DN^l : ()^[] . (
            (fn[h:"yield"]
                fsize2 ^[h] () (g[h]))
            [handler^l "yield"(_x, k) k ()])
    };

    println!("ex3a := {:?}", &ex3a);
    println!(
        "{{}} |- ex3a : {:?}",
        e_tysyn(&WFCtx(vec![], Map::new(), &sigs), &ex3a)
    );
    println!("ex3a --> {:?}", eval(&sigs, ex3a.clone()));
    // let mut esteps = EvalStep::Progress(EvalCtx::Hole, ex3a);
    // while let EvalStep::Progress(_, _) = esteps {
    //     esteps = eval_step(&sigs, dbg!(esteps));
    // }
    // dbg!(esteps);
}
