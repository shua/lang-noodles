#![allow(dead_code)]

// https://ecommons.cornell.edu/server/api/core/bitstreams/3b34b390-c307-42ae-a6d5-c25db60f0d7c/content
// Abstraction-Safe Effect Handlers via Tunneling

use std::marker::PhantomData;

type Index = usize;
type Lbl = usize;
type Lbls = Vec<Lbl>;
#[derive(Debug, Clone)]
enum Cap {
    A(Index),
    L(Lbl),
    H(Index),
}
type Caps = Vec<Cap>;
#[derive(Debug, Clone)]
enum Type {
    Unit,
    Fn(Box<Self>, Box<Self>, Caps),
    FFn(Box<Self>),
    HFn(EffName, Box<Self>, Caps),
}
type EffName = String;
#[derive(Debug, Clone)]
enum Hdlr {
    H(Index),
    HH(HDef, Lbl),
}
type HDef = (EffName, Box<Term>);
#[derive(Debug, Clone)]
enum Term {
    V(Val),
    X(Index),
    App(Box<Self>, Box<Self>),
    Let(Type, Box<Self>, Box<Self>),
    FApp(Box<Self>, Caps),
    HApp(Box<Self>, Hdlr),
    UpH(Index),
    Dn(Lbl, Type, Caps, Box<Self>),
}
#[derive(Debug, Clone)]
enum Val {
    Unit,
    Fn(Type, Box<Term>),
    FFn(Box<Term>),
    HFn(EffName, Box<Term>),
    UpHH(HDef, Lbl),
}

trait SubstAny<T> {
    fn subst_any(&mut self, _x: Index, _v: T) {}
}
trait Subst<T>: SubstAny<T> {
    fn subst(&mut self, x: Index, v: T) {
        self.subst_any(x, v);
    }
}

impl<T> SubstAny<T> for Val
where
    T: Clone,
    Val: Subst<T>,
    Term: Subst<T>,
    Type: Subst<T>,
{
    fn subst_any(&mut self, x: Index, v: T) {
        match self {
            Val::Unit => {}
            Val::Fn(t, e) => {
                t.subst(x, v.clone());
                e.subst(x, v);
            }
            Val::FFn(e) => e.subst(x, v),
            Val::HFn(_, e) => e.subst(x, v),
            Val::UpHH((_, e), _) => e.subst(x, v),
        }
    }
}
impl Subst<Val> for Val {}
impl Subst<Lbls> for Val {}
impl Subst<(HDef, Lbl)> for Val {}

impl<T> SubstAny<T> for Term
where
    T: Clone,
    Val: Subst<T>,
    Term: Subst<T>,
    Type: Subst<T>,
    Caps: Subst<T>,
    Hdlr: Subst<T>,
{
    fn subst_any(&mut self, x: Index, v: T) {
        match self {
            Term::V(w) => w.subst(x, v),
            Term::X(_) => {}
            Term::App(e1, e2) => {
                e1.subst(x, v.clone());
                e2.subst(x, v);
            }
            Term::Let(t, e1, e2) => {
                t.subst(x, v.clone());
                e1.subst(x, v.clone());
                e2.subst(x, v);
            }
            Term::FApp(e, f) => {
                e.subst(x, v.clone());
                f.subst(x, v);
            }
            Term::HApp(e, h) => {
                e.subst(x, v.clone());
                h.subst(x, v);
            }
            Term::UpH(_) => {}
            Term::Dn(_, t, f, e) => {
                t.subst(x, v.clone());
                f.subst(x, v.clone());
                e.subst(x, v);
            }
        }
    }
}
impl Subst<Val> for Term {
    fn subst(&mut self, x: Index, v: Val) {
        match self {
            Term::X(y) if *y == x => *self = Term::V(v),
            _ => self.subst_any(x, v),
        }
    }
}
impl Subst<Lbls> for Term {}
impl Subst<(HDef, Lbl)> for Term {
    fn subst(&mut self, x: Index, v: (HDef, Lbl)) {
        match self {
            Term::UpH(h) if *h == x => *self = Term::V(Val::UpHH(v.0, v.1)),
            _ => self.subst_any(x, v),
        }
    }
}

impl<T> SubstAny<T> for Type
where
    T: Clone,
    Caps: Subst<T>,
{
    fn subst_any(&mut self, x: Index, v: T) {
        match self {
            Type::Unit => {}
            Type::Fn(t1, t2, f) => {
                t1.subst(x, v.clone());
                t2.subst(x, v.clone());
                f.subst(x, v);
            }
            Type::FFn(t) => t.subst(x, v),
            Type::HFn(_, t, f) => {
                t.subst(x, v.clone());
                f.subst(x, v);
            }
        }
    }
}
impl<T> Subst<T> for Type where Type: SubstAny<T> {}

impl<T> SubstAny<T> for Hdlr
where
    Term: Subst<T>,
{
    fn subst_any(&mut self, x: Index, v: T) {
        match self {
            Hdlr::H(_) => {}
            Hdlr::HH((_, e), _) => e.subst(x, v),
        }
    }
}
impl Subst<Val> for Hdlr {}
impl Subst<Lbls> for Hdlr {}
impl Subst<(HDef, Lbl)> for Hdlr {
    fn subst(&mut self, x: Index, v: (HDef, Lbl)) {
        match self {
            Hdlr::H(h) if *h == x => *self = Hdlr::HH(v.0, v.1),
            _ => self.subst_any(x, v),
        }
    }
}

impl<T> SubstAny<T> for Caps {}
impl Subst<Val> for Caps {}
impl Subst<(HDef, Lbl)> for Caps {
    fn subst(&mut self, x: Index, (_, l): (HDef, Lbl)) {
        for c in self {
            match c {
                Cap::H(h) if *h == x => *c = Cap::L(l.clone()),
                _ => {}
            }
        }
    }
}
impl Subst<Lbls> for Caps {
    fn subst(&mut self, x: Index, v: Lbls) {
        let mut found = false;
        let mut i = 0;
        while i < self.len() - 1 {
            match &self[i] {
                Cap::A(a) if *a == x => {
                    found = true;
                    self.swap_remove(i);
                }
                _ => i += 1,
            }
        }
        if let Some(Cap::A(a)) = self.last() {
            if *a == x {
                found = true;
                self.pop();
            }
        }
        if found {
            self.extend(v.into_iter().map(Cap::L));
        }
    }
}

#[derive(Debug)]
enum EvalCtx {
    Hole,
    AppL(Box<Self>, Box<Term>),
    AppR(Val, Box<Self>),
    FApp(Box<Self>, Lbls),
    HApp(Box<Self>, HDef, Lbl),
    Let(Type, Box<Self>, Box<Term>),
    Dn(Lbl, Type, Caps, Box<Self>),
}

impl EvalCtx {
    fn fill(self, e: Term) -> Term {
        match self {
            EvalCtx::Hole => e,
            EvalCtx::AppL(kk, e2) => Term::App(Box::new(kk.fill(e)), e2),
            EvalCtx::AppR(v, kk) => Term::App(Box::new(Term::V(v)), Box::new(kk.fill(e))),
            EvalCtx::FApp(kk, f) => {
                Term::FApp(Box::new(kk.fill(e)), f.into_iter().map(Cap::L).collect())
            }
            EvalCtx::HApp(kk, hh, l) => Term::HApp(Box::new(kk.fill(e)), Hdlr::HH(hh, l)),
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
        match (e1, e2) {
            (Term::V(Val::UpHH((ff, mut e), hl)), Term::V(v))
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
                eval(sigs, *e)
            }
            (e1, e2) => Err((
                EvalCtx::Dn(l, t, f, Box::new(kk)),
                Term::App(Box::new(e1), Box::new(e2)),
            )),
        }
    }
    let eval = |e| eval(sigs, e);
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
            Ok(v @ Val::UpHH(_, _)) => match eval(*e2) {
                Ok(w) => Err((
                    EvalCtx::Hole,
                    Term::App(Box::new(Term::V(v)), Box::new(Term::V(w))),
                )),
                Err((kk, e)) => Err((EvalCtx::AppR(v, Box::new(kk)), e)),
            },
            Ok(v) => Err((EvalCtx::Hole, Term::App(Box::new(Term::V(v)), e2))),
            Err((kk, e)) => Err((EvalCtx::AppL(Box::new(kk), e2), e)),
        },
        Term::FApp(e, f) if f.iter().all(|c| matches!(c, Cap::L(_))) => {
            let ls: Lbls = f
                .into_iter()
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
                    Term::FApp(Box::new(Term::V(v)), ls.into_iter().map(Cap::L).collect()),
                )),
                Err((kk, e)) => Err((EvalCtx::FApp(Box::new(kk), ls), e)),
            }
        }
        Term::HApp(e, Hdlr::HH(hh, l)) => match eval(*e) {
            Ok(Val::HFn(_, mut v)) => {
                v.subst(0, (hh, l));
                eval(*v)
            }
            Ok(v) => Err((
                EvalCtx::Hole,
                Term::HApp(Box::new(Term::V(v)), Hdlr::HH(hh, l)),
            )),
            Err((kk, e)) => Err((EvalCtx::HApp(Box::new(kk), hh, l), e)),
        },
        Term::Dn(l, t, f, e) => match eval(*e) {
            Ok(v) => Ok(v),
            Err((kk, Term::App(e1, e2))) => eval_dnup(sigs, l, t, f, kk, *e1, *e2),
            Err((kk, e)) => Err((kk, e)),
        },
        e => Err((EvalCtx::Hole, e)),
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
            Hdlr::HH(h, l) => Term::V(Val::UpHH(h, l)),
        }
    }
}

fn genlbl() -> usize {
    use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};
    static LBL: AtomicUsize = AtomicUsize::new(0);
    let r = LBL.load(SeqCst);
    LBL.compare_exchange(r, r + 1, SeqCst, SeqCst).unwrap();
    r
}

macro_rules! val {
    ($i:tt ()) => { Val::Unit };
    ($i:tt fn($x:ident : $($t:tt)*) $($e:tt)*) => { Val::Fn(typ_!($i $($t)*), Box::new({ let $x = MI($i, PhantomData::<Term>); expr_!(($i+1) $($e)*) })) };
    ($i:tt fn[$h:ident : $op:ident] $($e:tt)*) => { Val::HFn(stringify!($op).to_string(), Box::new({ let $h = MI($i, PhantomData::<Hdlr>); expr_!(($i+1) $($e)*) })) };
    ($i:tt fn^[$a:ident] $($v:tt)*) => { Val::FFn(Box::new({ let $a = MI::<Cap>($i, PhantomData); expr_!(($i+1) $($v)*) })) };
    ($i:tt UP handler^$l:ident $op:ident ($x:ident, $k:ident) $($e:tt)+) => { Val::UpHH((stringify!($op).to_string(), Box::new({
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
        Term::Dn($l, typ_!($i $t), caps!($i $($c)*), Box::new(expr_!($i $($e)*)))
    }};
    ($i:tt $e1:tt $e2:tt $($e3:tt)*) => { exprapp_!($i $e2 $($e3)*)(expr_!($i $e1)) };
}
macro_rules! exprapp_ {
    ($i:tt) => { |e: Term| e };
    ($i:tt ^[$($c:tt)*] $($e:tt)*) => { |e1: Term| { exprapp_!($i $($e)*) (Term::FApp(Box::new(e1), caps!($i $($c)*))) } };
    ($i:tt [$($h:tt)*] $($e:tt)*) => { |e1: Term| { exprapp_!($i $($e)*) (Term::HApp(Box::new(e1), hdlr!($i $($h)*))) } };
    ($i:tt $e2:tt $($e:tt)*) => { |e1: Term| { exprapp_!($i $($e)*) (Term::App(Box::new(e1), Box::new(expr_!($i $e2)))) } };
}
macro_rules! expr {
    ($($e:tt)*) => { expr_!(0 $($e)*) };
}
macro_rules! typ_ {
    ($i:tt ()) => { Type::Unit };
    ($i:tt ($($t:tt)+)) => { typ_!($i $($t)*) };
    ($i:tt fn($($s:tt)*)^[$($c:tt)*] $($t:tt)*) => { Type::Fn(Box::new(typ_!($i ($($s)*))), Box::new(typ_!($i $($t)*)), caps!($i $($c)*)) };
    ($i:tt fn($($s:tt)*) $($t:tt)*) => { typ_!($i fn($($s)*)^[] $($t)*) };
    ($i:tt fn^[$a:ident] $($t:tt)*) => { Type::FFn(Box::new({ let $a = MI($i, PhantomData::<Cap>); typ_!(($i+1) $($t)*) })) };
    //($i:tt fn^[$a:ident] $($t:tt)*) => { Type::FFn(Box::new(Type::Unit)) };
    ($i:tt fn[$h:ident : $F:ident]^[$($c:tt)*] $($t:tt)*) => { Type::HFn(stringify!($F).to_string(), Box::new({ let $h = MI($i, PhantomData::<Hdlr>);  typ_!(($i+1) $($t)*)}), caps!($i $($c)*)) };
    ($i:tt fn[$h:ident : $F:ident] $($t:tt)*) => { typ_!($i fn[$h: $F]^[] $($t)*) };
}
macro_rules! typ {
    ($($t:tt)*) => { typ_!(0 $($t)*) };
}
macro_rules! caps {
    ($i:tt $($c:expr),*) => { vec![$(Cap::from(($i, $c))),*] };
}
macro_rules! hdlr {
    ($i:tt $h:ident) => { Hdlr::from(($i, $h)) };
    ($i:tt handler^$l:tt $op:ident ($x:ident, $k:ident) $($e:tt)+) => {
        Hdlr::HH((stringify!($op).to_string(), Box::new({
            let ($x, $k) = (MI($i, PhantomData::<Term>), MI($i+1, PhantomData::<Term>));
            expr_!(($i+2) $($e)*)
            /*Term::V(Val::Unit)*/
        })), $l)
    };
}

fn main() {
    let unit = Term::X(4);
    let cap = Cap::A(5);
    let e = expr!(((fn^[_a] fn(x: ()) x) ^[cap]) unit);
    println!("{e:?}");
    let try_with = expr! {
        (DN^l : ()^[] . ((fn[h: yield] (UP h) ()) [handler^l yield(_x, k) k ()]))
    };
    println!("{try_with:?}");
    let mut sigs = Map::new();
    sigs.insert("yield".to_string(), (typ!(()), typ!(())));
    println!("{:?}", eval(&sigs, try_with));

    let fiterate = expr! {
        fn[h: yield] fn^[a] fn(tr: ()) fn(f: fn(())^[a] ())
            let _ : () = (f ());
            (UP h) tr
    };
    let ex3a = expr! {
        let g: (fn[h: yield] fn()^[h] ()) = (fn[h: yield] fn(x: ())
            let _ : () = (UP h); x);
        let fsize2: (fn^[a] fn() fn(fn()^[a] ()) ()) = (
            fn^[a] fn(tr: ()) fn(f: fn()^[a] ())
                f tr);
        let fsize1: (fn^[a] fn() fn(fn()^[a] ()) ()) = (
            fn^[a] fn(tr: ()) fn(f: fn()^[a] ())
                let num: () = ();
                let _ : () = (DN^l : ()^[] .
                    (fn[hi:yield]
                        fiterate [hi] ^[a] tr f)
                    [handler^l yield(_x, k) k()] );
                num
        );
        DN^l : ()^[] . (
            (fn[h:yield]
                fsize2 ^[h] () g)
            [handler^l yield(_x, k) k ()])
    };

    println!("{:?}", eval(&sigs, ex3a));
}
