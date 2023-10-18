#![allow(unused)]

// https://web.archive.org/web/20140917015759/http://www.eecs.harvard.edu/~greg/cs256sp2005/lec16.txt

use log::debug;
use std::collections::HashMap as Map;
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Debug)]
struct Idx(usize); // DeBruijn index

#[derive(Clone, PartialEq, Debug)]
enum Term {
    Unit,
    Var(Idx),
    Fun(Rc<Type>, Rc<Term>),
    FunT(Rc<Kind>, Rc<Term>),
    App(Rc<Term>, Rc<Term>),
    AppT(Rc<Term>, Rc<Type>),
}

#[derive(Clone, PartialEq, Debug)]
enum Type {
    Unit,
    Var(Idx),
    Arrow(Rc<Type>, Rc<Type>),
    FunT(Rc<Kind>, Rc<Type>),
    AppT(Rc<Type>, Rc<Type>),
}

#[derive(Clone, PartialEq, Debug)]
enum Kind {
    Type,
    Arrow(Rc<Kind>, Rc<Kind>),
}

#[derive(Debug)]
enum Binding<E, T> {
    Term(Rc<E>),
    Type(Rc<T>),
}

impl<E, T> std::clone::Clone for Binding<E, T> {
    fn clone(&self) -> Self {
        match self {
            Binding::Term(e) => Binding::Term(e.clone()),
            Binding::Type(t) => Binding::Type(t.clone()),
        }
    }
}

#[derive(Default, Clone, Debug)]
struct Ctx<E, T>(Vec<Binding<E, T>>);

impl<E: Clone, T: Clone> Ctx<E, T> {
    fn with_term(&self, t: E) -> Self {
        let mut ret = self.clone();
        ret.0.push(Binding::Term(Rc::new(t)));
        ret
    }
    fn with_type(&self, k: T) -> Self {
        let mut ret = self.clone();
        ret.0.push(Binding::Type(Rc::new(k)));
        ret
    }
    fn proj(&self, i: usize) -> Option<&Binding<E, T>> {
        if i < self.0.len() {
            Some(&self.0[self.0.len() - i - 1])
        } else {
            None
        }
    }
    fn get_term(&self, i: &Idx) -> Option<&E> {
        match self.proj(i.0) {
            Some(Binding::Term(e)) => Some(e.as_ref()),
            _ => None,
        }
    }
    fn get_type(&self, i: &Idx) -> Option<&T> {
        match self.proj(i.0) {
            Some(Binding::Type(t)) => Some(t.as_ref()),
            _ => None,
        }
    }
}

impl Type {
    fn arrow(t1: &Type, t2: &Type) -> Type {
        Type::Arrow(Rc::new(t1.clone()), Rc::new(t2.clone()))
    }
}

fn subst_termvar(e: &Term, a: usize, b: Term) -> Term {
    debug!("subst_termvar({e}, #{a}, {b})");
    match e {
        Term::Unit => Term::Unit,
        &Term::Var(Idx(x)) if x == a => b,
        Term::Var(x) => Term::Var(x.clone()),
        Term::Fun(t, e) => Term::Fun(t.clone(), Rc::new(subst_termvar(e, a + 1, b))),
        Term::FunT(k, e) => Term::FunT(k.clone(), Rc::new(subst_termvar(e, a + 1, b))),
        Term::App(e1, e2) => Term::App(
            Rc::new(subst_termvar(e1, a, b.clone())),
            Rc::new(subst_termvar(e2, a, b)),
        ),
        Term::AppT(e, t) => Term::AppT(Rc::new(subst_termvar(e, a, b)), t.clone()),
    }
}

fn subst_termtypevar(e: &Term, a: usize, b: Type) -> Term {
    match e {
        Term::Fun(t, e) => Term::Fun(
            Rc::new(subst_typevar(t, a, b.clone())),
            Rc::new(subst_termtypevar(e, a + 1, b)),
        ),
        Term::FunT(k, e) => Term::FunT(k.clone(), Rc::new(subst_termtypevar(e, a + 1, b))),
        Term::AppT(e, t) => Term::AppT(
            Rc::new(subst_termtypevar(e, a, b.clone())),
            Rc::new(subst_typevar(t, a, b)),
        ),
        _ => e.clone(),
    }
}

fn subst_typevar(t: &Type, a: usize, b: Type) -> Type {
    debug!("subst_typevar({t}, #[{a}], {b})");
    match t {
        Type::Unit => Type::Unit,
        &Type::Var(Idx(x)) if x == a => b,
        Type::Var(x) => Type::Var(x.clone()),
        Type::Arrow(t1, t2) => Type::Arrow(
            Rc::new(subst_typevar(t1, a, b.clone())),
            Rc::new(subst_typevar(t2, a, b)),
        ),
        Type::FunT(k, t) => Type::FunT(k.clone(), Rc::new(subst_typevar(t, a + 1, b))),
        Type::AppT(t1, t2) => Type::AppT(
            Rc::new(subst_typevar(t1, a, b.clone())),
            Rc::new(subst_typevar(t2, a, b)),
        ),
    }
}

type Ctx1 = Ctx<Rc<Type>, Rc<Kind>>;

fn kind_check(g: &Ctx1, t: &Type, k: &Kind) -> Option<()> {
    let kexpected = kind_synth(g, t)?;
    debug!("kind_check({kexpected} == {k})");
    (&kexpected == k).then(|| ())
}

fn kind_synth(g: &Ctx1, t: &Type) -> Option<Kind> {
    debug!("kind_synth({g}, {t})");
    match t {
        Type::Unit => Some(Kind::Type),
        Type::Var(a) => g.get_type(a).map(|k| (**k).clone()),
        //
        // ---------------------
        // G |- -> : * -> * -> *
        Type::Arrow(t1, t2) => {
            let ktype = Rc::new(Kind::Type);
            kind_check(g, t1, &ktype)?;
            kind_check(g, t2, &ktype)?;
            Some(Kind::Arrow(
                ktype.clone(),
                Rc::new(Kind::Arrow(ktype.clone(), ktype)),
            ))
        }
        // G,a:k |- t : k1
        // ----------------------
        // G |- \a:k.t : k -> k1
        Type::FunT(k, t) => {
            let g2 = g.with_type(k.clone());
            let k2 = kind_synth(&g2, t)?;
            Some(Kind::Arrow(k.clone(), Rc::new(k2)))
        }
        // G |- t1 : k1 -> k
        // G |- t2 : k1
        // -----------------
        // G |- t1 t2 : k
        Type::AppT(t1, t2) => {
            let k2 = kind_synth(g, t2)?;
            let k1 = kind_synth(g, t1)?;
            match k1 {
                Kind::Arrow(k1, k) if k1.as_ref() == &k2 => Some((*k).clone()),
                _ => None,
            }
        }
    }
}

fn type_check(g: &Ctx1, e: &Term, t: &Type) -> Option<()> {
    let texpected = type_synth(g, e)?;
    let g0 = Ctx(vec![]);
    let texpected = eval_type(&g0, &texpected);
    let tactual = eval_type(&g0, t);
    debug!("type_check({texpected} == {tactual})");
    (texpected == tactual).then(|| ())
}

fn type_synth(g: &Ctx1, e: &Term) -> Option<Type> {
    debug!("type_synth({g}, {e})");
    match e {
        //
        // -------------
        // G |- (): Unit
        Term::Unit => Some(Type::Unit),
        // x: t \in G
        // ----------
        // G |- x: t
        Term::Var(x) => g.get_term(x).map(|rc| (**rc).clone()),
        // G,x:t |- e : t2
        // -----------------------
        // G |- \x:t.e : t -> t2
        Term::Fun(t, e) => {
            let g2 = g.with_term(t.clone());
            let t2 = type_synth(&g2, e)?;
            Some(Type::arrow(t.as_ref(), &t2))
        }
        // G,a:k |- e: t
        // ---------------------
        // G |- /\a:k.e : \a:k.t
        Term::FunT(k, e) => {
            let g2 = g.with_type(k.clone());
            let t = type_synth(&g2, e)?;
            Some(Type::FunT(k.clone(), Rc::new(t)))
        }
        // G |- e1 : t2 -> t
        // G |- e2 : t2
        // -----------------
        // G |- e1 e2 : t
        Term::App(e1, e2) => {
            let t2 = type_synth(g, e2)?;
            let t1 = type_synth(g, e1)?;
            match t1 {
                Type::Arrow(t3, t4) => {
                    let g0 = Ctx(vec![]);
                    let t2 = eval_type(&g0, &t2);
                    let t3 = eval_type(&g0, &t3);
                    if t2 == t3 {
                        Some(t4.as_ref().clone())
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        // G |- e : \a:k.t1
        // G |- t : k
        // ------------------
        // G |- e t : t1[a/t]
        Term::AppT(e, t) => {
            let akt1 = type_synth(g, e)?;
            match akt1 {
                Type::FunT(k, t1) => {
                    kind_check(g, t, k.as_ref())?;
                    Some(subst_typevar(t1.as_ref(), 0, (**t).clone()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

type Ctx0 = Ctx<Term, Type>;

fn eval(g: &Ctx0, e: &Term) -> Term {
    debug!("eval({g}, {e})");
    match e {
        Term::Unit => Term::Unit,
        // x=v \in G
        // ------------
        // G |- x --> v
        Term::Var(x) => g.get_term(&x).expect("bad type").clone(),
        Term::Fun(t, e) => Term::Fun(Rc::new(eval_type(g, t)), e.clone()),
        Term::FunT(k, e) => Term::FunT(k.clone(), e.clone()),
        // G |- e1 --> \x:t.e3
        // G |- e2 --> e4
        // G,x=e4 |- e3 --> e
        // -------------------
        // G |- e1 e2 --> e
        Term::App(e1, e2) => {
            let e1 = eval(g, e1);
            match e1 {
                Term::Fun(_t, e1) => {
                    let e2 = eval(g, e2);
                    eval(&g.with_term(e2), e1.as_ref())
                }
                _ => unreachable!("bad type"),
            }
        }
        // G |- e --> /\a:k.e1
        // G |- t --> t1
        // G |- e1[a/t1] --> e2
        // -------------------
        // G |- e t --> e2
        Term::AppT(e, t) => {
            let e = eval(g, e);
            match e {
                Term::FunT(_k, e) => {
                    let t = eval_type(g, t);
                    let e2 = subst_termtypevar(&e, 0, t);
                    eval(g, &e2)
                }
                _ => unreachable!("bad type"),
            }
        }
    }
}

fn eval_type(g: &Ctx0, t: &Type) -> Type {
    debug!("eval_type({g}, {t})");
    match t {
        Type::Unit => Type::Unit,
        // a=t \in G
        // ------------
        // G |- a --> t
        Type::Var(a) => match g.proj(a.0) {
            Some(Binding::Term(_)) => unreachable!("bad kind"),
            Some(Binding::Type(t)) => (**t).clone(),
            None => Type::Var(*a),
        },
        Type::Arrow(t1, t2) => Type::Arrow(Rc::new(eval_type(g, t1)), Rc::new(eval_type(g, t2))),
        Type::FunT(k, t) => Type::FunT(k.clone(), t.clone()),
        // G |- t1 --> \a:k.t3
        // G |- t2 --> t4
        // G,a=t4 |- t3 --> t
        // -------------------
        // G |- t1 t2 --> t
        Type::AppT(t1, t2) => {
            let t1 = eval_type(g, t1);
            match t1 {
                Type::FunT(_k, t) => {
                    let t2 = eval_type(g, t2);
                    let g2 = g.with_type(t2);
                    eval_type(&g2, t.as_ref())
                }
                _ => unreachable!("bad kind"),
            }
        }
    }
}

use std::fmt::{Debug, Display};
impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Unit => f.write_str("{}"),
            Term::Var(Idx(x)) => write!(f, "#{x}"),
            Term::Fun(t, e) => write!(f, "(fun({t}) {e})"),
            Term::FunT(k, e) => write!(f, "(fun[{k}] {e})"),
            Term::App(e1, e2) => write!(f, "{e1}({e2})"),
            Term::AppT(e, t) => write!(f, "{e}[{t}]"),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unit => f.write_str("1"),
            Type::Var(Idx(x)) => write!(f, "#[{x}]"),
            Type::Arrow(t1, t2) => write!(f, "({t1} -> {t2})"),
            Type::FunT(k, t) => write!(f, "fun[{k}] {t}"),
            Type::AppT(t1, t2) => write!(f, "{t1}[{t2}]"),
        }
    }
}

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Type => f.write_str("*"),
            Kind::Arrow(k1, k2) => write!(f, "({k1} -> {k2})"),
        }
    }
}

impl<E: Display, T: Display> Display for Ctx<E, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.len() == 0 {
            return f.write_str("{}");
        }

        for (c, v) in std::iter::once("")
            .chain(std::iter::repeat(","))
            .zip(self.0.iter())
        {
            match v {
                Binding::Term(e) => write!(f, "{c}{e}")?,
                Binding::Type(t) => write!(f, "{c}{t}")?,
            }
        }
        Ok(())
    }
}

fn main() {
    env_logger::init();
    use {Idx as I, Kind as K, Term as E, Type as T};
    fn rc<T>(v: T) -> Rc<T> {
        Rc::new(v)
    }
    let g = Ctx(vec![]);
    let expr = E::FunT(
        rc(K::Arrow(rc(K::Type), rc(K::Type))),
        rc(E::FunT(
            rc(K::Type),
            rc(E::Fun(
                rc(T::AppT(rc(T::Var(I(1))), rc(T::Var(I(0))))),
                rc(E::Var(I(0))),
            )),
        )),
    );
    println!("{g} |- {expr} : {}", type_synth(&g, &expr).unwrap());
    let typ_id = T::FunT(rc(Kind::Type), rc(T::Var(Idx(0))));
    println!(
        "eval {expr} {typ_id}  --->  {}",
        eval(
            &Ctx(vec![]),
            &E::AppT(
                rc(E::AppT(rc(expr.clone()), rc(typ_id.clone()))),
                rc(T::Unit)
            ),
        )
    );
}
