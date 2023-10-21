#![allow(unused)]

// https://www.microsoft.com/en-us/research/uploads/prod/2023/05/fbip.pdf

use std::collections::HashMap as Map;
use std::rc::Rc;

type Var = String;
type Tup<T> = Vec<T>;

#[derive(Clone, Debug)]
enum Val {
    X(Var),
    C(String, Vec<Self>),
}

enum Expr {
    /// (v, ..., v)
    Tup(Tup<Val>),
    /// e e
    Apply(Rc<Self>, Rc<Self>),
    /// f(e; e)
    Call(String, Rc<Self>, Rc<Self>),
    /// let xbar = e in e
    Let(Tup<Var>, Rc<Self>, Rc<Self>),
    /// match e { (p |-> e)_bar }
    Match(Rc<Self>, Tup<(Pat, Self)>),
    /// match! e { (p |-> e)_bar }
    DMatch(Rc<Self>, Tup<(Pat, Self)>),
}

type Pat = (String, Vec<String>);
type FnDefs = Map<String, (Tup<Var>, Tup<Var>, Rc<Expr>)>;

#[derive(Clone)]
enum Env {
    Nil,
    Var(Rc<Self>, Var),
    Credit(Rc<Self>, usize),
}
impl Env {
    fn contains(&self, x: &Var) -> bool {
        match self {
            Env::Nil => false,
            Env::Var(g, y) if x == y => true,
            Env::Var(g, _) | Env::Credit(g, _) => g.contains(x),
        }
    }
}
type BEnv = Vec<Var>;

macro_rules! let_some {
    ($p:pat = $e1:expr => $e2:expr) => {
        if let $p = $e1 {
            Some($e2)
        } else {
            None
        }
    };
}

fn expr_wf(s: &FnDefs, d: &BEnv, g: &Env, e: &Expr) -> Option<()> {
    // D|G |- e
    // ------------ EMPTY
    // D|G,<>0 |- e
    if let Env::Credit(gtail, 0) = g {
        return expr_wf(s, d, gtail, e);
    }

    /// helper for expr_wf for vals
    ///
    /// expr_wf should check that g is ultimately consumed entirely
    /// but we can't do that in the intermediate steps because
    /// each value v can consume any number of elements of g
    fn val_wf<'g>(mut g: &'g Env, v: &Val) -> Option<&'g Env> {
        match v {
            //
            // -------- VAR
            // D|x |- x
            //
            Val::X(x) => match g {
                Env::Var(gout, y) if y == x => {
                    g = gout;
                }
                _ => return None,
            },
            //
            // --------- ATOM
            // D|{} |- C
            Val::C(c, vs) if vs.len() == 0 => {}
            // D|Gi |- vi
            // ----------------------------- REUSE
            // D|G1,...Gk,<>k |- Ck v1 ...vk
            Val::C(c, vs) => {
                match g {
                    Env::Credit(gn, k) if *k == vs.len() => {
                        g = gn;
                    }
                    _ => return None,
                }
                for v in vs {
                    g = val_wf(g, v)?;
                }
            }
        }
        Some(g)
    }

    fn single_var(e: &Expr) -> Option<&String> {
        let vbar = let_some! { Expr::Tup(vs) = e => vs}?;
        if vbar.len() != 1 {
            return None;
        }
        let_some! {Val::X(x) = &vbar[0] => x}
    }

    match e {
        // D|Gi |- vi
        // ------------------------ TUPLE
        // D|G1,...Gn |- (v1,...vn)
        //
        // also VAR, ATOM, REUSE
        Expr::Tup(xbar) => {
            let mut g = g;
            for x in xbar {
                g = val_wf(g, x)?;
            }

            // g should be consumed
            let_some! { Env::Nil = g => () }
        }
        // y \in D
        // D|G |- e
        // ---------- BAPP
        // D|G |- y e
        Expr::Apply(e1, e2) => {
            let y = single_var(e1)?;
            if !d.contains(y) {
                return None;
            }
            expr_wf(s, d, g, e2)
        }
        // ybar \in D,dom(Sig)
        // D|G |- e
        // ------------------- CALL
        // D|G |- f(ybar; e)
        Expr::Call(f, e1, e2) => {
            let ybar = let_some! { Expr::Tup(ybar) = &**e1 => ybar }?;
            // ybar \in D,dom(S)
            for y in ybar {
                let y = let_some! { Val::X(y) = y => y }?;
                if !d.contains(y) && !s.contains_key(y) {
                    return None;
                }
            }
            expr_wf(s, d, g, e2)
        }
        // D|G2,G3,xbar |- e2
        // D,G2|G1 |- e1
        // xbar \nin D,G2,G3
        // --------------------------------- LET
        // D|G1,G2,G3 |- let xbar = e1 in e2
        Expr::Let(xbar, e1, e2) => {
            // we could have out-env be unused env vars
            // which could split G1 from rest by
            //   D|G1,G2,G3,xbar |- e2 -| G1
            // but no idea how to split G2 from G3 for
            //   D,G2|G3 |- e1
            // maybe it's just "all bound vars after G1"
            // and G3 is optional tail of credits and vars?
            // because D can only contain vars
            todo!()
        }
        // y \in D  D,xbar_i|G |- ei
        // xbar_i \nin D,G
        // ---------------------------------- BMATCH
        // D|G |- match y {Ci xbar_i |-> ei }
        Expr::Match(e, cases) => {
            let y = single_var(e)?;
            // y \in D
            if !d.contains(y) {
                return None;
            }
            for ((c, xbar), e) in cases {
                // xbar \nin D,G
                for x in xbar {
                    if d.contains(x) || g.contains(x) {
                        return None;
                    }
                }
                // D,xbar_i|G |- ei
                let mut d = d.clone();
                d.extend(xbar.iter().cloned());
                expr_wf(s, &d, g, e)?;
            }
            Some(())
        }
        // D|G,xbar_i,<>k |- ei
        // k = |xbar_i|   xbar_i \nin D,G
        // -------------------------------------- DMATCH!
        // D|G,x |- match! x { Ci xbar_i |-> ei }
        Expr::DMatch(e, cases) => {
            let x = single_var(e)?;
            let (g, y) = let_some! { Env::Var(g, y) = g => (g, y)}?;
            if x != y {
                return None;
            }
            for ((c, xbar), e) in cases {
                // xbar_i \nin D,G
                for x in xbar {
                    if d.contains(x) || g.contains(x) {
                        return None;
                    }
                }
                // x = |xbar_i|
                let k = xbar.len();
                // D|G,xbar_i,<>k |- ei
                let g = xbar
                    .into_iter()
                    .fold(g.clone(), |acc, x| Rc::new(Env::Var(acc, x.clone())));
                let g = Env::Credit(g, k);
                expr_wf(s, d, &g, e)?;
            }
            Some(())
        }
    }
}

fn fndefs_wf(s: &FnDefs) -> Option<()> {
    //
    // ------ DEFBASE
    // ||- {}
    //
    // ||- S'   ybar|xbar |- e
    // ----------------------- DEFFUN
    // ||- S',f(ybar;xbar) = e
    for (f, (y, x, e)) in s {
        let d: &BEnv = y;
        let g: Env = x
            .into_iter()
            .fold(Env::Nil, |acc, x| Env::Var(Rc::new(acc), x.clone()));
        expr_wf(s, d, &g, e)?;
    }
    Some(())
}

enum EvalCtx {
    Hole,
    ApplyL(Box<Self>, Box<Expr>),
    ApplyR(Tup<Val>, Box<Self>),
    CallL(String, Box<Self>, Box<Expr>),
    CallR(String, Tup<Val>, Box<Self>),
    Let(Tup<Var>, Box<Self>, Box<Expr>),
    Match(Box<Self>, Vec<(Pat, Expr)>),
    DMatch(Box<Self>, Vec<(Pat, Expr)>),
}

fn eval(s: &FnDefs, e: Expr) -> Result<Val, (EvalCtx, Expr)> {
    /// replace tuple of vars xbar with corresponding values in vbar
    /// e[xbar:=vbar]
    fn subst(e: &Expr, xbar: &[Var], vbar: Tup<Val>) -> Expr {
        todo!()
    }
    enum EvalStep {
        Let(Tup<Var>, Tup<Val>, Expr),
        Call(String, Tup<Val>, Tup<Val>),
        App(Tup<Val>, Tup<Val>),
        Match(Tup<Val>, Vec<(Pat, Expr)>),
        DMatch(Tup<Val>, Vec<(Pat, Expr)>),
    }

    fn eval_inner(s: &FnDefs, e: EvalStep) -> Result<Expr, Expr> {
        fn etup(v: Tup<Val>) -> Rc<Expr> {
            Rc::new(Expr::Tup(v))
        }
        match e {
            EvalStep::Let(xbar, vbar, e) => Ok(subst(&e, &xbar, vbar)),
            EvalStep::Call(f, v1bar, v2bar) => {
                let call = || {
                    let (ybar, xbar, e) = s.get(&f)?;
                    let e = subst(e, ybar, v1bar);
                    Some(subst(&e, xbar, v2bar))
                };
                match call() {
                    Some(e) => Ok(e),
                    None => Err(Expr::Call(f, etup(v1bar), etup(v2bar))),
                }
            }
            EvalStep::App(mut fbar, v2bar) => {
                let call = || {
                    let f = let_some! { (Some(Val::X(f)), None) = (fbar.pop(), fbar.pop()) => f }?;
                    let (ybar, xbar, e) = s.get(&f)?;
                    if !ybar.is_empty() {
                        return None;
                    }
                    Some(subst(e, xbar, v2bar))
                };
                match call() {
                    Some(e) => Ok(e),
                    None => Err(Expr::Apply(etup(fbar), etup(v2bar))),
                }
            }
            EvalStep::Match(mut vbar, cases) | EvalStep::DMatch(mut vbar, cases) => {
                let (c, vbar) = let_some! { (Some(Val::C(c, vbar)), None) = (vbar.pop(), vbar.pop()) => (c, vbar) }?;
                let ((ci, xbar), e) = cases.into_iter().find(|((ci, _), _)| ci == &c)?;
                if xbar.len() == vbar.len() {
                    Some(subst(&e, &xbar, vbar))
                } else {
                    None
                }
            }
        }
    }

    fn eval_step(s: &FnDefs, ee: EvalCtx, vbar: Tup<Val>) -> Result<Tup<Val>, (EvalCtx, Expr)> {
        match ee {
            EvalCtx::Hole => Ok(vbar),
            EvalCtx::ApplyL(ee, e) => Err(match eval_step(s, *ee, vbar) {
                Ok(vbar) => (EvalCtx::ApplyR(vbar, Box::new(EvalCtx::Hole)), *e),
                Err((ee, enext)) => (EvalCtx::ApplyL(Box::new(ee), e), enext),
            }),
            EvalCtx::ApplyR(lvbar, ee) => Err(match eval_step(s, *ee, vbar) {
                Ok(vbar) => (
                    EvalCtx::Hole,
                    Expr::Apply(Rc::new(Expr::Tup(lvbar.clone())), Rc::new(Expr::Tup(vbar))),
                ),
                Err((ee, enext)) => (EvalCtx::ApplyR(lvbar, Box::new(ee)), enext),
            }),
            EvalCtx::CallL(f, ee, e) => Err(match eval_step(s, *ee, vbar) {
                Ok(vbar) => (EvalCtx::CallR(f, vbar, Box::new(EvalCtx::Hole)), *e),
                Err((ee, enext)) => (EvalCtx::CallL(f, Box::new(ee), e), enext),
            }),
            EvalCtx::CallR(f, lvbar, ee) => Err(match eval_step(s, *ee, vbar) {
                Ok(vbar) => (
                    EvalCtx::Hole,
                    Expr::Call(f, Rc::new(Expr::Tup(lvbar)), Rc::new(Expr::Tup(vbar))),
                ),
                Err((ee, enext)) => (EvalCtx::CallR(f, lvbar, Box::new(ee)), enext),
            }),
            EvalCtx::Let(xbar, ee, e) => Err(match eval_step(s, *ee, vbar) {
                Ok(vbar) => (
                    EvalCtx::Hole,
                    Expr::Let(xbar, Rc::new(Expr::Tup(vbar)), Rc::new(*e)),
                ),
                Err((ee, enext)) => (EvalCtx::Let(xbar, Box::new(ee), e), enext),
            }),
            EvalCtx::Match(ee, cases) => Err(match eval_step(s, *ee, vbar) {
                Ok(vbar) => (EvalCtx::Hole, Expr::Match(Rc::new(Expr::Tup(vbar)), cases)),
                Err((ee, enext)) => (EvalCtx::Match(Box::new(ee), cases), enext),
            }),
            EvalCtx::DMatch(ee, cases) => Err(match eval_step(s, *ee, vbar) {
                Ok(vbar) => (EvalCtx::Hole, Expr::DMatch(Rc::new(Expr::Tup(vbar)), cases)),
                Err((ee, enext)) => (EvalCtx::DMatch(Box::new(ee), cases), enext),
            }),
        }
    }

    todo!()
}

fn main() {}
