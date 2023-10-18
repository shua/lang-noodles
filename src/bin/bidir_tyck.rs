#![allow(unused)]

/// messing around with https://arxiv.org/abs/1306.6032 "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"
use std::fmt::Debug;

const DEBUG: bool = true;
macro_rules! debug {
    ($fmt:literal $(, $arg:expr)*) => {
        if DEBUG {
            print!("DBG: "); println!($fmt, $(, $arg)*);
        }
    }
}

type TVar = &'static str;

/// T represents types
/// t0 ::= Unit | x | t0 -> t0    ; monotypes
/// t ::= t0 | Pi x. t0 | t -> t  ; types
#[derive(Clone, PartialEq)]
enum T {
    /// Unit type
    U,
    /// x  type variable
    V(TVar),
    /// a  existential type variable
    X(usize),
    /// Pi x. t  pi type constructor
    P(TVar, Box<Self>),
    /// t -> t  arrow type
    A(Box<Self>, Box<Self>),
}

impl Debug for T {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            T::U => write!(f, "1"),
            T::V(x) => write!(f, "{x}"),
            T::X(y) => write!(f, "${y}"),
            T::P(x, t) => write!(f, "\\A{x}.{t:?}"),
            T::A(a, b) => write!(f, "{a:?}->{b:?}"),
        }
    }
}

/// B is a contextual bound
/// B ::= x | x: t | a | a = t0 | @a
#[derive(Clone, PartialEq)]
enum B {
    /// x term variable
    V(TVar),
    /// x:t term type bound
    Is(TVar, T),
    /// a existential type variable
    Ex(usize),
    /// a = t  existential type bound
    Eq(usize, T), // T should be a monotype, ie T::P is not allowed
    /// @a  existential marker
    M(usize),
}

impl Debug for B {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            B::V(x) => write!(f, "{x}"),
            B::Is(x, t) => write!(f, "{x}: {t:?}"),
            B::Ex(y) => write!(f, "${y}"),
            B::Eq(y, t) => write!(f, "${y} = {t:?}"),
            B::M(y) => write!(f, "@{y}"),
        }
    }
}

type Ctx = [B];

fn new_id() -> usize {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    COUNTER.fetch_add(1, Ordering::SeqCst)
}

/// E is terms
/// e ::= () | \x. e | e e | e: t | x
enum E {
    /// ()  unit
    U,
    /// \x. e  lambda expression
    L(&'static str, Box<E>),
    /// e e  application
    A(Box<E>, Box<E>),
    /// e: t  type ascription
    T(Box<E>, T),
    /// x  variable
    V(&'static str),
}

impl Debug for E {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            E::U => write!(f, "()"),
            E::L(x, e) => write!(f, "\\{x}.{e:?}"),
            E::A(a, b) => write!(f, "{a:?}({b:?})"),
            E::T(x, t) => write!(f, "{x:?}:{t:?}"),
            E::V(x) => write!(f, "{x}"),
        }
    }
}

impl T {
    fn a(a: T, b: T) -> T {
        T::A(Box::new(a), Box::new(b))
    }

    fn is_mono(&self) -> bool {
        match self {
            T::U | T::V(_) | T::X(_) => true,
            T::P(_, _) => false,
            T::A(a, b) => a.is_mono() && b.is_mono(),
        }
    }

    /// judgements of G |- t type
    fn well_formed(&self, ctx: &Ctx) -> bool {
        let wf = match self {
            //
            // ------------
            // G |- Unit wf
            T::U => true,
            // this seems questionable to me, do we need to
            // distinguish between type and term vars?
            //
            // x \in G
            // -----------
            // G |- x type
            T::V(v) => ctx.contains(&B::V(v)),
            // a \in G        a=t \in G
            // -----------    -----------
            // G |- a type    G |- a type
            T::X(v) => ctx.iter().any(|b| match b {
                B::Ex(x) | B::Eq(x, _) => x == v,
                _ => false,
            }),
            // G,x |- t type
            // -----------------
            // G |- Pi x. t type
            T::P(v, t) => {
                let mut ctx = ctx.to_vec();
                ctx.push(B::V(v));
                t.well_formed(&ctx)
            }
            // G |- t1 type
            // G |- t2 type
            // ------------------
            // G |- t1 -> t2 type
            T::A(a, b) => a.well_formed(&ctx) && b.well_formed(&ctx),
        };
        debug!("WF        {ctx:?} |- {self:?}  : {wf}");
        wf
    }

    // substitution
    fn apply_ctx(&self, ctx: &Ctx) -> T {
        let t = match self {
            // Unit[G] => Unit
            T::U => T::U,
            // x[G] => x
            T::V(a) => T::V(a),
            // a[G1,a,G2] => a
            // a[G1,a=t,G2] => t[G1,a=t,G2]
            T::X(a) => {
                if ctx.contains(&B::Ex(*a)) {
                    T::X(*a)
                } else {
                    match ctx.iter().filter(|b| matches!(b, B::Eq(_, _))).next() {
                        Some(B::Eq(_, t)) => t.apply_ctx(ctx),
                        _ => panic!("typing context is not well-formed"),
                    }
                }
            }
            // (Pi x.t)[G] => Pi x.(t[G])
            T::P(x, a) => T::P(x, Box::new(a.apply_ctx(ctx))),
            // (t1 -> t2)[G] => t1[G] -> t2[G]
            T::A(a, b) => T::A(Box::new(a.apply_ctx(ctx)), Box::new(b.apply_ctx(ctx))),
        };
        debug!("CTX_APPLY [{ctx:?}]{self:?}   = {t:?}");
        t
    }

    /// in t, substitute b for any occurence of a
    fn subst(&mut self, a: &T, b: T) {
        let dbg_before = format!("[{a:?}/{b:?}]{self:?}");
        if self == a {
            *self = b;
            debug!("SUBST     {dbg_before}   = {self:?}");
            return;
        }
        match self {
            T::U | T::V(_) | T::X(_) => {}
            T::P(_, c) => c.subst(a, b),
            T::A(c, d) => {
                c.subst(a, b.clone());
                d.subst(a, b);
            }
        }
        debug!("SUBST     {dbg_before}   = {self:?}");
    }

    /// a \nin free_vars(t)
    fn nin_free(&self, a: usize) -> bool {
        let res = match self {
            T::U | T::V(_) => true,
            &T::X(b) => a == b,
            T::P(_, c) => c.nin_free(a),
            T::A(b, c) => b.nin_free(a) && c.nin_free(a),
        };
        debug!("NIN_FREE  ${a} \\nin FV({self:?})   : {res}");
        res
    }

    // subtyping relation  G |- t2 :< t1 -| D
    fn subtype(&self, ctx: &Ctx, rhs: &Self) -> Option<Vec<B>> {
        let d = match (self, rhs) {
            //
            // ----------------
            // G |- t :< t -| G  in easy cases like Unit, or x \in G -> x :< x
            (T::U, T::U) => Some(ctx.to_vec()),
            (T::V(a), T::V(b)) if a == b && ctx.contains(&B::V(*a)) => Some(ctx.to_vec()),
            (T::X(a), T::X(b)) if a == b && ctx.contains(&B::Ex(*a)) => Some(ctx.to_vec()),
            // G  |- t3 :< t1 -| G1
            // G1 |- t2[G1] :< t4[G1] -| D
            // ---------------------------------
            // G  |- t1 -> t2  :<  t3 -> t4 -| D
            (T::A(a1, a2), T::A(b1, b2)) => {
                let m = b1.subtype(ctx, a1)?;
                let (a2, b2) = (a2.apply_ctx(&m), b2.apply_ctx(&m));
                a2.subtype(&m, &b2)
            }
            // G,@a,a |- t1[x/a] :< t2 -| D,@a,D1
            // ----------------------------------
            // G |- Pi x. t1 :< t2 -| D
            (T::P(x, a), b) => {
                let y = new_id();
                let mut a = a.clone();
                a.subst(&T::V(x), T::X(y));
                let mut ctx = ctx.to_vec();
                let mark = B::M(y);
                ctx.extend([mark.clone(), B::Ex(y)]);
                let mut d = a.subtype(&ctx, b)?;
                truncate_ctx(&mut d, &mark)
                    .expect("input context contained marker not found in output context");
                Some(d)
            }
            // G,x |- t1 :< t2 -| D,x,D1
            // -------------------------
            // G |- t1 :< Pi x. t2 -| D
            (a, T::P(x, b)) => {
                let mut ctx = ctx.to_vec();
                let mark = B::V(x);
                ctx.push(mark.clone());
                let mut d = a.subtype(&ctx, b)?;
                truncate_ctx(&mut d, &mark)
                    .expect("output context did not contain expected variable");
                Some(d)
            }
            // a \nin FV(t)
            // a \in G
            // G |- ??? -| D
            // ----------------
            // G |- a :< t -| D
            (T::X(a), b) => {
                if !(b.nin_free(*a) && ctx.contains(&B::Ex(*a))) {
                    return None;
                }
                b.subtype_inst(*a, ctx, true)
            }
            // a \nin FV(t)
            // a \in G
            // G |- ??? -| D
            // ----------------
            // G |- t :< a -| D
            (a, T::X(b)) => {
                if !(a.nin_free(*b) && ctx.contains(&B::Ex(*b))) {
                    return None;
                }
                a.subtype_inst(*b, ctx, false)
            }
            _ => None,
        };
        if let Some(d) = &d {
            debug!("SUBTYPE   {ctx:?} |- {self:?} <: {rhs:?} -| {d:?}");
        }
        d
    }

    /// judgements of form  G |- t :=< a -| D   or   G |- a :=< t -| D
    fn subtype_inst(&self, a: usize, ctx: &Ctx, left: bool) -> Option<Vec<B>> {
        // every judgement requires G[a], so find it upfront
        let i = ctx.iter().enumerate().find(|(_, b)| b == &&B::Ex(a))?.0;
        // G = Gi,@a,Gn

        let d = match self {
            // Inst?Solve
            //
            // mono(t)
            // Gi |- t type
            // -------------------------
            // G |- t :=< a -| Gi,a=t,Gn
            // G |- a :=< t -| Gi,a=t,Gn
            t if t.is_mono() && t.well_formed(&ctx[..i]) => {
                let mut d = ctx.to_vec();
                d[i] = B::Eq(a, t.clone());
                Some(d)
            }
            // Inst?Reach
            &T::X(b) => {
                let (i, _) = ctx
                    .iter()
                    .enumerate()
                    .skip(i + 1)
                    .find(|(_, c)| c == &&B::Ex(b))?;
                let mut d = ctx.to_vec();
                d[i] = B::Eq(b, T::X(a));
                Some(d)
            }
            // Inst?Arr
            T::A(b1, b2) => {
                let mut g = ctx[..i].to_vec();
                let a2 = new_id();
                let a1 = new_id();
                g.extend([
                    B::Ex(a2),
                    B::Ex(a1),
                    B::Eq(a, T::A(Box::new(T::X(a1)), Box::new(T::X(a2)))),
                ]);
                g.extend(ctx.iter().skip(i + 1).map(|b| b.clone()));
                let m = b1.subtype_inst(a1, &g, !left)?;
                let b2 = b2.apply_ctx(&m);
                b2.subtype_inst(a2, &m, left)
            }
            // Inst?AII?
            T::P(x, b) => {
                let mut g = ctx.to_vec();
                let mut b = b.clone();
                let mark = if left {
                    g.push(B::V(x));
                    B::V(x)
                } else {
                    let y = new_id();
                    g.extend([B::M(y), B::Ex(y)]);
                    b.subst(&T::V(x), T::X(y));
                    B::M(y)
                };
                let mut d = b.subtype_inst(a, &g, left)?;
                truncate_ctx(&mut d, &mark)
                    .expect(&format!("expected output context to contain {mark:?}"));
                Some(d)
            }
            _ => None,
        };
        if let Some(d) = &d {
            let s = if left {
                format!("${a} :=< {self:?}")
            } else {
                format!("{self:?} <=: ${a}")
            };
            debug!("INST*     {ctx:?} |- {s} -| {d:?}")
        }
        d
    }

    fn synth(&self, ctx: &Ctx, e: &E) -> Option<(T, Vec<B>)> {
        let d = match self {
            &T::X(x) => {
                let (i, _) = ctx.iter().enumerate().rfind(|(_, b)| b == &&B::Ex(x))?;
                let a1 = new_id();
                let a2 = new_id();
                let mut g = ctx[..i].to_vec();
                g.extend([B::Ex(a2), B::Ex(a1), B::Eq(x, T::a(T::X(a1), T::X(a2)))]);
                g.extend(ctx.iter().skip(i).map(|b| b.clone()));
                let d = e.check(&g, &T::X(a1))?;
                Some((T::X(a2), d))
            }
            T::P(x, a) => {
                let mut g = ctx.to_vec();
                let a1 = new_id();
                g.push(B::Ex(a1));
                let mut a = a.clone();
                a.subst(&T::V(x), T::X(a1));
                a.synth(&g, e)
            }
            T::A(a, b) => {
                let d = e.check(ctx, a)?;
                Some((*b.clone(), d))
            }
            _ => None,
        };
        if let Some((t, d)) = &d {
            debug!("TSYNTH     {ctx:?} |- {self:?} @ {e:?} =>> {t:?} -| {d:?}");
        }
        d
    }
}

impl E {
    fn check(&self, ctx: &Ctx, t: &T) -> Option<Vec<B>> {
        // Sub
        if let Some((a, m)) = self.synth(ctx) {
            let (a, b) = (t.apply_ctx(&m), a.apply_ctx(&m));
            if let Some(d) = a.subtype(&m, &b) {
                debug!("ECHECK    {ctx:?} |- {self:?} <= {t:?} -| {d:?}");
                return Some(d);
            }
        }

        let d = match (self, t) {
            // 1I
            (E::U, T::U) => Some(ctx.to_vec()),
            // AllI
            (e, T::P(x, a)) => {
                let mut g = ctx.to_vec();
                g.push(B::V(x));
                let mut d = e.check(&g, &*a)?;
                truncate_ctx(&mut d, &B::V(x))
                    .expect("variable bound in input context, not found in output context");
                Some(d)
            }
            // ->I
            (E::L(x, e), T::A(a, b)) => {
                let mut g = ctx.to_vec();
                let mark = B::Is(x, *a.clone());
                g.push(mark.clone());
                let mut d = e.check(&g, &b)?;
                truncate_ctx(&mut d, &mark)
                    .expect("variable annotated in input context, not found in output context");
                Some(d)
            }
            _ => None,
        };
        if let Some(d) = &d {
            debug!("ECHECK    {ctx:?} |- {self:?} <= {t:?} -| {d:?}");
        }
        d
    }

    fn synth(&self, ctx: &Ctx) -> Option<(T, Vec<B>)> {
        // Var
        if let E::V(x) = self {
            if let Some(t) =
                ctx.iter()
                    .rev()
                    .find_map(|t| if let B::Is(x, t) = t { Some(t) } else { None })
            {
                debug!("ESYNTH    {ctx:?} |- {self:?} => {t:?} -| {ctx:?}");
                return Some((t.clone(), ctx.to_vec()));
            }
        }

        let d = match self {
            // Anno
            E::T(e, t) => {
                if !t.well_formed(&ctx) {
                    return None;
                }
                let d = e.check(&ctx, &t)?;
                Some((t.clone(), d))
            }
            // 1I=>
            E::U => Some((T::U, ctx.to_vec())),
            // ->I=>
            E::L(x, e) => {
                let a = new_id();
                let b = new_id();
                let mut g = ctx.to_vec();
                let mark = B::Is(x, T::X(a));
                g.extend([B::Ex(a), B::Ex(b), mark.clone()]);
                let mut d = e.check(&g, &T::X(b))?;
                truncate_ctx(&mut d, &mark)
                    .expect("variable annotated in input context, not found in output context");
                Some((T::a(T::X(a), T::X(b)), d))
            }
            // ->E
            E::A(e1, e2) => {
                let (mut a, m) = e1.synth(ctx)?;
                a.apply_ctx(&m);
                let (c, d) = a.synth(&m, e2)?;
                Some((c, d))
            }
            _ => None,
        };
        if let Some((t, d)) = &d {
            debug!("ESYNTH    {ctx:?} |- {self:?} => {t:?} -| {d:?}");
        }
        d
    }
}

/// search for a marker @a in context and take the prefix
/// D1,@a,D2 => D1
fn truncate_ctx(ctx: &mut Vec<B>, mark: &B) -> Option<()> {
    let (i, _) = ctx.iter().enumerate().rfind(|(_, b)| b == &mark)?;
    ctx.truncate(i);
    Some(())
}

fn well_formed_ctx(ctx: &Ctx) -> bool {
    if ctx.is_empty() {
        return true;
    }

    let last = &ctx[ctx.len() - 1];
    let g = &ctx[..ctx.len() - 2];
    if !well_formed_ctx(g) {
        return false;
    }

    // `t \nin dom(G)` is not really defined in the paper,
    // this is my best guess, it doesn't recurse into the
    // types `t` in `a = t` or `x: t`
    fn nin_dom(a: T, g: &[B]) -> bool {
        for b in g {
            match b {
                B::V(x) | B::Is(x, _) => match &a {
                    &T::V(y) if *x == y => return false,
                    _ => {}
                },
                B::Ex(x) | B::Eq(x, _) | B::M(x) => match &a {
                    &T::X(y) if *x == y => return false,
                    _ => {}
                },
            }
        }
        true
    }

    match last {
        B::V(a) => well_formed_ctx(g) && nin_dom(T::V(a), g),
        B::Is(x, a) => well_formed_ctx(g) && nin_dom(T::V(x), g) && a.well_formed(g),
        B::Ex(a) => well_formed_ctx(g) && nin_dom(T::X(*a), g),
        B::Eq(a, t) => well_formed_ctx(g) && nin_dom(T::X(*a), g) && t.well_formed(g),
        B::M(a) => well_formed_ctx(g) && !g.contains(&B::M(*a)) && nin_dom(T::X(*a), g),
    }
}

macro_rules! ty {
    (1) => { T::U };
    (($($t:tt)*)) => { ty!($($t)*) };
    ($a:tt -> $($b:tt)*) => { T::a(ty!($a), ty!($($b)*)) };
    (#$a:tt -> $($b:tt)*) => { T::a(ty!(#$a), ty!($($b)*)) };
    (#$x:literal) => { T::X($x) };
    (@ $x:ident . $($t:tt)*) => { T::P(stringify!($x), Box::new(ty!($($t)*))) };
}

macro_rules! expr {
    () => { E::U };
    (($($body:tt)*)) => { expr!($($body)*) };
    (@ $x:ident . $e:tt) => { E::L(stringify!($x), Box::new(expr!($e))) };
    ($x:ident : $t:tt) => { E::T(stringify!($x), ty!($t)) };
    ($x:ident) => { E::V(stringify!($x)) };
}

macro_rules! ctx_bind {
    ([$($acc:expr ,)*]) => { vec![$($acc),*] };
    ([$($acc:expr ,)*] , #$x:literal = $y:tt $($rest:tt)*) => { ctx_bind!([$($acc ,)* B::Eq($x, ty!($y)) ,] $($rest)*) };
    ([$($acc:expr ,)*] , #$x:literal         $($rest:tt)*) => { ctx_bind!([$($acc ,)* B::Ex($x) ,] $($rest)*) };
    ([$($acc:expr ,)*] , ^$x:literal         $($rest:tt)*) => { ctx_bind!([$($acc ,)* B::M($x) ,] $($rest)*) };
    ([$($acc:expr ,)*] , $x:ident : $y:tt    $($rest:tt)*) => { ctx_bind!([$($acc ,)* B::Is(stringify!($x), ty!($y)) ,] $($rest)*) };
    ([$($acc:expr ,)*] , $x:ident            $($rest:tt)*) => { ctx_bind!([$($acc ,)* B::V(stringify!($x)) ,] $($rest)*) };
}
macro_rules! ctx {
    () => { vec![] };
    ($($b:tt)*) => { ctx_bind!([] , $($b)*) };
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_esynth() {
        let g = ctx![];
        assert_eq!(expr!().synth(&g), Some((ty!(1), ctx![])));
        assert_eq!(
            expr!(@x.()).synth(&g),
            Some((ty!(#0 -> #1), ctx![#0, #1 = 1]))
        );
        assert_eq!(expr!(x).synth(&ctx![x: 1]), Some((ty!(1), ctx![x: 1])));
    }
}

fn main() {}
