#![allow(unused)]

use std::collections::HashSet as Set;
/// messing around with https://arxiv.org/abs/1306.6032 "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"
use std::fmt::Debug;

type Ident = usize;

fn gen_ident() -> usize {
    use std::sync::atomic::*;
    static IDENTS: AtomicUsize = AtomicUsize::new(0);
    IDENTS.fetch_add(1, Ordering::SeqCst)
}

#[derive(Debug, Clone, PartialEq)]
enum T {
    Unit,
    A(Ident),
    Ah(Ident),
    TFn(Ident, Box<T>),
    Fn(Box<T>, Box<T>),
}

#[derive(Debug, Clone, PartialEq)]
enum B {
    A(Ident),
    X(Ident, T),
    Ah(Ident, Option<T>),
    Mark(Ident),
}

#[derive(Clone)]
struct Ctx<'ctx>(&'ctx [B], Vec<B>);
impl std::fmt::Debug for Ctx<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Ctx")?;
        f.debug_list().entries(self.iter()).finish()
    }
}
impl PartialEq for Ctx<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl Ctx<'_> {
    fn borrow<'b>(cs: &'b [B]) -> Ctx<'b> {
        Ctx(cs, vec![])
    }
}
impl<'ctx> Ctx<'ctx> {
    fn push(mut self, b: B) -> Self {
        self.1.push(b);
        self
    }
    fn extend<I>(mut self, it: I) -> Self
    where
        I: IntoIterator<Item = B>,
        I::IntoIter: ExactSizeIterator,
    {
        let it = it.into_iter();
        assert!(usize::MAX - self.len() > it.len());
        self.1.extend(it);
        self
    }
    fn splice<I>(self, i: usize, it: I) -> Self
    where
        I: IntoIterator<Item = B>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut it = it.into_iter();
        let Ctx(b, mut v) = self;
        if b.len() > i {
            let v = it
                .chain(b[i + 1..].into_iter().cloned())
                .chain(v.into_iter())
                .collect();
            Ctx(&b[..i], v)
        } else {
            let i = i - b.len();
            match it.len() {
                0 => drop(v.remove(i)),
                1 => v[i] = it.next().unwrap(),
                _ => drop(v.splice(i..i + 1, it)),
            }
            Ctx(b, v)
        }
    }
    fn truncate(&mut self, i: usize) {
        if i >= self.0.len() {
            self.1.truncate(i - self.0.len());
        } else {
            self.1.truncate(0);
            self.0 = &self.0[..i];
        }
    }
    fn truncate_after(&mut self, p: impl FnMut(&B) -> bool) -> Option<()> {
        let i = self.iter().rposition(p)?;
        self.truncate(i);
        Some(())
    }

    fn get(&self, x: usize) -> Option<&B> {
        if x < self.0.len() {
            self.0.get(x)
        } else {
            self.1.get(x - self.0.len())
        }
    }
    fn apply(&self, mut aa: T) -> Option<T> {
        fn inner(ctx: &Ctx, aa: &mut T) -> Option<()> {
            match aa {
                T::Unit | T::A(_) => Some(()),
                &mut T::Ah(ah) => ctx.iter().rev().find_map(|b| match b {
                    B::Ah(bh, t) if *bh == ah => {
                        if let Some(t) = t {
                            *aa = t.clone();
                        }
                        Some(())
                    }
                    _ => None,
                }),
                T::TFn(a, aa) => inner(ctx, aa),
                T::Fn(aa, bb) => {
                    inner(ctx, aa)?;
                    inner(ctx, bb)
                }
            }
        }
        inner(self, &mut aa)?;
        Some(aa)
    }

    fn len(&self) -> usize {
        self.0.len() + self.1.len()
    }
    fn iter<'it>(&'it self) -> CtxIter<'it> {
        CtxIter(self.0.iter(), self.1.iter())
    }
}

struct CtxIter<'ctx>(std::slice::Iter<'ctx, B>, std::slice::Iter<'ctx, B>);
impl<'ctx> Iterator for CtxIter<'ctx> {
    type Item = &'ctx B;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().or_else(|| self.1.next())
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        // SAFETY: we assert in Ctx that combined len is < usize::MAX
        let len = self.0.len() + self.1.len();
        (len, Some(len))
    }
}
impl<'ctx> DoubleEndedIterator for CtxIter<'ctx> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.1.next_back().or_else(|| self.0.next_back())
    }
}
impl ExactSizeIterator for CtxIter<'_> {}

fn ctx_wf(ctx: &Ctx) -> Option<()> {
    let mut nindom = Set::new();
    let mut marknin = Set::new();
    for c in ctx.iter() {
        match c {
            B::A(a) => {
                (!nindom.contains(a)).then(|| ())?;
                nindom.insert(*a);
            }
            B::X(x, aa) => {
                (!nindom.contains(x)).then(|| ())?;
                ty_wf(ctx, aa)?;
                nindom.insert(*x);
            }
            B::Ah(ah, t) => {
                (!nindom.contains(ah)).then(|| ())?;
                if let Some(t) = t {
                    ty_wf(ctx, t)?;
                }
                nindom.insert(*ah);
            }
            B::Mark(ah) => {
                (!marknin.contains(ah)).then(|| ())?;
                nindom.insert(*ah);
                marknin.insert(*ah);
            }
        }
    }
    Some(())
}

fn ty_wf(ctx: &Ctx, aa: &T) -> Option<()> {
    fn inner<'ctx>(ctx: Ctx<'ctx>, aa: &T) -> Option<Ctx<'ctx>> {
        match aa {
            T::Unit => Some(ctx),
            T::A(a) => ctx.iter().rposition(|c| c == &B::A(*a)).and(Some(ctx)),
            T::Ah(ah) => ctx
                .iter()
                .rposition(|c| match c {
                    B::Ah(bh, _) => bh == ah,
                    _ => false,
                })
                .and(Some(ctx)),
            T::TFn(a, aa) => {
                let len = ctx.len();
                let ictx = ctx.push(B::A(*a));
                let mut octx = inner(ictx, aa)?;
                octx.truncate(len);
                Some(octx)
            }
            T::Fn(aa, bb) => {
                let ctx = inner(ctx, aa)?;
                inner(ctx, bb)
            }
        }
    }
    inner(ctx.clone(), aa)?;
    Some(())
}

fn ty_sub<'ctx>(ctx: Ctx<'ctx>, aa: T, bb: T) -> Option<Ctx<'ctx>> {
    match (aa, bb) {
        (T::Unit, T::Unit) => Some(ctx),
        (T::A(a), T::A(b)) => {
            (a == b).then(|| ())?;
            ctx.iter().rposition(|b| b == &B::A(a))?;
            Some(ctx)
        }
        (T::Ah(ah), T::Ah(bh)) if ah == bh => {
            ctx.iter().rposition(|b| b == &B::Ah(ah, None))?;
            Some(ctx)
        }
        (T::Fn(aa1, aa2), T::Fn(bb1, bb2)) => {
            let octx = ty_sub(ctx, *bb1, *aa1)?;
            let aa2 = octx.apply(*aa2)?;
            let bb2 = octx.apply(*bb2)?;
            ty_sub(octx, aa2, bb2)
        }

        // don't need to worry about instantiate rules
        // because TFn can't appear in Instantiations
        (T::TFn(a, aa), bb) => {
            let ah = gen_ident();
            let ictx = ctx.extend([B::Mark(ah), B::Ah(ah, None)]);
            let aa = ty_subst(*aa, T::Ah(ah), a);
            let mut octx = ty_sub(ictx, aa, bb)?;
            octx.truncate_after(|b| b == &B::Mark(ah))?;
            Some(octx)
        }
        (aa, T::TFn(a, bb)) => {
            let ictx = ctx.push(B::A(a));
            let mut octx = ty_sub(ictx, aa, *bb)?;
            octx.truncate_after(|b| b == &B::A(a))?;
            Some(octx)
        }

        // instantiation cases
        (T::Ah(ah), T::Ah(bh)) => {
            // have ah \nin fv(bh) and vice-versa, by ah != bh
            {
                let i = ctx.iter().rposition(|b| b == &B::Ah(ah, None))?;
                ty_instantiate(ctx.clone(), i, ah, T::Ah(bh), Inst::L)
            }
            .or_else(|| {
                let i = ctx.iter().rposition(|b| b == &B::Ah(bh, None))?;
                ty_instantiate(ctx, i, bh, T::Ah(ah), Inst::R)
            })
        }
        (T::Ah(ah), aa) => {
            ty_nin_fv(ah, &aa)?;
            let i = ctx.iter().rposition(|b| b == &B::Ah(ah, None))?;
            ty_instantiate(ctx, i, ah, aa, Inst::L)
        }
        (aa, T::Ah(ah)) => {
            ty_nin_fv(ah, &aa)?;
            let i = ctx.iter().rposition(|b| b == &B::Ah(ah, None))?;
            ty_instantiate(ctx, i, ah, aa, Inst::R)
        }
        _ => None,
    }
}

/// [ah/aa]bb
fn ty_subst(mut bb: T, aa: T, a: Ident) -> T {
    fn inner(bb: &mut T, aa: T, a: Ident) {
        match bb {
            T::A(b) if *b == a => *bb = aa,
            T::TFn(_, bb) => inner(bb, aa, a),
            T::Fn(bb, cc) => {
                inner(bb, aa.clone(), a);
                inner(cc, aa, a);
            }
            _ => {}
        }
    }
    inner(&mut bb, aa, a);
    bb
}
/// ah \nin FV(aa)
fn ty_nin_fv(ah: Ident, aa: &T) -> Option<()> {
    match aa {
        T::Ah(bh) => (*bh != ah).then(|| ()),
        T::TFn(_, aa) => ty_nin_fv(ah, aa),
        T::Fn(aa, bb) => ty_nin_fv(ah, aa).and(ty_nin_fv(ah, bb)),
        _ => Some(()),
    }
}

#[derive(Clone, Copy)]
enum Inst {
    R,
    L,
}
impl std::ops::Not for Inst {
    type Output = Self;
    fn not(self) -> Self {
        match self {
            Inst::R => Inst::L,
            Inst::L => Inst::R,
        }
    }
}
/// ctx[ah] |- ah :<= aa -| octx
/// ctx[ah] |- aa :<= ah -| octx
///     i^     ^^^sub^^^
fn ty_instantiate<'ctx>(
    ctx: Ctx<'ctx>,
    i: usize,
    ah: Ident,
    aa: T,
    sub: Inst,
) -> Option<Ctx<'ctx>> {
    match (aa, sub) {
        (aa @ (T::Unit | T::A(_)), _) => {
            ty_wf(&ctx, &aa)?;
            Some(ctx.splice(i, [B::Ah(ah, Some(aa))]))
        }
        (T::Ah(bh), _) => {
            let j = ctx.iter().rposition(|b| b == &B::Ah(bh, None))?;
            (j > i).then(|| ())?;
            Some(ctx.splice(j, [B::Ah(bh, Some(T::Ah(ah)))]))
        }
        (T::Fn(aa1, aa2), _) => {
            let (ah2, ah1) = (gen_ident(), gen_ident());
            let t = T::Fn(Box::new(T::Ah(ah1)), Box::new(T::Ah(ah2)));
            // XXX: this is the transformation that makes deBruijn indexing hard
            // it's also the one that requires us to search the output context
            // because any number of these changes could happen, which would keep
            // increasing the distance from ah to top of stack
            let ictx = ctx.splice(i, [B::Ah(ah2, None), B::Ah(ah1, None), B::Ah(ah, Some(t))]);
            let octx = ty_instantiate(ictx, i + 1, ah1, *aa1, !sub)?;
            let aa2 = octx.apply(*aa2)?;
            let j = octx.iter().rposition(|b| b == &B::Ah(ah2, None))?;
            ty_instantiate(octx, j, ah2, aa2, sub)
        }
        (T::TFn(a, bb), Inst::L) => {
            let ictx = ctx.push(B::A(a));
            let mut octx = ty_instantiate(ictx, i, ah, *bb, Inst::L)?;
            octx.truncate_after(|b| b == &B::A(a))?;
            Some(octx)
        }
        (T::TFn(a, bb), Inst::R) => {
            let bh = gen_ident();
            let ictx = ctx.extend([B::Mark(bh), B::Ah(bh, None)]);
            let bb = ty_subst(*bb, T::Ah(bh), a);
            let mut octx = ty_instantiate(ictx, i, ah, bb, Inst::R)?;
            octx.truncate_after(|b| b == &B::Mark(bh))?;
            Some(octx)
        }
    }
}

#[derive(Debug)]
enum E {
    Unit,
    X(Ident),
    T(Box<E>, T),
    Fn(Ident, Box<E>),
    App(Box<E>, Box<E>),
}

impl std::fmt::Display for E {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            E::Unit => f.write_str("()"),
            E::X(x) => write!(f, "#{x}"),
            E::T(e, t) => write!(f, "({e} : {t:?})"),
            E::Fn(x, e) => write!(f, "λ#{x}.{e}"),
            E::App(e1, e2) => write!(f, "({e1} {e2})"),
        }
    }
}
impl std::fmt::Display for T {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            T::Unit => f.write_str("𝟙"),
            T::A(a) => write!(f, "#{a}"),
            T::Ah(ah) => write!(f, "_{ah}"),
            T::TFn(a, t) => write!(f, "Ɐ#{a}.{t}"),
            T::Fn(t1, t2) => write!(f, "({t1} -> {t2})"),
        }
    }
}
impl std::fmt::Display for Ctx<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut it = self.iter();
        if it.len() == 0 {
            return f.write_str("·");
        }
        fn fmt_b(b: &B, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match b {
                B::A(a) => write!(f, "#{a}"),
                B::X(x, t) => write!(f, "#{x}: {t}"),
                B::Ah(ah, Some(t)) => write!(f, "_{ah} = {t}"),
                B::Ah(ah, None) => write!(f, "_{ah}"),
                B::Mark(ah) => write!(f, ">{ah}"),
            }
        }
        fmt_b(it.next().unwrap(), f)?;
        for b in it {
            f.write_str(",")?;
            fmt_b(b, f)?;
        }
        Ok(())
    }
}

fn ty_ck<'ctx>(ctx: Ctx<'ctx>, e: &E, aa: &T) -> Option<Ctx<'ctx>> {
    fn fallback<'ctx>(ctx: Ctx<'ctx>, e: &E, bb: &T) -> Option<Ctx<'ctx>> {
        let (aa, octx) = ty_syn(ctx, e)?;
        let aa = octx.apply(aa)?;
        let bb = octx.apply(bb.clone())?;
        ty_sub(octx, aa, bb)
    }
    match (e, aa) {
        (E::Unit, T::Unit) => Some(ctx),
        (e, T::TFn(a, aa)) => {
            let ictx = ctx.clone().push(B::A(*a));
            (|| {
                let mut octx = ty_ck(ictx, e, aa)?;
                octx.truncate_after(|b| b == &B::A(*a))?;
                Some(octx)
            })()
            .or_else(|| fallback(ctx, e, aa))
        }
        (E::Fn(x, e), T::Fn(aa, bb)) => {
            let ictx = ctx.clone().push(B::X(*x, (**aa).clone()));
            (|| {
                let mut octx = ty_ck(ictx, e, bb)?;
                octx.truncate_after(|b| match b {
                    B::X(y, cc) => (y, cc) == (x, aa),
                    _ => false,
                })?;
                Some(octx)
            })()
            .or_else(|| fallback(ctx, e, aa))
        }
        (e, bb) => fallback(ctx, e, aa),
    }
}
fn ty_syn<'ctx>(ctx: Ctx<'ctx>, e: &E) -> Option<(T, Ctx<'ctx>)> {
    match e {
        E::Unit => Some((T::Unit, ctx)),
        E::X(x) => {
            let aa = ctx.iter().rev().find_map(|b| match b {
                B::X(y, aa) if y == x => Some(aa.clone()),
                _ => None,
            })?;
            Some((aa, ctx))
        }
        E::T(e, aa) => {
            ty_wf(&ctx, aa)?;
            let octx = ty_ck(ctx, e, aa)?;
            Some(((*aa).clone(), octx))
        }
        E::Fn(x, e) => {
            let (ah, bh) = (gen_ident(), gen_ident());
            let ictx = ctx.extend([B::Ah(ah, None), B::Ah(bh, None), B::X(*x, T::Ah(ah))]);
            let mut octx = ty_ck(ictx, e, &T::Ah(bh))?;
            octx.truncate_after(|b| b == &B::X(*x, T::Ah(ah)))?;
            let t = T::Fn(Box::new(T::Ah(ah)), Box::new(T::Ah(bh)));
            Some((t, octx))
        }
        E::App(e1, e2) => {
            let (aa, octx) = ty_syn(ctx, e1)?;
            let aa = octx.apply(aa)?;
            ty_fnsyn(octx, aa, e2)
        }
    }
}
fn ty_fnsyn<'ctx>(ctx: Ctx<'ctx>, aa: T, e: &E) -> Option<(T, Ctx<'ctx>)> {
    match aa {
        T::TFn(a, aa) => {
            let ah = gen_ident();
            let ictx = ctx.push(B::Ah(ah, None));
            let aa = ty_subst(*aa, T::Ah(ah), a);
            ty_fnsyn(ictx, aa, e)
        }
        T::Ah(ah) => {
            let i = ctx.iter().rposition(|b| b == &B::Ah(ah, None))?;
            let (ah1, ah2) = (gen_ident(), gen_ident());
            let t = T::Fn(Box::new(T::Ah(ah1)), Box::new(T::Ah(ah2)));
            let ictx = ctx.splice(i, [B::Ah(ah2, None), B::Ah(ah1, None), B::Ah(ah, Some(t))]);
            let octx = ty_ck(ictx, e, &T::Ah(ah1))?;
            Some((T::Ah(ah2), octx))
        }
        T::Fn(aa, cc) => {
            let octx = ty_ck(ctx, e, &aa)?;
            Some((*cc, octx))
        }
        _ => None,
    }
}

macro_rules! impl_ident {
    ($name:ident for $tgt:ident :: $var:ident) => {
        #[derive(Clone, Copy)]
        struct $name(Ident);
        impl From<$name> for $tgt {
            fn from(v: $name) -> $tgt {
                $tgt::$var(v.0)
            }
        }
    };
}
impl_ident! {ExprIdent for E::X}
impl_ident! {TyIdent for T::A}
impl_ident! {ExIdent for T::Ah}

macro_rules! ty {
    (()) => { T::Unit };
    (fn($($t1:tt)*) -> $($t2:tt)*) => { T::Fn(Box::new(ty!($($t1)*)), Box::new(ty!($($t2)*))) };
    (fn[$a:ident] -> $($t:tt)*) => {{
        let a = gen_ident();
        let $a = TyIdent(a);
        T::TFn(a, Box::new(ty!($($t)*)))
    }};
    (($($t:tt)+)) => { ty!($($t)*) };
    ($e:expr) => { ($e).into() };
}
macro_rules! expr {
    (()) => { E::Unit };
    ($x:tt : $t:tt) => { E::T(Box::new(expr!($x)), ty!($t)) };
    (($x:ident : $($t:tt)*)) => { E::T(Box::new($x.into()), ty!($($t)*)) };
    (($($e:tt)*)) => { expr!($($e)*) };
    (fn($x:ident) { $($e:tt)* }) => {{
        let x = gen_ident();
        let $x = ExprIdent(x);
        E::Fn(x, Box::new(expr!($($e)*)))
    }};
    ($e1:tt $e2:tt) => { E::App(Box::new(expr!($e1)), Box::new(expr!($e2))) };
    ($e:expr) => { E::from($e) }
}
macro_rules! ctx {
    // internal muncher
    ([]) => { [] };
    ([, $($bs:tt)*]) => { [$($bs)*] };
    ([$($bs:tt)*] $x:ident : $t: tt $(, $($ctx:tt)*)?) => {
        ctx!([$($bs)* , B::X({ let ExprIdent(x) = $x; x }, ty!($t))] $(, $($ctx)*)?)
    };
    ([$($bs:tt)*] $ah:tt = $t:tt $(, $($ctx:tt)*)?) => {
        ctx!([$($bs)* , B::Eq($ah, ty!($t))] $(, $($ctx)*)?)
    };
    ([$($bs:tt)*] > $ah:tt $(, $($ctx:tt)*)?) => {
        ctx!([$($bs)* , B::Mark($ah)] $(, $($ctx)*)?)
    };
    ([$($bs:tt)*] $id:tt $(, $($ctx:tt)*)?) => {
        ctx!([$($bs)* , B::from($id)] $(, $($ctx)*)?)
    };

    // entry-point
    ($($b:tt)*) => { Ctx::borrow(&ctx!([] $($b)*)) }
}

type Span = std::ops::Range<usize>;
#[derive(Debug)]
struct ParseErr(&'static str, Span);
fn parse(text: &str) -> Result<E, ParseErr> {
    #[derive(Debug, PartialEq)]
    enum D {
        Paren,
        Brace,
        Brack,
    }
    #[derive(Debug)]
    enum Tok<S> {
        G(D, Vec<Tok<S>>, Span, Span),
        W(S, Span),
    }
    fn tokenize(text: &str) -> Result<Vec<Tok<&str>>, ParseErr> {
        let mut stack = vec![];
        let mut toks = vec![];
        let mut start = 0;
        let mut push_word = |i, toks: &mut Vec<_>| {
            let w = &text[start..i];
            if w != "" {
                toks.push(Tok::W(w, start..i));
            }
            start = i + 1;
        };
        let mut delim_start = 0..0;
        fn delim_for(c: char) -> D {
            match c {
                '(' | ')' => D::Paren,
                '[' | ']' => D::Brack,
                '{' | '}' => D::Brace,
                _ => panic!(),
            }
        }
        for (i, c) in text.char_indices() {
            match c {
                '(' | '[' | '{' => {
                    push_word(i, &mut toks);
                    stack.push((delim_for(c), i..i + 1, toks));
                    toks = vec![];
                }
                ')' | '}' | '}' => {
                    push_word(i, &mut toks);
                    match stack.pop() {
                        Some((delim, start_span, mut pre_toks)) if delim == delim_for(c) => {
                            pre_toks.push(Tok::G(delim, toks, start_span, i..i + 1));
                            toks = pre_toks;
                        }
                        Some((delim, _, _)) => {
                            return Err(ParseErr("unexpected delimiter", i..i + 1))
                        }
                        None => return Err(ParseErr("unexpected closing delimiter", i..i + 1)),
                    }
                }
                _ => {
                    if c.is_whitespace() {
                        push_word(i, &mut toks);
                    }
                }
            }
        }
        push_word(text.len(), &mut toks);
        if !stack.is_empty() {
            return Err(ParseErr("unexpected EOF while parsing groups", 0..0));
        }
        Ok(toks)
    }
    let mut toks = tokenize(text)?;
    use std::collections::HashMap as Map;
    fn parse_bind_list(
        ctx: &Map<String, Ident>,
        toks: Vec<Tok<&str>>,
    ) -> Result<(Map<String, Ident>, Vec<Ident>), ParseErr> {
        let mut fnargs = vec![];
        let mut scope = ctx.clone();
        for tok in toks {
            match tok {
                Tok::W(a, span) => {
                    let id = gen_ident();
                    fnargs.push(id);
                    scope.insert(a.to_string(), id);
                }
                _ => return Err(ParseErr("unexpected token in argument position", 0..0)),
            }
        }
        Ok((scope, fnargs))
    }
    fn parse_expr(ctx: &Map<String, Ident>, toks: Vec<Tok<&str>>) -> Result<E, ParseErr> {
        let mut appstack = vec![];
        let mut type_ascript = None;
        let mut toks = toks.into_iter();
        while let Some(tok) = toks.next() {
            match tok {
                Tok::G(D::Paren, in_toks, _, _) => {
                    let e = if in_toks.is_empty() {
                        E::Unit
                    } else {
                        parse_expr(ctx, in_toks)?
                    };
                    appstack.push(e);
                }
                Tok::W("fn", span) => {
                    let args = match toks.next() {
                        Some(Tok::G(D::Paren, args, _, _)) => args,
                        Some(Tok::G(_, _, span, _)) | Some(Tok::W(_, span)) => {
                            return Err(ParseErr("expected `fn(`_`)`", span))
                        }
                        None => return Err(ParseErr("unexpected EOF scanning `fn`", 0..0)),
                    };
                    let (scope, fnargs) = parse_bind_list(ctx, args)?;
                    if fnargs.is_empty() {
                        return Err(ParseErr("fn arguments cannot be empty", span));
                    }
                    let body = match toks.next() {
                        Some(Tok::G(D::Brace, body, _, _)) => body,
                        Some(Tok::G(_, _, span, _) | Tok::W(_, span)) => {
                            return Err(ParseErr("expected `fn(`_`) {` _ `}`", span))
                        }
                        None => {
                            return Err(ParseErr(
                                "unexpected EOF while scanning `fn(`_`){{``}}`",
                                0..0,
                            ))
                        }
                    };
                    let mut body = parse_expr(&scope, body)?;
                    let mut fnargs = fnargs.into_iter().rev();
                    body = E::Fn(fnargs.next().unwrap(), Box::new(body));
                    for id in fnargs {
                        body = E::Fn(id, Box::new(body));
                    }
                    appstack.push(body);
                }
                Tok::W(":", span) => {
                    if appstack.is_empty() {
                        return Err(ParseErr("unexpected `:`", span));
                    }
                    let ty = parse_ty(&Map::new(), toks)?;
                    type_ascript = Some(ty);
                    break;
                }
                Tok::W(x, span) => {
                    if ctx.contains_key(x) {
                        appstack.push(E::X(*ctx.get(x).unwrap()))
                    } else {
                        return Err(ParseErr("undefined variable", span));
                    }
                }
                Tok::G(_, _, span, _) => return Err(ParseErr("unexpected token", span)),
            }
        }

        if appstack.is_empty() {
            return Err(ParseErr("unexpected EOF parsing expr", 0..0));
        }
        let mut es = appstack.into_iter().rev();
        let mut tl = es.next().unwrap();
        for e in es {
            tl = E::App(Box::new(e), Box::new(tl));
        }
        if let Some(ty) = type_ascript {
            tl = E::T(Box::new(tl), ty);
        }
        Ok(tl)
    }
    fn parse_ty(
        ctx: &Map<String, Ident>,
        mut toks: std::vec::IntoIter<Tok<&str>>,
    ) -> Result<T, ParseErr> {
        let Some(tok) = toks.next() else {
            return Err(ParseErr("unexpected EOF parsing type", 0..0));
        };
        match tok {
            // unit tup
            Tok::G(D::Paren, in_toks, _, _) if in_toks.is_empty() => {
                if toks.next().is_some() {
                    Err(ParseErr("expected EOF", 0..0))
                } else {
                    Ok(T::Unit)
                }
            }
            Tok::W("fn", span) => {
                let (delim, args) = match toks.next() {
                    Some(Tok::G(delim @ (D::Paren | D::Brack), args, _, _)) => (delim, args),
                    Some(Tok::G(_, _, span, _) | Tok::W(_, span)) => {
                        return Err(ParseErr(
                            "unexpected: `fn` _, expected `fn` `(` _ `)`",
                            span,
                        ))
                    }

                    None => return Err(ParseErr("unexpected EOF while parsing `fn`", 0..0)),
                };
                match delim {
                    D::Paren => {
                        let in_ty = parse_ty(ctx, args.into_iter())?;
                        let out_ty = parse_ty(ctx, toks)?;
                        Ok(T::Fn(Box::new(in_ty), Box::new(out_ty)))
                    }
                    D::Brack => {
                        let (scope, fnargs) = parse_bind_list(ctx, args)?;
                        if fnargs.is_empty() {
                            return Err(ParseErr("expected bindings in `fn[_]` ", span));
                        }
                        let mut ty = parse_ty(&scope, toks)?;
                        let mut args = fnargs.into_iter().rev();
                        for id in args {
                            ty = T::TFn(id, Box::new(ty));
                        }
                        Ok(ty)
                    }
                    _ => unreachable!(),
                }
            }
            Tok::W(a, span) => {
                if ctx.contains_key(a) {
                    Ok(T::A(*ctx.get(a).unwrap()))
                } else {
                    Err(ParseErr("unexpected token", span))
                }
            }
            Tok::G(_, _, span, _) => Err(ParseErr("unexpected tokens", span)),
        }
    }
    parse_expr(&Map::new(), toks)
}

fn print_err(text: &str, msg: &str, span: Span) {
    println!("error: {msg}");
    if span != (0..0) {
        let mut line_span = span.start..span.end;
        while line_span.start > 0 && &text[line_span.start..line_span.start + 1] != "\n" {
            line_span.start -= 1;
        }
        while line_span.end < text.len() && &text[line_span.end..line_span.end + 1] != "\n" {
            line_span.end += 1;
        }
        let mut i = line_span.start;
        for line in text[line_span].split_inclusive('\n') {
            print!("  | {line}");
            if !line.ends_with('\n') {
                println!();
            }
            print!("  | ");
            for _ in 0..line.len() {
                if span.contains(&i) {
                    print!("^");
                } else {
                    print!(" ");
                }
                i += 1;
            }
            println!();
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_esynth() {
        let g = ctx![];
        assert_eq!(ty_syn(ctx![], &expr!(())), Some((ty!(()), ctx![])));
        let actual = ty_syn(ctx![], &expr!(fn(x) {x}));
        assert!(
            match &actual {
                Some((T::Fn(a, b), ctx)) => match (&**a, &**b) {
                    (&T::Ah(ah), &T::Ah(bh)) => {
                        ctx == &Ctx::borrow(&[B::Ah(ah, None), B::Ah(bh, Some(T::Ah(ah)))])
                    }
                    _ => false,
                },
                _ => false,
            },
            "assert_eq: ty_syn(ctx![], &expr!(fn(x), {{x}})) != expected\nactual:   {actual:?}\nexpected: Some((Fn(Ah(_a), Ah(_b)), Ctx[Ah(_a), Eq(_b, Ah(_a))]))"
        );
        let x = ExprIdent(gen_ident());
        assert_eq!(ty_syn(ctx![x: ()], &expr!(x)), Some((ty![()], ctx![x: ()])));
    }
}

fn main() {
    let input = std::io::read_to_string(std::io::stdin()).unwrap();
    let expr = match parse(&input) {
        Ok(expr) => expr,
        Err(ParseErr(msg, span)) => {
            print_err(&input, msg, span);
            return;
        }
    };
    match ty_syn(ctx![], &expr) {
        Some((ty, ctx)) => println!("|-  {expr}  =>  {ty}  -| {ctx}"),

        None => println!("|- {expr} : ??"),
    }
}
