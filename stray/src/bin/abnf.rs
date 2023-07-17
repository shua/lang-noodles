#![allow(unused)]

use std::fmt::Debug;

#[derive(Debug, Clone)]
enum Expr {
    Seq(Vec<Expr>),  // ws-separated exprs
    Cont(Vec<Expr>), // contiguous exprs
    Alt(Vec<Expr>),
    Many(Box<Expr>),
    Opt(Box<Expr>),

    Term(usize),
    Atom(String),
    Str(String),
    Set(bool, String),
}

impl Expr {}

#[derive(Debug)]
struct Term {
    display: String,
    expr: Expr,
}

struct Terms(Vec<Term>);

impl std::ops::Index<usize> for Terms {
    type Output = Term;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl Terms {
    fn fmt_join(&self, f: &mut std::fmt::Formatter, e: &[Expr], sep: &str) -> std::fmt::Result {
        let mut seps = std::iter::once("").chain(std::iter::repeat(sep));
        for e in e {
            f.write_str(seps.next().unwrap())?;
            if matches!(e, Expr::Alt(_)) {
                f.write_str("(")?;
                self.fmt_expr(f, e)?;
                f.write_str(")")?;
            } else {
                self.fmt_expr(f, e)?;
            }
        }
        Ok(())
    }

    fn fmt_suffix(&self, f: &mut std::fmt::Formatter, e: &Expr, suff: &str) -> std::fmt::Result {
        if matches!(e, Expr::Seq(_) | Expr::Cont(_) | Expr::Alt(_)) {
            f.write_str("(")?;
            self.fmt_expr(f, e)?;
            f.write_str(")")?;
        } else {
            self.fmt_expr(f, e)?;
        }
        f.write_str(suff)
    }

    fn fmt_expr(&self, f: &mut std::fmt::Formatter, e: &Expr) -> std::fmt::Result {
        fn charruns(s: &str, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            if s.len() == 0 {
                return Ok(());
            }
            let mut iter = s.bytes().enumerate();
            let mut j = 0;
            let mut rangestart = 0;
            let (_, mut last) = iter.next().unwrap();
            while let Some((i, c)) = iter.next() {
                if c == last + 1 {
                    if rangestart == 0 {
                        write!(f, "{}", &s[j..i - 1])?;
                        rangestart = last;
                    }
                } else if rangestart != 0 {
                    write!(f, "{}-{}", rangestart as char, last as char)?;
                    rangestart = 0;
                    j = i;
                }
                last = c;
            }
            if rangestart == 0 {
                write!(f, "{}", &s[j..])
            } else {
                write!(f, "{}-{}", rangestart as char, last as char)
            }
        }

        match e {
            Expr::Seq(es) => self.fmt_join(f, es, " "),
            Expr::Cont(es) => self.fmt_join(f, es, ""),
            Expr::Alt(es) => self.fmt_join(f, es, " / "),
            Expr::Many(e) => self.fmt_suffix(f, e, "*"),
            Expr::Opt(e) => self.fmt_suffix(f, e, "?"),
            Expr::Term(t) => f.write_str(&self[*t].display),
            Expr::Atom(a) => write!(f, "${a}"),
            Expr::Str(s) if s.len() == 1 => {
                let b = s.bytes().next().unwrap();
                if b >= 0x20 && b < 0x7f && b != 0x27 {
                    write!(f, "'{s}'")
                } else {
                    write!(f, "(0x{b:02x?})")
                }
            }
            Expr::Str(s) => write!(f, "\"{s}\""),
            Expr::Set(false, s) if s == "" => f.write_str("."),
            Expr::Set(pos, s) => {
                write!(f, "[{}", if *pos { "" } else { "^" })?;
                charruns(s, f)?;
                f.write_str("]")
            }
        }
    }
}

impl Debug for Terms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Terms[")?;
        let mut first = true;
        if self.0.len() > 1 {
            for t in &self.0 {
                if f.alternate() {
                    f.write_str("\n    ")?;
                } else if !first {
                    f.write_str("  ;  ");
                }
                first = false;
                write!(f, "{} ::= ", t.display)?;
                self.fmt_expr(f, &t.expr)?;
            }
        }
        if f.alternate() {
            f.write_str("\n]")
        } else {
            f.write_str("]")
        }
    }
}

fn parse_terms<'s>(txt: &'s str) -> Terms {
    #[derive(Debug)]
    enum S {
        Line,
        Term,
        Def,
        Expr,
        Atom,
        Set,
    };
    let mut s = S::Line;
    let mut iter = txt.char_indices();
    let mut j = 0;
    let mut tdisp = "";
    let mut texpr = vec![vec![]];
    let mut parstack = vec![];
    let mut tsetpos = None;
    let mut tset = String::new();
    let push_seq = |texpr: &mut Vec<Vec<_>>, expr: Expr| {
        texpr.last_mut().unwrap().push(expr);
    };
    let push_if_atom = |texpr: &mut _, s: &mut _, txt: &'s str| {
        if matches!(s, S::Atom) {
            push_seq(texpr, Expr::Atom(txt.to_string()));
            *s = S::Expr;
        }
    };
    let to_expr = |texpr: Vec<Vec<Expr>>| {
        let mut altes = texpr.into_iter().map(|mut es| {
            // remove ws delimiters
            let match_delim = |e: Option<&_>| match e {
                Some(&Expr::Cont(ref es)) if es.len() == 0 => true,
                _ => false,
            };
            while match_delim(es.first()) {
                es.remove(0);
            }
            while match_delim(es.last()) {
                es.pop();
            }
            let mut seq = vec![];
            let mut cont = vec![];
            for e in es {
                if match_delim(Some(&e)) {
                    if cont.len() == 1 {
                        seq.push(cont.pop().unwrap());
                    } else {
                        seq.push(Expr::Cont(cont));
                        cont = vec![];
                    }
                } else {
                    cont.push(e);
                }
            }
            match cont.len() {
                0 => {}
                1 => seq.push(cont.pop().unwrap()),
                _ => seq.push(Expr::Cont(cont)),
            }
            if seq.len() == 1 {
                seq.pop().unwrap()
            } else {
                Expr::Seq(seq)
            }
        });
        if altes.len() == 1 {
            altes.next().unwrap()
        } else {
            Expr::Alt(altes.collect())
        }
    };

    let mut ts = vec![];
    let mut tids = vec![];
    let mut push_term = |tdisp: &'s str, texpr: Vec<Vec<_>>, parstack: &[_]| {
        if parstack.len() != 0 {
            panic!("unclosed parenthesis");
        }
        let expr = to_expr(texpr);
        tids.push((tids.len(), tdisp));
        ts.push(Term {
            display: tdisp.to_string(),
            expr,
        });
    };
    while let Some((i, c)) = iter.next() {
        match (&s, c) {
            (S::Line, ' ' | '\t' | '\n') => {}
            (S::Line, _) => (s, j) = (S::Term, i),
            (S::Term, ' ' | '\t') => (s, tdisp) = (S::Def, &txt[j..i]),
            (S::Def, ' ' | '\t') => {}
            (S::Def, _) | (S::Term, ':') => match (c, iter.next(), iter.next()) {
                (':', Some((_, ':')), Some((_, '='))) => {
                    if matches!(s, S::Term) {
                        tdisp = &txt[j..i];
                    }
                    s = S::Expr;
                }
                (_, Some(_), Some(_)) => {
                    panic!("unexpected chars parsing '::=':{i}: {:?}", &txt[i..(i + 2)])
                }
                _ => panic!("unexpected eof parsing '::='"),
            },
            (S::Term, _) => {}
            (S::Expr | S::Atom, '(') => {
                push_if_atom(&mut texpr, &mut s, &txt[j..i]);
                parstack.push(texpr);
                texpr = vec![vec![]];
            }
            (S::Expr | S::Atom, ')') => {
                push_if_atom(&mut texpr, &mut s, &txt[j..i]);
                let e = to_expr(texpr);
                texpr = parstack.pop().expect("unexpected ')':{i}");
                push_seq(&mut texpr, e);
            }
            (S::Expr | S::Atom, ' ' | '\t') => {
                push_if_atom(&mut texpr, &mut s, &txt[j..i]);
                push_seq(&mut texpr, Expr::Cont(vec![]));
            }
            (S::Expr | S::Atom, '*' | '?') => {
                push_if_atom(&mut texpr, &mut s, &txt[j..i]);
                let mut e = texpr.last_mut().unwrap().pop();
                match (e, c) {
                    (None, _) => panic!("unexpected '*' without preceding expression:{i}"),
                    (Some(elast), '*') => {
                        push_seq(&mut texpr, Expr::Many(Box::new(elast)));
                    }
                    (Some(elast), _) => {
                        push_seq(&mut texpr, Expr::Opt(Box::new(elast)));
                    }
                }
            }
            (S::Expr | S::Atom, '\n') => {
                push_if_atom(&mut texpr, &mut s, &txt[j..i]);
                s = S::Line;
                push_term(tdisp, texpr, &parstack);
                texpr = vec![vec![]];
            }
            (S::Expr | S::Atom, '/') => {
                push_if_atom(&mut texpr, &mut s, &txt[j..i]);
                texpr.push(vec![]);
            }
            (S::Expr | S::Atom, '[') => {
                push_if_atom(&mut texpr, &mut s, &txt[j..i]);
                s = S::Set;
                j = i + 1;
            }
            (S::Expr | S::Atom, '\'') => match (iter.next(), iter.next()) {
                (Some((_, c)), Some((_, '\''))) => {
                    push_if_atom(&mut texpr, &mut s, &txt[j..i]);
                    push_seq(&mut texpr, Expr::Str(String::from(c)));
                }
                (Some(_), Some((_, c))) => {
                    panic!("unexpected char parsing char literal:{i}: {c:?}")
                }
                _ => panic!("unexpected eof parsing char literal"),
            },
            (S::Expr | S::Atom, '"') => {
                push_if_atom(&mut texpr, &mut s, &txt[j..i]);
                j = i + 1;
                let mut esc = false;
                let mut s = String::new();
                loop {
                    let (i, c) = iter.next().expect("unexpected eof parsing \"..\"");
                    match (esc, c) {
                        (false, '"') => {
                            s.push_str(&txt[j..i]);
                            break;
                        }
                        (false, '\\') => {
                            s.push_str(&txt[j..i]);
                            esc = true;
                        }
                        (false, _) => {}
                        (true, c) => {
                            s.push(match c {
                                'n' => '\n',
                                't' => '\t',
                                c => c,
                            });
                            esc = false;
                        }
                    }
                }
                push_seq(&mut texpr, Expr::Str(s));
            }
            (S::Expr, _) => (s, j) = (S::Atom, i),
            (S::Atom, _) => {}
            (S::Set, '^') if tsetpos.is_none() => (tsetpos, j) = (Some(false), i + 1),
            (S::Set, ']') => {
                s = S::Expr;
                tset.push_str(&txt[j..i]);
                push_seq(&mut texpr, Expr::Set(tsetpos.unwrap_or(true), tset));
                (tsetpos, tset) = (None, String::new());
            }
            (S::Set, '-') => {
                if j >= i {
                    panic!("unexpected '-' in charset, correct usage is '[c-c]':{i}");
                }
                tset.push_str(&txt[j..i - 1]);
                let cstart = txt[i - 1..i].chars().last().unwrap();
                let (_, cend) = iter.next().expect("unexpected eof while scanning charset");
                j = i + 2;
                tset.extend(cstart..=(cend));
            }
            (S::Set, _) if tsetpos.is_none() => tsetpos = Some(true),
            (S::Set, _) => {}
        }
    }

    if matches!(s, S::Atom) {
        s = S::Expr;
        push_seq(&mut texpr, Expr::Atom(String::from(&txt[j..])));
    }
    if matches!(s, S::Expr) {
        s = S::Line;
        push_term(tdisp, texpr, &parstack);
    }
    if !matches!(s, S::Line) {
        panic!("unexpected eof");
    }

    fn ground(e: &mut Expr, ts: &[(usize, &str)]) {
        match e {
            Expr::Seq(es) | Expr::Cont(es) | Expr::Alt(es) => {
                es.iter_mut().for_each(|e| ground(e, ts));
            }
            Expr::Many(e) | Expr::Opt(e) => ground(&mut **e, ts),
            Expr::Atom(a) => {
                if a == "." {
                    *e = Expr::Set(false, String::new());
                } else if a.starts_with("0x") && a.len() == 4 {
                    *e = Expr::Str((u8::from_str_radix(&a[2..], 16).unwrap() as char).to_string());
                } else if let Some((i, _)) = ts.iter().find(|(_, s)| s == &a) {
                    *e = Expr::Term(*i);
                }
            }
            _ => {}
        }
    }

    fn convert_left_recursion(tid: usize, e: &mut Expr) -> Option<Expr> {
        match e {
            Expr::Seq(es) | Expr::Cont(es) => {
                if let Some(Expr::Term(t)) = es.get(0) {
                    if *t == tid {
                        es.remove(0);
                        let tail = if es.len() > 1 {
                            let mut tail = Expr::Alt(vec![]);
                            std::mem::swap(e, &mut tail);
                            tail
                        } else {
                            es.pop().unwrap()
                        };
                        return Some(tail);
                    }
                }
                None
            }
            _ => None,
        }
    }

    for (tid, Term { expr, .. }) in ts.iter_mut().enumerate() {
        ground(expr, &tids);
        let mut tail_exprs = vec![];

        // convert top-level left-recursive
        match expr {
            Expr::Alt(es) => {
                let mut idxs = vec![];
                for (i, e) in es.iter_mut().enumerate() {
                    if let Some(tail) = convert_left_recursion(tid, e) {
                        tail_exprs.push(tail);
                        idxs.push(i);
                    }
                }
                for i in idxs.into_iter().rev() {
                    es.remove(i);
                }
                if es.len() == 1 {
                    *expr = es.pop().unwrap();
                }
            }
            Expr::Seq(es) | Expr::Cont(es) => {
                if let Some(tail) = convert_left_recursion(tid, expr) {
                    tail_exprs.push(tail);
                }
            }
            _ => {}
        }
        if !tail_exprs.is_empty() {
            let tail = if tail_exprs.len() > 1 {
                Expr::Alt(tail_exprs)
            } else {
                tail_exprs.pop().unwrap()
            };
            let mut head = Expr::Alt(vec![]);
            std::mem::swap(expr, &mut head);
            *expr = Expr::Seq(vec![head, Expr::Many(Box::new(tail))]);
        }
    }

    Terms(ts)
}

struct Parser<'t, 's> {
    terms: &'t Terms,
    expr: &'t Expr,
    cycles: &'t mut Vec<bool>,
    src: &'s str,
}

#[derive(Debug)]
enum SynElem<'s> {
    Term(usize, Box<SynElem<'s>>),
    Node(Vec<SynElem<'s>>),
    Leaf(Span<'s>),
}

struct SynTree<'s, 't> {
    src: &'s str,
    root: SynElem<'s>,
    terms: &'t Terms,
}

type Span<'s> = (&'s str, usize, usize);

impl<'s> SynElem<'s> {
    fn span(&self) -> Span<'s> {
        match self {
            SynElem::Term(_, e) => e.span(),
            SynElem::Node(es) => {
                let (str, start, _) = es.first().map(SynElem::span).unwrap();
                (str, start, es.last().map(SynElem::span).unwrap().2)
            }
            SynElem::Leaf((src, s, e)) => (src, *s, *e),
        }
    }
}

struct SynTreeDebugElem<'e>(&'e Terms, &'e SynElem<'e>);
impl Debug for SynTreeDebugElem<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.1 {
            SynElem::Term(t, e) => f
                .debug_map()
                .key(&self.0[*t].display)
                .value(&SynTreeDebugElem(self.0, &**e))
                .finish(),
            SynElem::Node(es) => f
                .debug_list()
                .entries(es.iter().map(|e| SynTreeDebugElem(self.0, e)))
                .finish(),
            SynElem::Leaf(span) => write!(f, "{:?}", &span.0[span.1..span.2]),
        }
    }
}
impl Debug for SynTree<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("SynTree")?;
        f.debug_list()
            .entry(&SynTreeDebugElem(self.terms, &self.root))
            .finish()
    }
}

impl<'s, 't> SynTree<'s, 't> {
    fn walk(&mut self, mut f: impl FnMut(&mut SynElem) -> bool) {
        let f = &mut f;
        fn walk_expr(e: &mut SynElem, f: &mut dyn FnMut(&mut SynElem) -> bool) {
            if !f(e) {
                return;
            }
            match e {
                SynElem::Term(_, e) => walk_expr(&mut **e, f),
                SynElem::Node(es) => es.iter_mut().for_each(|e| walk_expr(e, f)),
                SynElem::Leaf(..) => {}
            }
        }
        walk_expr(&mut self.root, f)
    }
}

impl Terms {
    fn parse<'t, 's>(&'t self, start: &str, src: &'s str) -> ParseResult<'s, SynTree<'s, 't>> {
        let start = match self.0.iter().enumerate().find(|(_, t)| t.display == start) {
            Some((i, _)) => i,
            None => return Err((src, "start symbol is not defined in terms")),
        };

        // empty elems are represented as SynElem::Node(vec![])
        fn prune(e: &mut SynElem) {
            match e {
                SynElem::Term(_, et) => {
                    prune(&mut **et);
                    if let SynElem::Node(es) = &**et {
                        if es.is_empty() {
                            *e = SynElem::Node(vec![]);
                        }
                    }
                }
                SynElem::Node(es) => es.iter_mut().for_each(prune),
                SynElem::Leaf(_) => {}
            }
        }

        let terms = self;
        Parser {
            terms,
            // we wrap the start term here to trim whitespace
            expr: &Expr::Seq(vec![
                Expr::Str(String::from("")),
                Expr::Term(start),
                Expr::Str(String::from("")),
            ]),
            cycles: &mut vec![false; self.0.len()],
            src,
        }
        .parse(src)
        .map(|(e, tail)| {
            let mut root = match e {
                SynElem::Node(mut es) => es.remove(1),
                _ => unreachable!("we wrapped the starting expression"),
            };
            prune(&mut root);
            (SynTree { src, root, terms }, tail)
        })
    }
}

type ParseResult<'s, T = SynElem<'s>> = Result<(T, &'s str), (&'s str, &'static str)>;
impl<'t, 's> Parser<'t, 's> {
    fn subexpr(&mut self, e: &Expr, s: &'s str) -> ParseResult<'s> {
        Parser {
            terms: self.terms,
            expr: e,
            cycles: self.cycles,
            src: self.src,
        }
        .parse(s)
    }

    fn parse(&mut self, mut s: &'s str) -> ParseResult<'s> {
        match &self.expr {
            Expr::Seq(es) | Expr::Cont(es) => {
                let ws = Expr::Many(Box::new(Expr::Set(true, String::from(" \t\n"))));
                let mut nodes = vec![];
                let mut node;
                for e in es {
                    (node, s) = self.subexpr(e, s)?;
                    nodes.push(node);
                    if matches!(&self.expr, Expr::Seq(es)) {
                        (_, s) = self.subexpr(&ws, s)?;
                    }
                }
                Ok((SynElem::Node(nodes), s))
            }
            Expr::Alt(es) => {
                // try to limit recursion
                let cycles = self.cycles.clone();
                for e in es {
                    if let Ok(res) = self.subexpr(e, s) {
                        return Ok(res);
                    }
                }
                *self.cycles = cycles;
                return Err((s, "no alternatives matched"));
            }
            Expr::Many(e) => {
                let mut nodes = vec![];
                while let Ok((t, s1)) = self.subexpr(&**e, s) {
                    nodes.push(t);
                    s = s1;
                }
                Ok((SynElem::Node(nodes), s))
            }
            Expr::Opt(e) => match self.subexpr(&**e, s) {
                Ok((t, s)) => Ok((t, s)),
                Err(_) => Ok((SynElem::Node(vec![]), s)),
            },
            Expr::Term(t) => {
                if self.cycles[*t] {
                    return Err((s, "infinite loop"));
                }
                self.cycles[*t] = true;
                let (sn, s1) = self.subexpr(&self.terms[*t].expr, s)?;
                Ok((SynElem::Term(*t, Box::new(sn)), s1))
            }
            Expr::Atom(a) => Err((s, "cannot parse bare atom")),
            Expr::Str(s1) => {
                let i = s1.len();
                if s.get(..i) == Some(s1) {
                    *self.cycles = vec![false; self.terms.0.len()];
                    let start = self.src.len() - s.len();
                    Ok((SynElem::Leaf((self.src, start, start + i)), &s[i..]))
                } else {
                    Err((s, "unable to match string literal"))
                }
            }
            Expr::Set(pos, set) => {
                if !s.is_empty() && set.contains(s.chars().next().unwrap()) == *pos {
                    *self.cycles = vec![false; self.terms.0.len()];
                    let mut cis = s.char_indices().map(|(i, _)| i);
                    cis.next(); // just 0
                    let i = cis.next().unwrap_or(s.len());
                    let start = self.src.len() - s.len();
                    Ok((SynElem::Leaf((self.src, start, start + i)), &s[i..]))
                } else {
                    Err((s, "unable to match charset"))
                }
            }
        }
    }
}

impl SynElem<'_> {
    fn flatten(&mut self) {
        match self {
            SynElem::Term(_, e) => e.flatten(),
            SynElem::Node(es) => {
                es.iter_mut().for_each(SynElem::flatten);
                *es = std::mem::take(es)
                    .into_iter()
                    .fold(vec![], |mut es, e| match e {
                        SynElem::Node(es1) => {
                            es.extend(es1);
                            es
                        }
                        e => {
                            es.push(e);
                            es
                        }
                    });
                if es.len() == 1 {
                    *self = es.pop().unwrap();
                }
            }
            _ => {}
        }
    }
}

fn main() {
    let mut ts = parse_terms(
        r#"
            c ::= '''.''' / "0x"[0-9][0-9]
            s ::= '"'([^"\]/'\'.)*'"'
            a ::= [a-zA-Z_][a-zA-Z0-9_]
            e_cont ::= c / s / a / '(' e ')' / (e)(e)
            e ::= e_cont / e e / e '/' e
            t ::= a "::=" e / t(0x0a)t
        "#,
    );
    println!("{ts:#?}");
    for t in &ts.0 {
        println!("{t:?}");
    }

    let mut ts = parse_terms(
        r#"
            v ::= '0' / [1-9][0-9]*
            r ::= 'r'[0-9]
            arg ::= v / r
            e ::= "ld" arg arg / "mov" arg arg / "st" arg arg / "add" arg arg / e e

            t ::= 'D' / 'P' / '?'

            G ::= "{}" / G ',' r ':' t
            s ::= "s"
            h ::= "h"
            Pred ::= G ":-" r ':' t  / '(' s ',' h ',' e ')' "-->" '(' s ',' h ')'
            Ident ::= [a-zA-Z0-9_][a-zA-Z0-9_]*
            Judgement ::= Pred* "---"'-'* '[' Ident ']' Pred
        "#,
    );

    println!("{ts:#?}");
    for t in &ts.0 {
        println!("{t:?}");
    }

    let src = r#"
        ld r1 r2
        mov r2 45
        add r2 2
    "#;
    let pres = ts.parse("e", src);
    println!("{pres:?}");

    let (mut stree, _) = pres.unwrap();
    stree.root.flatten();
    stree.walk(|e| match e {
        SynElem::Term(t, e1) if ts[*t].display == "r" || ts[*t].display == "v" => {
            let span = e1.span();
            **e1 = SynElem::Leaf(span);
            false
        }
        _ => true,
    });
    println!("{stree:?}");
}
