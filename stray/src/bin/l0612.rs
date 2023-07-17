#![allow(unused)]

use std::fmt::Debug;

// tt ::= block<_> | inl_tt
// inl_tt ::= (node | string | tok) ('\\' '\n' | [ \t])*
// node ::= '(' tt* ')'
//        | '[' tt* ']'
//        | '{' tt* '}'
// tok ::= [^ \t\n(){}[]"]+
// string ::= '"' ([^"\]|'\\'.)* '"'
// ind<s> ::= s := [ \t]*
// block<s> ::= '\n' ind<s> inl_tt* (block<s> | block<s+_>)*
type Span<'s> = (usize, usize, &'s str);
#[derive(Clone)]
enum TT<'s> {
    Block(Span<'s>, Vec<TT<'s>>),
    Node(char, Vec<TT<'s>>),
    Token(Span<'s>),
    String(Span<'s>),
}

struct SpanDebug<'s>(Span<'s>);
impl Debug for SpanDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let SpanDebug((l, r, txt)) = self;
        write!(f, "{l}..{r}{txt:?}")
    }
}

impl Debug for TT<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TT::Block(s, tts) => f
                .debug_tuple("Block")
                .field(&SpanDebug(*s))
                .field(tts)
                .finish(),
            TT::Node(c, tts) => f.debug_tuple("Node").field(c).field(tts).finish(),
            TT::Token(s) => f.debug_tuple("Token").field(&SpanDebug(*s)).finish(),
            TT::String(s) => f.debug_tuple("String").field(&SpanDebug(*s)).finish(),
        }
    }
}

impl PartialEq for TT<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TT::Block((_, _, s1), tts1), TT::Block((_, _, s2), tts2)) => (s1, tts1) == (s2, tts2),
            (TT::Node(c1, tts1), TT::Node(c2, tts2)) => (c1, tts1) == (c2, tts2),
            (TT::Token((_, _, s1)), TT::Token((_, _, s2))) => s1 == s2,
            (TT::String((_, _, s1)), TT::String((_, _, s2))) => s1 == s2,
            (_, _) => false,
        }
    }
}

type TTResult<T> = Result<(T, usize), (usize, &'static str)>;
impl<'s> TT<'s> {
    fn parse(txt: &'s str) -> TTResult<Self> {
        fn string<'s>(txt: &'s str, start: usize) -> TTResult<Span<'s>> {
            let mut bs = txt.bytes().enumerate().skip(start);
            if bs.next() != Some((start, b'"')) {
                return Err((start, "expected '\"'"));
            }
            let start = start + 1;
            let mut esc = false;
            while let Some((i, b)) = bs.next() {
                match (b, esc) {
                    (_, true) => esc = false,
                    (b'\\', false) => esc = true,
                    (b'"', false) => return Ok(((start, i, &txt[start..i]), i + 1)),
                    (_, false) => {}
                }
            }
            Err((txt.len(), "expected closing '\"'"))
        }
        fn token<'s>(txt: &'s str, start: usize) -> TTResult<Span<'s>> {
            for (i, b) in txt.bytes().enumerate().skip(start) {
                if "\"()[]{} \t\n".contains(b as char) {
                    if i == start {
                        return Err((start, "expected token"));
                    } else {
                        return Ok(((start, i, &txt[start..i]), i));
                    }
                }
            }
            if txt.len() == start {
                Err((start, "expected token, not empty string"))
            } else {
                Ok(((start, txt.len(), &txt[start..]), txt.len()))
            }
        }
        fn node<'s>(txt: &'s str, mut start: usize) -> TTResult<Vec<TT<'s>>> {
            let mut bs = txt.bytes().skip(start);
            let right = match bs.next() {
                Some(b'(') => b')',
                Some(b'[') => b']',
                Some(b'{') => b'}',
                _ => return Err((start, "expected node start '(' '[' or '{'")),
            };
            start += 1;
            let mut tts = vec![];
            while let Ok((tt, next)) = tt(txt, start) {
                tts.push(tt);
                start = next;
            }
            if txt.bytes().skip(start).next() == Some(right) {
                Ok((tts, start + 1))
            } else {
                Err((start, "expected node end"))
            }
        }
        fn inl_tt<'s>(txt: &'s str, start: usize) -> TTResult<TT<'s>> {
            let (tt, start) = match txt.bytes().skip(start).next() {
                Some(b'"') => string(txt, start).map(|(s, next)| (TT::String(s), next)),
                Some(b @ (b'(' | b'[' | b'{')) => {
                    node(txt, start).map(|(tts, next)| (TT::Node(b as char, tts), next))
                }
                Some(b')' | b']' | b'}' | b'\n' | b' ' | b'\t') => {
                    Err((start, "expected inline tt"))
                }
                Some(b) => token(txt, start).map(|(s, next)| (TT::Token(s), next)),
                None => Err((start, "unexpected eof while parsing inline tt")),
            }?;
            // skip trailing ws
            for (i, b) in txt.bytes().enumerate().skip(start) {
                if !" \t".contains(b as char) {
                    return Ok((tt, i));
                }
            }
            Ok((tt, txt.len()))
        }
        fn ind<'s>(txt: &'s str, mut start: usize) -> TTResult<Span<'s>> {
            let mut bs = txt.bytes().enumerate().skip(start);
            match bs.next() {
                Some((i, b'\n')) => start = i + 1,
                _ => return Err((start, "expected newline to start indent")),
            }
            for (i, b) in bs {
                if !" \t".contains(b as char) {
                    return Ok(((start, i, &txt[start..i]), i));
                }
            }
            Ok(((start, txt.len(), &txt[start..]), txt.len()))
        }
        fn block_tail<'s>(
            txt: &'s str,
            mut start: usize,
            bind: Span<'s>,
            mut tts: Vec<TT<'s>>,
        ) -> TTResult<(Span<'s>, Vec<TT<'s>>)> {
            while let Ok((nind, mut next)) = ind(txt, start) {
                let mut inl_tts = vec![];
                while let Ok((tt, next2)) = inl_tt(txt, next) {
                    next = next2;
                    inl_tts.push(tt);
                }

                if bind.2 == nind.2 {
                    start = next;
                    tts.extend(inl_tts);
                    continue;
                }

                if nind.2.starts_with(bind.2) {
                    println!("indent block");
                    let ((s, btts), next) = block_tail(txt, next, nind, inl_tts)?;
                    start = next;
                    tts.push(TT::Block(s, btts));
                    continue;
                }

                println!(
                    "handle block_tail case {:?} {:?}",
                    SpanDebug(bind),
                    SpanDebug(nind)
                );
                break;
            }
            Ok(((bind, tts), start))
        }
        fn block<'s>(txt: &'s str, start: usize) -> TTResult<(Span<'s>, Vec<TT<'s>>)> {
            let (bind, mut start) = ind(txt, start)?;
            let mut inl_tts = vec![];
            while let Ok((tt, next)) = inl_tt(txt, start) {
                inl_tts.push(tt);
                start = next;
            }
            block_tail(txt, start, bind, inl_tts)
        }
        fn tt<'s>(txt: &'s str, start: usize) -> TTResult<TT<'s>> {
            match txt.bytes().skip(start).next() {
                Some(b'\n') => block(txt, start).map(|((s, tts), next)| (TT::Block(s, tts), next)),
                _ => inl_tt(txt, start),
            }
        }

        let mut bs = txt.bytes().enumerate();
        let mut start = 0;
        while let Some((i, b)) = bs.next() {
            if !" \t".contains(b as char) {
                start = i;
                break;
            }
        }
        if txt.len() == 0 {
            return Err((start, "input is empty"));
        }
        let bind = (0, start, &txt[..start]);
        let mut tts = vec![];
        while let Ok((tt, next)) = inl_tt(txt, start) {
            tts.push(tt);
            start = next;
        }
        let ((mut bind, mut tts), next) = block_tail(txt, start, bind, tts)?;
        if bind.2 != "" {
            tts = vec![TT::Block(bind, tts)];
            bind = (0, 0, "");
        }
        start = next;
        while let Ok(((s, tt), next)) = block(txt, start) {
            if s == bind {
                tts.extend(tt);
            } else {
                tts.push(TT::Block(s, tt));
            }
            start = next;
        }
        Ok((TT::Block(bind, tts), start))
    }

    fn print(&self) {
        match self {
            TT::Block((_, _, ind), tts) => {
                println!();
                let mut nl = true;
                for tt in tts {
                    if matches!(tt, TT::Block(_, _)) {
                        nl = true;
                    } else if nl {
                        print!("{ind}");
                        nl = false;
                    }
                    tt.print();
                }
                println!();
            }
            TT::Node(l, tts) => {
                let r = match l {
                    '(' => ')',
                    '[' => ']',
                    '{' => '}',
                    _ => unreachable!(),
                };
                print!("{l}");
                for tt in tts {
                    tt.print();
                }
                print!("{r} ");
            }
            TT::Token((_, _, t)) => print!("{t} "),
            TT::String((_, _, s)) => print!("\"{s}\" "),
        }
    }
}

fn main() {
    let res = TT::parse(
        r#":= main[A] (a : A , b : A)
    := bar (c : A)
        c + 42
    a + bar(b)

:= foo
    "foo"
"#,
    );
    println!("{res:#?}");
    res.unwrap().0.print();
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn simple() {
        let input = r#"
:= foo
    32 + 24 .
    "foo"
"#;
        let res = TT::parse(input);
        let lit = |s| (0, 0, s);
        let tok = |s| TT::Token(lit(s));
        assert_eq!(
            res,
            Ok((
                TT::Block(
                    lit(""),
                    vec![
                        tok("::"),
                        tok("foo"),
                        tok("="),
                        TT::Block(
                            lit("    "),
                            vec![
                                tok("32"),
                                tok("+"),
                                tok("24"),
                                tok("."),
                                TT::String(lit("foo")),
                            ]
                        )
                    ]
                ),
                input.len()
            ))
        );
    }

    #[test]
    fn double_indent() {
        let lit = |s| (0, 0, s);
        let tok = |s| TT::Token(lit(s));
        let input = r#":: foo =
    32 .
    := bar
        42 .
    32 + bar()
"#;
        let res = TT::parse(input);
        assert_eq!(
            res,
            Ok((
                TT::Block(
                    lit(""),
                    vec![
                        tok("::"),
                        tok("foo"),
                        tok("="),
                        TT::Block(
                            lit("    "),
                            vec![
                                tok("32"),
                                tok("."),
                                tok("::"),
                                tok("bar"),
                                tok("="),
                                TT::Block(lit("        "), vec![tok("42"), tok(".")]),
                                tok("32"),
                                tok("+"),
                                tok("bar"),
                                TT::Node('(', vec![])
                            ]
                        )
                    ]
                ),
                input.len()
            ))
        );
    }
}
