#![allow(unused)]

use std::fmt::Debug;

#[derive(Clone, PartialEq)]
enum Tree<T> {
    Node(Vec<Tree<T>>),
    Leaf(T),
}

struct DebugTree<'t, T>(&'t Tree<T>);
impl<T: Debug> Debug for DebugTree<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.0 {
            Tree::Node(cs) => f.debug_list().entries(cs.iter().map(DebugTree)).finish(),
            Tree::Leaf(val) => val.fmt(f),
        }
    }
}
impl<T: Debug> Debug for Tree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Tree").field(&DebugTree(self)).finish()
    }
}

fn parse_spaced<'t, R>(txt: &'t str, mut parse_leaf: impl FnMut(&'t str) -> Tree<R>) -> Tree<R> {
    fn append<T>(root: &mut Tree<T>, depth: usize, val: Tree<T>) {
        match (root, depth) {
            (Tree::Node(cs), 0) => cs.push(val),
            (Tree::Node(cs), _) => append(cs.last_mut().unwrap(), depth - 1, val),
            (root @ Tree::Leaf(_), _) => {
                let mut lhs = std::mem::replace(root, Tree::Node(vec![]));
                lhs = Tree::Node(vec![lhs, val]);
                for i in 0..depth {
                    lhs = Tree::Node(vec![lhs]);
                }
                std::mem::replace(root, lhs);
            }
        }
    }

    let mut depth = 0;
    let mut root = Tree::Node(vec![]);
    let mut cs = txt.char_indices();
    #[derive(Debug, Clone, Copy)]
    enum State {
        S,
        W,
        C,
        C0,
    }
    let mut s = State::S;
    let mut wslen = 0;
    let mut tok_start = 0;
    use State::*;
    while let Some((i, c)) = cs.next() {
        match (s, c) {
            (S, ' ') => {}
            (S, c) => {
                s = C0;
                tok_start = i;
            }
            (C0, ' ') => {
                s = W;
                root = parse_leaf(&txt[tok_start..i]);
                wslen = 1;
            }
            (C, ' ') => {
                s = W;
                while depth < wslen {
                    root = Tree::Node(vec![root]);
                    depth += 1;
                }
                append(&mut root, depth - wslen, parse_leaf(&txt[tok_start..i]));
                wslen = 1;
            }
            (C | C0, c) => {}
            (W, ' ') => {
                wslen += 1;
            }
            (W, c) => {
                s = C;
                tok_start = i;
            }
        }
    }
    match s {
        S | W => {}
        C0 => root = parse_leaf(&txt[tok_start..]),
        C => append(&mut root, depth - wslen, parse_leaf(&txt[tok_start..])),
    }
    root
}

fn parse_blocks<'t, R>(txt: &'t str, mut parse_leaf: impl FnMut(&'t str) -> Tree<R>) -> Tree<R> {
    #[derive(Debug, Clone, Copy)]
    enum State {
        T,
        C,
    }
    use State::*;
    let mut s = T;
    let mut cs = txt.char_indices();
    let mut indent = 0;
    let mut tok_start = 0;
    let mut depth = 0;
    let mut root = vec![];
    fn append<T>(root: &mut Vec<Tree<T>>, depth: usize, val: Tree<T>) {
        match (root.last_mut(), depth) {
            (Some(_), 0) => root.push(val),
            (Some(Tree::Node(cs)), _) => append(cs, depth - 1, val),
            (None | Some(Tree::Leaf(_)), _) => {
                let mut node = val;
                for i in 0..depth {
                    node = Tree::Node(vec![node]);
                }
                root.push(node);
            }
        }
    }
    while let Some((i, c)) = cs.next() {
        match (s, c) {
            (T, '\n') => {
                indent = 0;
            }
            (T, '\t') => {
                indent += 1;
            }
            (T, c) => {
                s = C;
                tok_start = i;
            }
            (C, '\n') => {
                s = T;
                append(&mut root, indent, parse_leaf(&txt[tok_start..i]));
                indent = 0;
            }
            (C, c) => {}
        }
    }
    match s {
        T => {}
        C => append(&mut root, indent, parse_leaf(&txt[tok_start..])),
    }
    Tree::Node(root)
}

impl<T> Tree<T> {
    fn map_leaf<R>(self, mut f: impl FnMut(T) -> Tree<R>) -> Tree<R> {
        self.map(f, Tree::Node)
    }

    fn map<R>(self, mut leaf: impl FnMut(T) -> R, mut node: impl FnMut(Vec<R>) -> R) -> R {
        fn inner<T, R>(
            root: Tree<T>,
            leaf: &mut dyn FnMut(T) -> R,
            node: &mut dyn FnMut(Vec<R>) -> R,
        ) -> R {
            match root {
                Tree::Node(vs) => {
                    let vs = vs.into_iter().map(|v| inner(v, leaf, node)).collect();
                    node(vs)
                }
                Tree::Leaf(v) => leaf(v),
            }
        }
        inner(self, &mut leaf, &mut node)
    }
}

fn parse_nums(txt: &str) -> Tree<Result<u32, &str>> {
    #[repr(u32)]
    #[derive(Debug, Clone, Copy)]
    enum State {
        N2 = 2,
        N10 = 10,
        N16 = 16,
        S,
        P,
        I,
        N0,
    }
    use State::*;

    let mut cs = txt.char_indices();
    let mut tok_start = 0;
    let mut seq = vec![];
    let mut s = S;
    let mut num = 0;
    while let Some((i, c)) = cs.next() {
        match (s, c) {
            (S, '0') => {
                s = N0;
                tok_start = i;
            }
            (S, '1'..='9') => {
                s = N10;
                tok_start = i;
            }
            (S, c) if c.is_alphabetic() || c == '_' => {
                s = I;
                tok_start = i;
            }
            (S, c) => {
                s = P;
                tok_start = i;
            }
            (N0, '0'..='9' | '_') => {
                s = N10;
            }
            (N0, 'x') => {
                s = N16;
                tok_start = i + 1;
            }
            (N0, 'b') => {
                s = N2;
                tok_start = i + 1;
            }
            (N0, c) if c.is_alphabetic() || c == '_' => {
                s = I;
                tok_start = i;
                seq.push(Tree::Leaf(Ok(0)));
            }
            (N0, c) => {
                s = P;
                tok_start = i;
                seq.push(Tree::Leaf(Ok(0)))
            }
            (N2 | N10 | N16, '_') => {
                if tok_start != i {
                    let n = u32::from_str_radix(&txt[tok_start..i], s as u32).unwrap();
                    num += n;
                }
                tok_start = i + 1;
            }
            (N2, '0' | '1') | (N10, '0'..='9') | (N16, '0'..='9' | 'a'..='f' | 'A'..='F') => {
                num *= s as u32;
            }
            (N2 | N10 | N16, c) => {
                if c.is_alphabetic() {
                    s = I;
                } else {
                    s = P;
                }
                let n = u32::from_str_radix(&txt[tok_start..i], s as u32).unwrap();
                seq.push(Tree::Leaf(Ok(num + n)));
                num = 0;
                tok_start = i;
            }
            (P, '0') => {
                s = N0;
                seq.push(Tree::Leaf(Err(&txt[tok_start..i])));
                tok_start = i;
            }
            (P, '1'..='9') => {
                s = N10;
                seq.push(Tree::Leaf(Err(&txt[tok_start..i])));
                tok_start = i;
            }
            (P, c) if c.is_alphanumeric() || c == '_' => {
                s = I;
                seq.push(Tree::Leaf(Err(&txt[tok_start..i])));
                tok_start = i;
            }
            (P, c) => {}
            (I, '_') => {}
            (I, c) if c.is_alphanumeric() => {}
            (I, c) => {
                s = P;
                seq.push(Tree::Leaf(Err(&txt[tok_start..i])));
                tok_start = i;
            }
        }
    }

    match s {
        S => {}
        P | I => seq.push(Tree::Leaf(Err(&txt[tok_start..]))),
        N0 => seq.push(Tree::Leaf(Ok(0))),
        N2 | N10 | N16 => seq.push(Tree::Leaf(Ok(
            num + u32::from_str_radix(&txt[tok_start..], s as u32).unwrap()
        ))),
    }
    if seq.len() == 1 {
        seq.pop().unwrap()
    } else {
        Tree::Node(seq)
    }
}

enum Expr {
    Var(String),
    Num(u32),
    Add(Vec<Expr>),
    Mul(Vec<Expr>),
    Seq(Vec<Expr>),
    Neg(Box<Expr>),
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_spaced() {
        assert_eq!(
            parse_spaced(r#"1 + 2  *  - 3"#, Tree::Leaf),
            Tree::Node(vec![
                Tree::Node(vec![Tree::Leaf("1"), Tree::Leaf("+"), Tree::Leaf("2")]),
                Tree::Leaf("*"),
                Tree::Node(vec![Tree::Leaf("-"), Tree::Leaf("3")])
            ])
        );
    }

    #[test]
    fn test_blocks() {
        let example = r#"
				a
				b
			c
				d
					e
			f"#;
        assert_eq!(
            parse_blocks(example, Tree::Leaf),
            Tree::Node(vec![Tree::Node(vec![Tree::Node(vec![Tree::Node(vec![
                Tree::Node(vec![Tree::Leaf("a"), Tree::Leaf("b"),]),
                Tree::Leaf("c"),
                Tree::Node(vec![Tree::Leaf("d"), Tree::Node(vec![Tree::Leaf("e"),])]),
                Tree::Leaf("f"),
            ])])])])
        )
    }

    #[test]
    fn test_nums() {
        let example = r#"-2*=a+0x5_0;foo()0b1101/0"#;
        assert_eq!(
            parse_nums(example),
            Tree::Node(
                [
                    Err("-"),
                    Ok(2),
                    Err("*="),
                    Err("a"),
                    Err("+"),
                    Ok(0x50),
                    Err(";"),
                    Err("foo"),
                    Err("()"),
                    Ok(0b1101),
                    Err("/"),
                    Ok(0)
                ]
                .into_iter()
                .map(Tree::Leaf)
                .collect()
            )
        );
    }
}

fn main() {
    let mut blocks = parse_blocks(
        r#"
			a + 2  *  -3
			foo
		bar
			baz
				quux
		end"#,
        |l| parse_spaced(l, Tree::Leaf),
    );

    println!("{blocks:#?}");
}
