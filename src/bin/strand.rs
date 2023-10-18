use std::collections::VecDeque;
use std::convert::TryFrom;
use std::fmt::Debug;

#[derive(Clone, PartialEq)]
enum V {
    A(&'static str),
    N(i64),
    X(usize),
    E(&'static str, Vec<V>),
}

impl Debug for V {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            V::A(a) => write!(f, "{a}"),
            V::N(n) => write!(f, "{n}"),
            V::X(x) => write!(f, "_{x}"),
            V::E(hd, vs) => {
                write!(f, "{hd}(")?;
                write!(f, "{:?}", vs[0])?;
                for v in &vs[1..] {
                    write!(f, ", {v:?}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl TryFrom<&V> for Option<i64> {
    type Error = String;
    fn try_from(v: &V) -> Result<Option<i64>, String> {
        match *v {
            V::A(a) => a.parse().map(Some).map_err(|e| format!("{e}")),
            V::N(n) => Ok(Some(n)),
            V::X(_) => Ok(None),
            V::E(_, _) => Err(format!("unable to convert {v:?} to number")),
        }
    }
}

trait LowerV: Sized {
    fn lower(v: &V) -> Option<Self>;
}

impl<T, Err> LowerV for T
where
    Option<T>: for<'z> TryFrom<&'z V, Error = Err>,
    Err: Debug,
{
    fn lower(v: &V) -> Option<Self> {
        Option::try_from(v).unwrap()
    }
}

fn eq(a: &V, b: &V) -> Option<bool> {
    match (a, b) {
        (a, b) if a == b => Some(true),
        (V::X(_), _) | (_, V::X(_)) => None,
        (V::E(ahd, atl), V::E(bhd, btl)) if (ahd, atl.len()) == (bhd, btl.len()) => {
            for i in 0..atl.len() {
                match eq(&atl[i], &btl[i]) {
                    Some(true) => {}
                    res => return res,
                }
            }
            Some(true)
        }
        _ => Some(false),
    }
}

fn neq(a: &V, b: &V) -> Option<bool> {
    eq(a, b).map(|b| !b)
}

fn ge(a: i64, b: i64) -> Option<bool> {
    Some(a >= b)
}

fn gt(a: i64, b: i64) -> Option<bool> {
    Some(a > b)
}

fn known(v: &V) -> Option<bool> {
    match v {
        V::X(_) => Some(false),
        _ => Some(true),
    }
}

fn unknown(v: &V) -> Option<bool> {
    known(v).map(|b| !b)
}

fn bind(env: &mut Vec<V>, arg: &V, val: &V) -> Option<bool> {
    match (arg, val) {
        (&V::X(x), v) if env.get(x) == Some(&V::X(x)) => {
            env[x] = v.clone();
            Some(true)
        }
        (V::X(_), _) => panic!("var already bound"),
        (arg, val) => panic!("unable to bind {arg:?} := {val:?}"),
    }
}

fn arith_bind(env: &mut Vec<V>, x: &V, arith: &[V]) -> Option<bool> {
    let mut stack = vec![];
    for a in arith {
        match *a {
            V::N(n) => stack.push(n),
            V::A(c @ ("+" | "*" | "-")) => {
                let (b, a) = (stack.pop().unwrap(), stack.pop().unwrap());
                match c {
                    "+" => stack.push(a + b),
                    "*" => stack.push(a * b),
                    "-" => stack.push(a - b),
                    _ => unreachable!(),
                }
            }
            V::A(a) => stack.push(a.parse().unwrap()),
            _ => return None,
        }
    }
    let v = stack.pop().unwrap();
    bind(env, x, &V::N(v))
}

fn bind_yx(env: &mut Vec<V>, bindings: &mut Vec<(&'static str, usize)>, v: &mut V) {
    let z = match *v {
        V::A(a) if a.chars().next().unwrap_or('0').is_uppercase() => a,
        _ => return,
    };

    if let Some(&(_, x)) = bindings.iter().find(|&&(y, _)| y == z) {
        *v = V::X(x);
    } else {
        let x = env.len();
        *v = V::X(x);
        env.push(v.clone());
        bindings.push((z, x));
    }
}

type Thunk = (&'static str, Vec<V>);

fn main() {
    let init = vec![
        (":=", vec![V::A("X"), V::N(7)]),
        ("div", vec![V::A("X"), V::N(2), V::A("Res")]),
    ];
    let mut procs = VecDeque::new();
    let mut globals = vec![];
    let mut init_bindings = vec![];
    for (hd, mut args) in init.clone() {
        for a in args.iter_mut() {
            bind_yx(&mut globals, &mut init_bindings, a);
        }
        procs.push_front((hd, args));
    }
    let clauses: Vec<(&str, usize, Vec<Thunk>, Vec<Thunk>)> = vec![
        (
            "div",
            3,
            vec![
                ("=\\=", vec![V::X(1), V::N(0)]),
                (">=", vec![V::X(0), V::X(1)]),
            ],
            vec![
                ("is", vec![V::A("X"), V::X(0), V::X(1), V::A("-")]),
                ("div", vec![V::A("X"), V::X(1), V::A("Out")]),
                ("is", vec![V::X(2), V::A("Out"), V::N(1), V::A("+")]),
            ],
        ),
        (
            "div",
            3,
            vec![
                ("=\\=", vec![V::X(1), V::N(0)]),
                (">", vec![V::X(1), V::X(0)]),
            ],
            vec![(":=", vec![V::X(2), V::N(0)])],
        ),
    ];

    fn guards_match(guards: &[Thunk], env: &[V]) -> Option<bool> {
        let bind = |a: &V| match *a {
            V::X(x) => env[x].clone(),
            ref v => v.clone(),
        };
        for (hd, args) in guards {
            let args: Vec<_> = args.iter().map(|a| bind(a)).collect();
            let res = match (*hd, args.len()) {
                ("==", 2) => eq(&args[0], &args[1]),
                ("=\\=", 2) => neq(&args[0], &args[1]),
                ("known", 1) => known(&args[0]),
                ("unknown", 1) => unknown(&args[0]),
                (">=", 2) => ge(LowerV::lower(&args[0])?, LowerV::lower(&args[1])?),
                (">", 2) => gt(LowerV::lower(&args[0])?, LowerV::lower(&args[1])?),
                ("=<", 2) => ge(LowerV::lower(&args[1])?, LowerV::lower(&args[0])?),
                ("<", 2) => gt(LowerV::lower(&args[1])?, LowerV::lower(&args[0])?),
                (hd, arity) => panic!("cannot use {hd}/{arity} in guard expression"),
            };
            match res {
                Some(true) => {}
                res => return res,
            }
        }
        Some(true)
    }

    while let Some((hd, mut args)) = procs.pop_back() {
        for a in args.iter_mut() {
            match *a {
                V::X(x) => *a = globals[x].clone(),
                _ => {}
            }
        }
        println!("{:?} {globals:?}", V::E(hd, args.clone()));

        let res = match (hd, args.len()) {
            (":=", 2) => bind(&mut globals, &args[0], &args[1]),
            ("is", n) if n >= 2 => arith_bind(&mut globals, &args[0], &args[1..]),
            (hd, n) => match clauses.iter().find(|(name, arity, guards, _)| {
                (*name, *arity) == (hd, n) && guards_match(guards, &args) == Some(true)
            }) {
                Some((_, _, _, body)) => {
                    let mut bindings = vec![];
                    for (hd, mut bargs) in body.clone() {
                        for a in bargs.iter_mut() {
                            // bind local arguments
                            if let V::X(x) = *a {
                                *a = args[x].clone();
                            }
                            // bind new globals
                            bind_yx(&mut globals, &mut bindings, a);
                        }
                        procs.push_front((hd, bargs));
                    }
                    Some(true)
                }
                None => None,
            },
        };
        match res {
            Some(true) => {}
            Some(false) => {
                eprintln!("unsatisfiable");
                return;
            }
            None => procs.push_front((hd, args)),
        }
    }

    for (y, x) in init_bindings {
        print!("{y} = {:?}, ", globals[x]);
    }
    for (hd, args) in init {
        print!("{:?}, ", V::E(hd, args));
    }
    println!();
}
