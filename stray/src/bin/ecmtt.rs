#![allow(unused)]

// messing with https://arxiv.org/abs/1202.0904
// Denotation of syntax and metaprogramming in contextual modal type theory (CMTT)

mod cmtt {
    use std::collections::HashMap;
    #[derive(Default, Clone)]
    struct Map<Val> {
        atoms: HashMap<String, Val>,
        vars: HashMap<String, Val>,
    }

    impl<Val: Clone> Map<Val> {
        fn with(&self, a: &str, t: &Val) -> Self {
            let mut bs = self.atoms.clone();
            bs.insert(a.to_string(), t.clone());
            Map {
                atoms: bs,
                vars: self.vars.clone(),
            }
        }

        fn with_var(&self, a: &str, t: &Val) -> Self {
            let mut bs = self.vars.clone();
            bs.insert(a.to_string(), t.clone());
            Map {
                atoms: self.atoms.clone(),
                vars: bs,
            }
        }
    }

    mod natural {
        use std::collections::HashMap;
        use std::rc::Rc;

        #[derive(Clone, PartialEq)]
        enum Ty {
            B,
            N,
            A(Box<Ty>, Box<Ty>),
            M(Box<Ty>),
        }

        impl std::fmt::Debug for Ty {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    Ty::B => write!(f, "o"),
                    Ty::N => write!(f, "ℕ"),
                    Ty::A(a, b) => write!(f, "({a:?})→{b:?}"),
                    Ty::M(a) => write!(f, "□({a:?})"),
                }
            }
        }

        #[derive(Debug, Clone)]
        enum Term {
            B(bool),
            N(u64),
            Atom(String),
            At(String),
            Abs(String, Box<Ty>, Box<Term>),
            App(Box<Term>, Box<Term>),
            Modal(Box<Term>),
            Let(String, Box<Term>, Box<Term>),
        }

        fn fa(t: &Term) -> Vec<&str> {
            match t {
                Term::B(_) | Term::N(_) | Term::At(_) => vec![],
                Term::Atom(a) => vec![a],
                Term::Abs(a, _t, r) => fa(r).into_iter().filter(|b| a != b).collect(),
                Term::App(r1, r2) => {
                    let mut as1 = fa(r1);
                    let as2 = fa(r2);
                    as1.extend(as2);
                    as1
                }
                Term::Modal(r) => fa(r),
                Term::Let(_, s, r) => {
                    let mut as_s = fa(s);
                    let as_r = fa(r);
                    as_s.extend(as_r);
                    as_s
                }
            }
        }

        fn fu(t: &Term) -> Vec<&str> {
            match t {
                Term::B(_) | Term::N(_) | Term::Atom(_) => todo!(),
                Term::At(x) => vec![x],
                Term::Abs(_a, _t, s) => fu(s),
                Term::App(r, s) => {
                    let mut as_r = fu(r);
                    as_r.extend(fu(s));
                    as_r
                }
                Term::Modal(r) => fu(r),
                Term::Let(x, s, r) => {
                    let mut as_r = fu(r);
                    as_r.into_iter().filter(|b| b != x).chain(fu(s)).collect()
                }
            }
        }

        type Ctx = super::Map<Ty>;

        fn tyck(g: &Ctx, r: &Term, t: &Ty) -> bool {
            match r {
                Term::B(_) => matches!(t, Ty::B),
                Term::N(_) => matches!(t, Ty::N),
                Term::Atom(a) => g.atoms.get(a) == Some(t),
                Term::At(x) => g.vars.get(x) == Some(t),
                Term::Abs(a, t0, r) => match t {
                    Ty::A(t1, t2) => t0 == t1 && tyck(&g.with(a, t0), r, t2),
                    _ => false,
                },
                Term::App(r1, r2) => match tysyn(g, r1) {
                    Ty::A(a, b) if &*b == t => tyck(g, r2, &a),
                    _ => panic!("unable to synthesize type"),
                },
                Term::Modal(r) => match t {
                    Ty::M(t) => tyck(g, r, t) && fa(r).is_empty(),
                    _ => false,
                },
                Term::Let(x, s, r) => {
                    let t_s = tysyn(g, s);
                    if let Ty::M(_) = t_s {
                        tyck(&g.with_var(x, &t_s), r, t)
                    } else {
                        false
                    }
                }
            }
        }

        fn tysyn(g: &Ctx, r: &Term) -> Ty {
            match r {
                Term::B(_) => Ty::B,
                Term::N(_) => Ty::N,
                Term::Atom(a) => g.atoms.get(a).unwrap().clone(),
                Term::At(x) => match g.vars.get(x) {
                    Some(t) => (*t).clone(),
                    _ => panic!("unable to synthesize type"),
                },
                Term::Abs(a, t, r) => {
                    let t2 = tysyn(&g.with(a, t), r);
                    Ty::A(t.clone(), Box::new(t2))
                }
                Term::App(r1, r2) => match tysyn(g, r1) {
                    Ty::A(t1, t2) => {
                        if tyck(g, r2, &t1) {
                            *t2
                        } else {
                            panic!("unable to synthesize type");
                        }
                    }
                    _ => panic!("unable to synthesize type"),
                },
                Term::Modal(r) => Ty::M(Box::new(tysyn(g, r))),
                Term::Let(x, s, r) => match tysyn(g, s) {
                    Ty::M(t_s) => tysyn(&g.with_var(x, &t_s), r),
                    _ => panic!("unable to synthesize type"),
                },
            }
        }

        fn subst_atom(r: &Term, sigma: &HashMap<String, Term>) -> Term {
            match r {
                &Term::B(b) => Term::B(b),
                &Term::N(n) => Term::N(n),
                Term::Atom(a) if sigma.contains_key(a) => sigma.get(a).unwrap().clone(),
                Term::Atom(a) => Term::Atom(a.clone()),
                Term::At(x) => Term::At(x.clone()),
                Term::Abs(a, t, r) => {
                    if sigma.contains_key(a) {
                        let mut b = a.clone();
                        // a -> a'
                        while sigma.contains_key(&b) {
                            b.push('\'');
                        }
                        let sigma1 = HashMap::from([(a.clone(), Term::Atom(b.clone()))]);
                        let r = subst_atom(r, &sigma1);
                        Term::Abs(b, t.clone(), Box::new(subst_atom(&r, sigma)))
                    } else {
                        Term::Abs(a.clone(), t.clone(), Box::new(subst_atom(r, sigma)))
                    }
                }
                Term::App(r, s) => Term::App(
                    Box::new(subst_atom(r, sigma)),
                    Box::new(subst_atom(s, sigma)),
                ),
                Term::Modal(r) => Term::Modal(Box::new(subst_atom(r, sigma))),
                Term::Let(x, s, r) => Term::Let(
                    x.clone(),
                    Box::new(subst_atom(s, sigma)),
                    Box::new(subst_atom(r, sigma)),
                ),
            }
        }

        fn subst_unknown(r: &Term, theta: &HashMap<String, Term>) -> Term {
            match r {
                &Term::B(b) => Term::B(b),
                &Term::N(n) => Term::N(n),
                Term::Atom(a) => Term::Atom(a.clone()),
                Term::At(x) => match theta.get(x) {
                    Some(t) => t.clone(),
                    None => Term::At(x.clone()),
                },
                Term::Abs(a, t, r) => {
                    Term::Abs(a.clone(), t.clone(), Box::new(subst_unknown(r, theta)))
                }
                Term::App(r, s) => Term::App(
                    Box::new(subst_unknown(r, theta)),
                    Box::new(subst_unknown(s, theta)),
                ),
                Term::Modal(r) => Term::Modal(Box::new(subst_unknown(r, theta))),
                Term::Let(x, s, r) => {
                    if theta.contains_key(x) {
                        let mut y = x.clone();
                        while theta.contains_key(&y) {
                            y.push('\'');
                        }
                        let theta1 = HashMap::from([(x.clone(), Term::At(y.clone()))]);
                        let r = subst_unknown(r, &theta1);
                        Term::Let(
                            y,
                            Box::new(subst_unknown(s, theta)),
                            Box::new(subst_unknown(&r, theta)),
                        )
                    } else {
                        Term::Let(
                            x.clone(),
                            Box::new(subst_unknown(s, theta)),
                            Box::new(subst_unknown(r, theta)),
                        )
                    }
                }
            }
        }

        // -- denotational semantics ----------------------------

        #[derive(Clone)]
        enum DSVal {
            B(bool),
            N(u64),
            // (x \in [|A|]  |->  [|r|]_s[a:=x])
            Map(String, Valuation, Box<DSSet>, Box<Term>),
            Pair(Box<Term>, Box<DSVal>),
        }

        impl std::fmt::Debug for DSVal {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    DSVal::B(b) => write!(f, "{}", if *b { "⟙" } else { "⟘" }),
                    DSVal::N(n) => write!(f, "{n:?}"),
                    DSVal::Map(x, _s, t, r) => write!(f, "(x∈{t:?} ↦ [|{r:?}|]_s[x≔{x}])"),
                    DSVal::Pair(r, v) => write!(f, "(□{r:?}, {v:?})"),
                }
            }
        }

        #[derive(Debug, Clone)]
        enum DSSet {
            // {true,false}
            B,
            // {0,1, ...}
            N,
            // [|B|] ^ [|A|]
            Map(Rc<DSSet>, Rc<DSSet>),
            // { r | {} |- r:[]A } \X [|A|]
            Syn(Rc<Ty>, Rc<DSSet>),
        }

        fn tysem(t: &Ty) -> DSSet {
            match t {
                Ty::B => DSSet::B,
                Ty::N => DSSet::N,
                Ty::A(a, b) => DSSet::Map(Rc::new(tysem(a)), Rc::new(tysem(b))),
                Ty::M(t) => DSSet::Syn(Rc::new((**t).clone()), Rc::new(tysem(t))),
            }
        }

        type Valuation = super::Map<DSVal>;

        fn elemof(e: &DSVal, s: &DSSet) -> bool {
            match (e, s) {
                (DSVal::B(_), DSSet::B) => true,
                (DSVal::N(_), DSSet::N) => true,
                _ => false,
            }
        }

        fn valuation_tyck(g: &Ctx, s: &Valuation) -> bool {
            // dom(g) = dom(s)  =>  |dom(g)| = |dom(s)|
            if g.atoms.len() != s.atoms.len() || g.vars.len() != s.vars.len() {
                return false;
            }

            // \A a \in dom(s) . a:A \in g  /\  s(a) \in [|A|]
            for (a, v) in &s.atoms {
                let t = match g.atoms.get(a) {
                    Some(t) => t,
                    None => return false,
                };
                if !elemof(v, &tysem(t)) {
                    return false;
                }
            }

            // \A X \in dom(s) . X:[]A \in g  /\  s(X) \in [| []A |]
            for (x, v) in &s.vars {
                let t = match g.vars.get(x) {
                    Some(t) => t,
                    None => return false,
                };
                if !elemof(v, &tysem(&Ty::M(Box::new(t.clone())))) {
                    return false;
                }
            }

            true
        }

        impl DSVal {
            fn hd(&self) -> Option<Result<DSVal, Term>> {
                match self {
                    // if x \in [|o|] or [|N|] or [|A->B|] then hd(x) = x
                    DSVal::B(_) | DSVal::N(_) | DSVal::Map(_, _, _, _) => Some(Ok(self.clone())),
                    DSVal::Pair(hd, _) => Some(Err((**hd).clone())),
                }
            }

            fn tl(&self) -> Option<DSVal> {
                match self {
                    // if x \in [|o|] or [|N|] or [|A->B|] then tl(x) is undefined
                    DSVal::B(_) | DSVal::N(_) | DSVal::Map(_, _, _, _) => None,
                    //
                    DSVal::Pair(_, tl) => Some((**tl).clone()),
                }
            }
        }

        fn termsem(s: &Valuation, r: &Term) -> Option<DSVal> {
            match r {
                &Term::B(b) => Some(DSVal::B(b)),
                &Term::N(n) => Some(DSVal::N(n)),
                Term::Atom(a) => s.atoms.get(a).cloned(),
                Term::At(x) => s.vars.get(x).and_then(|v| v.tl()),
                Term::Abs(x, t, r) => Some(DSVal::Map(
                    x.clone(),
                    s.clone(),
                    Box::new(tysem(t)),
                    Box::new((**r).clone()),
                )),
                Term::App(r1, r2) => {
                    let v1 = termsem(s, r1)?;
                    let v2 = termsem(s, r2)?;
                    match v1 {
                        DSVal::Map(x, s0, t, r) if elemof(&v2, &t) => {
                            termsem(&s0.with_var(&x, &v2), &r)
                        }
                        _ => None,
                    }
                }
                Term::Modal(r) => {
                    let sx: HashMap<String, Term> = s
                        .vars
                        .iter()
                        .filter_map(|(x, v)| v.hd().and_then(|v| v.err()).map(|v| (x.clone(), v)))
                        .collect();
                    let hd = subst_unknown(r, &sx);
                    let hd = Term::Modal(Box::new(hd));
                    let tl = termsem(s, r)?;
                    Some(DSVal::Pair(Box::new(hd), Box::new(tl)))
                }
                Term::Let(x, r1, r) => {
                    let vs = termsem(s, r1)?;
                    termsem(&s.with_var(x, &vs), r)
                }
            }
        }

        // the examples all use _+_ , _*_ , or pattern matching on nats (0, succ(n))
        // none of which are used or defined in the definitions
        // tried adding, eg Add(_, _) to Term, but it results in having to add
        // cases to everything, down to DSVal.
        //
        // there is something the paper doesn't like about
        //   exp 0         => []\b:N.1
        //   exp (succ(n)) => let X = exp n in [](\b:N.b * (X@ b))
        // and
        //   [|  exp 0  |]_{}
        //     = [|  []\b:N.1  |]_{}
        //     = []\b:N.1 :: [|\b:N.1|]_{}
        //     = []\b:N.1 :: (x \in N |-> [|1|]_{}[b:=x])
        //     = []\b:N.1 :: (x \in N |-> 1)
        //   [|  exp (succ 0)  |]_{}
        //     = [|  let X = exp 0 in [](\b:N.b(X@ b))  |]_{}
        //     = [|  [](\b:N.b*(X@ b))  |]_{}[ X:=[|exp 0|]_{}                ]
        //     = [|  [](\b:N.b*(X@ b))  |]_{}[ X:=([]\b:N.1 :: [|\b:N.1|]_{}) ]
        //     = [](\b:N.b*(X@ b))[X:=[]\b:N.1] :: [|\b:N.b*(X@ b)|]_{}[ X:=[|exp 0|]_{} ]
        //     = [](\b:N.b*((\b:N.1)b)) :: [|\b:N.b*(X@ b)|]_{}[ X:=[|exp 0|]_{} ]
        //     = [](\b:N.b*((\b:N.1)b)) :: (x \in N |-> [|b*(X@ b)|]_{}[X:=[|exp 0|]_{}][b:=x])
        //     = [](\b:N.b*((\b:N.1)b)) :: (x \in N |-> [|b|]_{}[X:=[|exp 0|]_{}][b:=x]
        //                                               *([|X@|]_{}[X:=[|exp 0|]_{}][b:=x] [|b|]_{}[X:=[|exp 0|]_{}][b:=x]))
        //     = [](\b:N.b*((\b:N.1)b)) :: (x \in N |-> x * ((x \in N |-> 1) x))
        //     = [](\b:N.b*((\b:N.1)b)) :: (x \in N |-> x * 1)
        //   [|  exp (succ (succ 0))  |]_{}
        //     = [|  let X = exp (succ 0) in [](\b:N.b*(X@ b))  |]_{}
        //     = [|  [](\b:N.b*(X@ b))  |]_{}[ X:=[|exp(succ 0)|]_{} ]
        //     = [](\b:N.b*(X@ b))[ X:=hd[|exp (succ 0)|]_{} ]
        //       :: [|  \b:N.b*(X@ b)  |]_{}[X:=[|exp (succ 0)|]_{}]
        //     = [](\b:N.b*(X@ b))[ X:=[](\b:N.b*((\b:N.1)b)) ]
        //       :: [|  \b:N.b*(X@ b)  |]_{}[X:=[|exp (succ 0)|]_{}]
        //     = [](\b:N.b*(\b:N.b*((\b:N.1)b)b))
        //       :: (x0 \in N |-> [|b*(X@ b)|]_{}[X:=[|exp (succ 0)|]_{}][b:=x0])
        //     = [](\b:N.b*(\b:N.b*((\b:N.1)b)b))
        //       :: (x0 \in N |-> [|b     |]_{}[X:=[|exp (succ 0)|]_{}][b:=x0]
        //                       *[|(X@ b)|]_{}[X:=[|exp (succ 0)|]_{}][b:=x0])
        //     = [](\b:N.b*(\b:N.b*((\b:N.1)b)b))
        //       :: (x0 \in N |-> x0 *(
        //                          [|X@|]_{}[X:=[|exp (succ 0)|]_{}][b:=x0]
        //                            [|b|]_{}[X:=[|exp (succ 0)|]_{}][b:=x0]))
        //     = [](\b:N.b*(\b:N.b*((\b:N.1)b)b))
        //       :: (x0 \in N |-> x0 * ((x1 \in N |-> x1 * 1) x0))
        //     = [](\b:N.b*(\b:N.b*((\b:N.1)b)b))
        //       :: (x0 \in N |-> x0 * x0 * 1)
        //     = [](\b:N.b*(\b:N.b*((\b:N.1)b)b)) :: (x \in N |-> x*x)
        //
        // I don't understand why we have the syntactical reduction on the left
        // and the set theoretic interpretation on the right
        // > [](1+2) denotes the pair 'The syntax of 1+2, with associated extension 3'
        // > Usually sets of denotations are 'quite large' and sets of syntax are 'quite small'
    } // end natural

    mod contextual {
        use std::collections::HashMap;

        #[derive(Clone, PartialEq)]
        enum Ty {
            // o
            B,
            // N
            N,
            // A -> B
            A(Box<Ty>, Box<Ty>),
            // [A_i]_1..n(A)
            M(Vec<Ty>, Box<Ty>),
        }

        enum Consts {
            False,
            True,
            IsApp(Box<Ty>),
        }
        fn const_type(c: &Consts) -> Ty {
            match c {
                Consts::False | Consts::True => Ty::B,
                Consts::IsApp(t) => Ty::A(Box::new(Ty::M(vec![], (*t).clone())), Box::new(Ty::B)),
            }
        }

        enum Term {
            C(Consts),
            // a
            Atom(String),
            // \a:A.r
            Abs(String, Box<Ty>, Box<Term>),
            // r r
            App(Box<Term>, Box<Term>),
            // [a_i:A_i]r
            Modal(HashMap<String, Ty>, Box<Term>),
            // X@(r_i)_1..n
            Var(String, Vec<Term>),
            // let X = s in r
            Let(String, Box<Term>, Box<Term>),
        }

        type Ctx = super::Map<Ty>;

        fn tyck(g: &Ctx, x: &Term, t: &Ty) -> bool {
            match (x, t) {
                (Term::C(c), t) => const_type(c) == *t,
                (Term::Atom(a), t) => match g.atoms.get(a) {
                    Some(t1) => t1 == t,
                    None => false,
                },
                (Term::Abs(x, t, r), Ty::A(t1, t2)) => t == t1 && tyck(&g.with(x, t), r, t2),
                (Term::App(r1, r2), t2) => {
                    let t = tysyn(g, r1).expect("r1 should have synthesizable type");
                    match t {
                        Ty::A(a, b) => {
                            todo!()
                        }
                        _ => false,
                    }
                }
                (Term::Modal(_, _), _) => todo!(),
                (Term::Var(_, _), _) => todo!(),
                (Term::Let(_, _, _), _) => todo!(),
                _ => false,
            }
        }

        fn tysyn(g: &Ctx, x: &Term) -> Option<Ty> {
            todo!()
        }
    }
}

fn main() {}
