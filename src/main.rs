#![allow(unused)]

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use lalrpop_util::lalrpop_mod;
use std::fmt::Display;
use std::rc::Rc;

mod disp;

lalrpop_mod!(
    #[allow(clippy::all)]
    parse
);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Val {
    Atom(String),
    Num(i64),

    Set(Vec<Val>),
    Tup(Vec<Val>),

    Unbound,
}

impl Val {
    // powset is not smart, it expands a vec of values to the powerset
    // TODO: either generalized lazy vals or specific Pow variant
    fn powset(set: impl AsRef<[Val]>) -> Val {
        let set = set.as_ref();
        if set.len() > 64 {
            panic!("unable to evaluate powset of >64 elements");
        }

        let mut out = vec![];
        for i in 0..(1 << set.len()) {
            let s: Vec<_> = set
                .iter()
                .enumerate()
                .filter(|(j, _)| ((1 << j) & i) != 0)
                .map(|(_, v)| v.clone())
                .collect();
            out.push(Val::Set(s));
        }
        Val::Set(out)
    }

    fn union<'v>(mut a: Vec<Val>, mut b: Vec<Val>) -> Vec<Val> {
        a.extend(b);
        a.sort();
        a.dedup();
        a
    }

    fn normalize(&mut self) {
        match self {
            Val::Atom(_) => {}
            Val::Num(_) => {}
            Val::Set(s) => {
                for v in s.iter_mut() {
                    v.normalize();
                }
                s.sort();
                s.dedup();
            }
            Val::Tup(vs) => {
                for v in vs {
                    v.normalize();
                }
            }
            Val::Unbound => {}
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum E {
    Val(Val),
    Var(String),
    Next(String),
    Op1(EOp1, Box<E>),
    Op2(EOp2, Box<E>, Box<E>),
    Opn(EOpn, Box<E>, Vec<E>),
    Set(Vec<E>),                               // {e_0, ..e_n}
    Tup(Vec<E>),                               // <<e_0, .. e_n>>
    Iter(EOpi, Vec<(Vec<String>, E)>, Box<E>), // \A c \in e : e
    Except(Box<E>, Box<E>, Box<E>),            // [e_0 EXCEPT ![e_1] = e_2]
}
#[derive(Copy, Clone, Debug, PartialEq)]
enum EOp1 {
    Subset,
    Union,
    Unchanged,
    Enabled,
    Ever, // []e
    Anon, // <>e
}
#[derive(Copy, Clone, Debug, PartialEq)]
enum EOp2 {
    In,     // a \in b
    Subset, // a \subseteq b
    Arrow,  // [a -> b]
    Apply,  // a[b]
    Eq,     // a = b
    Neq,    // a # b

    Union,  // a \cup b
    Isect,  // a \cap b
    SetSub, // a \ b

    Imply, // a => b

    TImply, // a ~> b
    TStep,  // [b]_a
    WFair,  // WF_a(b)
    SFair,  // SF_a(b)
}
#[derive(Copy, Clone, Debug, PartialEq)]
enum EOpn {
    And,  // /\ list
    Or,   // \/ list
    Call, // e_0(e_1, ...e_n)
}
#[derive(Copy, Clone, Debug, PartialEq)]
enum EOpi {
    All,    // \A c \in e_0 : e_1
    Any,    // \E c \in e_0 : e_1
    Choose, // CHOOSE c \in e_0: e_1
    Set,    // {e_1 : c \in e_0}
    Map,    // [c \in e_0 |-> e_1]
    Filter, // {c \in e_0 : e_1}
    Let,    // LET c = e_0 IN e_1
}

impl E {
    fn precedence(&self) -> f64 {
        match self {
            E::Val(_) => f64::MAX,
            E::Var(_) => f64::MAX,
            E::Next(_) => f64::MAX,
            E::Op1(_, _) => 5.0,
            E::Op2(op, _, _) => match op {
                EOp2::Arrow => f64::MAX,
                EOp2::Apply => 5.0,
                EOp2::TStep => f64::MAX,
                EOp2::WFair => f64::MAX,
                EOp2::SFair => f64::MAX,
                _ => 4.0,
            },
            E::Opn(op, _, _) => match op {
                EOpn::Call => f64::MAX,
                _ => 4.0,
            },
            E::Set(_) => f64::MAX,
            E::Tup(_) => f64::MAX,
            E::Iter(op, _, _) => match op {
                EOpi::All => 5.0,
                EOpi::Any => 5.0,
                EOpi::Choose => 5.0,
                EOpi::Set => f64::MAX,
                EOpi::Map => f64::MAX,
                EOpi::Let => 5.0,
                EOpi::Filter => f64::MAX,
            },
            E::Except(_, _, _) => f64::MAX,
        }
    }
}
#[derive(Clone, Debug, PartialEq)]
enum St {
    Extends(Vec<String>),
    Constants(Vec<String>),
    Variables(Vec<String>),
    Assume(E),
    Def(String, Vec<String>, E),
    Theorem(E),
}

fn pparseerr<T>(
    file: (&str, &str),
    res: Result<T, lalrpop_util::ParseError<usize, lalrpop_util::lexer::Token, &str>>,
) -> T {
    let err = match res {
        Ok(v) => return v,
        Err(err) => err,
    };

    let file = codespan_reporting::files::SimpleFile::new(file.0, file.1);
    let mut diag: Diagnostic<_> = Diagnostic::error().with_message(format!("{err}"));
    fn fmt_expected(expected: &[String]) -> String {
        let mut s = "expected one of: ".to_string();
        for (i, exp) in expected.iter().enumerate() {
            if i != 0 {
                s.push_str(", ");
            }
            s.push_str(exp);
        }
        s
    }
    match err {
        lalrpop_util::ParseError::InvalidToken { location } => {
            diag = diag.with_labels(vec![Label::primary((), location..location + 1)])
        }
        lalrpop_util::ParseError::UnrecognizedEOF { location, expected } => {
            diag = diag
                .with_labels(vec![Label::primary((), location..location + 1)])
                .with_notes(vec![fmt_expected(&expected)])
        }
        lalrpop_util::ParseError::UnrecognizedToken { token, expected } => {
            diag = diag
                .with_labels(vec![Label::primary((), token.0..token.2)])
                .with_notes(vec![fmt_expected(&expected)])
        }
        lalrpop_util::ParseError::ExtraToken { token } => {
            diag = diag.with_labels(vec![Label::primary((), token.0..token.2)])
        }
        lalrpop_util::ParseError::User { error } => {}
    }
    let writer = StandardStream::stderr(ColorChoice::Auto);
    let config = codespan_reporting::term::Config::default();
    codespan_reporting::term::emit(&mut writer.lock(), &config, &file, &diag);
    std::process::exit(1);
}

#[derive(PartialEq)]
enum EnvBind<Root, Bind> {
    Root(Root),
    Bind(Rc<EnvBind<Root, Bind>>, Bind),
}
type RootOps = Vec<(String, Vec<String>, E)>;
type Binding<T> = Vec<(String, T)>;
#[derive(Clone, PartialEq)]
struct Env(Rc<EnvBind<RootOps, Binding<Val>>>);

impl EnvBind<RootOps, Binding<Val>> {
    fn lookup(&self, key: impl AsRef<str>) -> Option<(&[String], E)> {
        match self {
            EnvBind::Root(bs) => bs
                .iter()
                .find_map(|(n, a, e)| (n == key.as_ref()).then(|| (a.as_slice(), e.clone()))),
            EnvBind::Bind(parent, bs) => bs
                .iter()
                .find_map(|(n, v)| (n == key.as_ref()).then(|| (&[][..], E::Val(v.clone()))))
                .or_else(|| parent.lookup(key)),
        }
    }
}
impl std::ops::Deref for Env {
    type Target = EnvBind<RootOps, Binding<Val>>;
    fn deref(&self) -> &EnvBind<RootOps, Binding<Val>> {
        &self.0
    }
}
impl Env {
    fn bind(&mut self, key: impl Into<String>, v: impl Into<Val>) {
        let (key, v) = (key.into(), v.into());
        match Rc::get_mut(&mut self.0) {
            // only one instance means we can just update the binding
            Some(EnvBind::Bind(_, bs)) => bs.push((key, v)),
            _ => self.0 = Rc::new(EnvBind::Bind(self.0.clone(), vec![(key, v)])),
        }
    }
}

// map from string to val
struct State(Vec<(String, Val)>);
type Ctx = (State, Env);
type Ctxs = Box<dyn Iterator<Item = (Ctx, Val)>>;

// https://www.hpl.hp.com/techreports/Compaq-DEC/SRC-TN-1997-006A.pdf
//
// F(a0, ..an) is an operator (sort of polymorphic action)
//
// 2 classes of variables: rigid and flexible
// an "action" is a boolean formula that may contain primed and unprimed flexible variables
//   p'           p with every flexible variable x replaced by its primed version x'
//   [A]_e        A \/ (e' = e)   A may occur, or e is unchanged
//   <A>_e        A /\ (e' != e)  A must occur, and e must be changed
//   ENABLED A    Let x1...xn be flex var that occur primed in A, let x1*...xn* be new
//                rigid vars that do not occur in A, and let A* be the formula obtained
//                from A by replacing each occurance of xi' with xi*, for i=1..n.
//                Then ENABLED A equals \E x1*...xn*: A*.
//                For example: ENABLED (x' * x = y' * z) == \E x*,y*: x* * x = y* * z
//   UNCHANGED e  e' = e
//
// Temporal formula is one that is true/false of a behaviour, which is an infinite sequence
// of states. The temporal quantifiers have the same generalizations as the unbounded pred-logic
// quantifiers, for example \EE x1..xn : F
//   <>F      ![]!F
//   WF_e(A)  ([]<>!(ENABLED <A>_e)) \/ ([]<> <A>_e)
//   SF_e(A)  (<>[]!(ENABLED <A>_e)) \/ ([]<> <A>_e)
//   F ~> G   [](F => <>G)
//   \AA x:F  !\EE x: !F
//
//   WF_e(A)  ([]<>!(ENABLED (A /\ (e' != e)))) \/ ([]<> \E e*: A[e*/e'] /\ (e* != e))
//            ([]<>!(\E e*: A[e*/e'] /\ (e* != e))) \/ ([]<> \E e*: A[e*/e1] /\ (e* != e))
//            ([]![]!!(\E ...)) \/ ([]![]! \E ...)
//
// https://en.wikipedia.org/wiki/Temporal_logic defines
// (B U C)(phi) = (\E i: C(phi_i) /\ (\A j < i: B(phi_j)))
//                p _##__  Until: C holds at the current or a future
//                q ___##  position, and B has to hold until that position.
//              pUq _####  At that position, B does not have to hold anymore.
// FB(phi)   'F'uture: B has eventually has to hold
// <>B(phi) = (true U B)(phi)
//          = (\E i: B(phi_i)) /\ (\A j < i: true)
// GB(phi)   'G'lobally: B has to hold on the entire subsequent path
// []B(phi) = !<>!B(phi)
//          = !(\E i: !B(phi_i) /\ \A j < i: true)
//          = !(\E i: !B(phi_i)) \/ !(\A j < i: true)
//          = !(\E i: !B(phi_i)) \/ false
//          = (\A i: !!B(phi_i))
// \A B or \AA B  'A'll: B has to hold on all paths starting from
//                the current state
// (AB)(psi) = (\A phi: phi_0 = psi -> B(phi))
// \E B or \EE B  'E'xists: there exists at least one path starting from
//                the current state where B holds
// (EB)(psi) = (\E phi: phi_0 = psi /\ B(phi))
//
// I think there are
// 1. statements about a state (ie predicate with no primed variables)
// 2. statements about a single step (ie "action" or predicate with primed variables, but no temporal quantifiers)
// 3. statements about behaviour (ie predicate with temporal quantifiers)
//
// computationally (ie for purposes of 'eval'),
// 1. simply need to bind free vars and evaluate
// 2. input is binding for free rigid and free unprimed flex vars and output is constraints on primed flex vars
//    (Var -> Val) -> (Var -> [Eq Val | In Val])
//    (Arg -> Val) -> (State -> Val) -> (State -> [Eq Val | In Val])
//    where Arg is set of arguments to n-Operator
// 3. I'm not sure, I am going to limit at top-level specification
//    so there is no 'eval' only simplify/normalize, and check
//
// t := bool | nat | {t0} | t0 -> t0 | any
// t* := t | temp
//
// ------------- [TVal]
// |- true: bool
//   false: bool
//   0...n: nat
//       x: any
//      x': any
//
// G|- \A i: e_i:t
// ------------------ [TSet]
// G|- {v..}:{t}
//   <<v..>>:nat -> t
//
// G|-e1:{t1}  G,x:t1|-e2:t2
// -------------------------------- [TArrow]
// G|-[x \in e1 |-> e2]: {t1} -> t2
//
// G|-e1:any  G,x:any|-e2:t2
// ------------------------------- [TArrowAny]
// G|-[x \in e1 |-> e2]: any -> t2
//
// G|-e1:t1->t2  G|-e2:t1
// \/ G|-e1:any->t2 G|-e2:t1
// ------------------------- [TApp]
// G|-e1[e2]:t2
//
// G|-e1:t1->t2 G|-e2:any
// \/ G|-e1:any G|-e2:t1
// ---------------------- [TAppAny]
// G|-e1[e2]:any
//
// G|-e1:t1  G|-e2:t2
// ---------------------- [TSetArrow]
// G|-[e1 -> e2]:{t1->t2}
//
// G|-e1:{t1}  G,x:t1|-e2:t2
// \/ G|-e1:any  G,x:any|-e2:t2
// ---------------------------- [TSetMap]
// G|-{e2 : x \in e1}:{t2}
//
// G|-e1:{t1}  G,x:t1|-e2:bool
// \/ G|-e1:{t1}  G,x:t1|-e2:any
// ----------------------------- [TSetFilter]
// G|-{x \in e1: e2}:{t1}
//
// G|-e1:any
// G,x:any|-e2:bool \/ G,x:any|-e2:any
// ----------------------------------- [TSetFilterAny]
// G|-{x \in e1: e2}:{any}
//
// G|-e1:bool \/ G|-e1:any
// G|-e2:bool \/ G|-e2:any
// ----------------------- [TBoolOps]
// G|-e1 /\ e2:bool
//    e1 \/ e2:bool
//    e1 => e2:bool
//    !e1:bool
//
// G|-e1:nat \/ G|-e1:any
// G|-e2:nat \/ G|-e2:any
// ---------------------- [TNatOps]
// G|-e1+e2:nat
//    e1*e2:nat
//    e1-e2:nat
//
// G|-e1:{t1} \/ G|-e1:any
// G|-e2:{t2} \/ G|-e2:any
// ----------------------- [TSetOps]
// G|-e1 \subseteq e2:bool
//    e1 \cap e2:{any}
//    e1 \cup e2:{any}
//
// G|-e1:t \/ G|-e1:any
// G|-e2:{t} \/ G|-e2:any
// ---------------------- [TSetIn]
// G|-e1 \in e2:bool
//
//    G|-e1:{t1}  G,x:t1|-e2:t2
// \/ G|-e1:any  G,x:any|-e2:t2
// ---------------------------- [TBoolAllAny]
// G|-\A x \in e1 . e2:bool
// G|-\E x \in e1 . e2:bool
//
// G|-e1:{t1}
// G,x:t1|-e2:bool \/ G,x:t1|-e2:any
// --------------------------------- [TChoose]
// CHOOSE x \in e1 . e2:t1
//
// G|-e1:any
// G,x:any|-e2:bool \/ G,x:any|-e2:any
// ----------------------------------- [TChooseAny]
// CHOOSE x \in e1 . e2:any
//
// G|-e1:bool \/ G|-e1:any
// G|-e2:t  t # temp
// ----------------------- [TStep]
// G|-[e1]_e2:temp
//    WF_e2(e1):temp
//    SF_e2(e1):temp
//
// G|-e:bool \/ G|-e:any
// --------------------- [TEnabled]
// G|-ENABLED e:temp
//
// G|-e:bool \/ G|-e:any \/ G|-e:temp
// ---------------------------------- [TTemp]
// G|-[]e:temp
//    <>e:temp
//
// G|-e1:temp   G|-e2:temp \/ G|-e2:bool \/ G|-e2:any
// G|-e1:temp \/ G|-e1:bool \/ G|-e1:any   G|-e2:temp
// -------------------------------------------------- [TTempOps]
// G|-e1 /\ e2:temp
//    e1 \/ e2:temp
//    e1 => e2:temp
//
// G|-e:temp
// ---------- [TTempNot]
// G|-!e:temp
//

#[derive(Clone, Debug, PartialEq)]
enum Ty {
    Any,
    Atom,
    Bool,
    Nat,
    Temp,
    Map(Box<Ty>, Box<Ty>),
    Set(Box<Ty>),
}
impl Ty {
    fn superset(self, rhs: Ty) -> Ty {
        match (self, rhs) {
            (t1, t2) if t1 == t2 => t1,
            (Ty::Set(t1), Ty::Set(t2)) => Ty::Set(Box::new(t1.superset(*t2))),
            // as far as I understand, this is not subtyping, we want to know what the *possible* values are
            // given two possible values of s1->t1 and s2->t2.
            // Let's say S->T = {U \in P(S*T) : \A s \in S. \E t \in T. (s,t) \in U}
            // then S->T \subseteq P(S*T) and \A U \in S->T. U \subseteq S*T
            // S->T \cup U->V \subset P(S*T) \cup P(U*V) \subset P(S*T \cup U*V)
            //                \subset P((S \cup U)*(T \cup V))
            (Ty::Map(s1, t1), Ty::Map(s2, t2)) => {
                Ty::Map(Box::new(s1.superset(*s2)), Box::new(t1.superset(*t2)))
            }
            _ => Ty::Any,
        }
    }
}

#[derive(Clone, PartialEq)]
struct TyEnv(Rc<EnvBind<RootOps, Binding<Ty>>>);
impl EnvBind<RootOps, Binding<Ty>> {
    fn lookup(&self, key: impl AsRef<str>) -> Option<&Ty> {
        match self {
            EnvBind::Root(_) => None,
            EnvBind::Bind(parent, bs) => bs
                .iter()
                .find_map(|(n, t)| (n == key.as_ref()).then(|| t))
                .or_else(|| parent.lookup(key)),
        }
    }

    fn op_lookup(&self, key: impl AsRef<str>) -> Option<(&[String], &E)> {
        match self {
            EnvBind::Root(bs) => bs
                .iter()
                .find_map(|(n, a, e)| (n == key.as_ref()).then(|| (a.as_slice(), e))),
            EnvBind::Bind(parent, _) => parent.op_lookup(key),
        }
    }
}
impl std::ops::Deref for TyEnv {
    type Target = EnvBind<RootOps, Binding<Ty>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl TyEnv {
    fn bind(&mut self, key: impl Into<String>, ty: impl Into<Ty>) {
        let b = (key.into(), ty.into());
        if let Some(EnvBind::Bind(_, bs)) = Rc::get_mut(&mut self.0) {
            bs.push(b);
        } else {
            let parent = self.0.clone();
            self.0 = Rc::new(EnvBind::Bind(parent, vec![b]));
        }
    }
}

enum SBind {
    In(bool, Vec<Val>),
}
type StateConstraints = Vec<(String, SBind)>;
impl SBind {
    fn isect_(mut a: Vec<Val>, mut b: &[Val], complement: bool) -> Vec<Val> {
        a.into_iter()
            .filter(move |a| {
                let i = (*b)
                    .iter()
                    .enumerate()
                    .find(|(i, b)| a == *b)
                    .map(|(i, _)| i);
                b = &b[i.unwrap_or(b.len())..];

                complement != i.is_some()
            })
            .collect()
    }

    fn isect(mut a: Vec<Val>, b: &Vec<Val>) -> Vec<Val> {
        Self::isect_(a, b.as_slice(), false)
    }

    fn minus(mut a: Vec<Val>, b: &Vec<Val>) -> Vec<Val> {
        Self::isect_(a, b.as_slice(), true)
    }

    fn new() -> Self {
        // unconstrained
        Self::In(false, vec![])
    }

    fn and(&mut self, rhs: Self) {
        use std::mem::take;
        match (self, rhs) {
            (SBind::In(true, s1), SBind::In(true, s2)) => *s1 = Self::isect(s2, s1),
            (SBind::In(true, s1), SBind::In(false, s2)) => *s1 = Self::minus(take(s1), &s2),
            (SBind::In(b @ false, s1), SBind::In(true, s2)) => {
                (*b, *s1) = (true, Self::minus(s2, s1))
            }
            (SBind::In(false, s1), SBind::In(false, s2)) => *s1 = Val::union(take(s1), s2),
        }
    }

    fn or(&mut self, rhs: Self) {
        use std::mem::take;
        match (self, rhs) {
            (SBind::In(true, s1), SBind::In(true, s2)) => *s1 = Val::union(take(s1), s2),
            (SBind::In(b @ true, s1), SBind::In(false, s2)) => {
                (*b, *s1) = (false, Self::minus(s2, s1))
            }
            (SBind::In(false, s1), SBind::In(true, s2)) => *s1 = Self::minus(take(s1), &s2),
            (SBind::In(b @ false, s1), SBind::In(false, s2)) => {
                (*b, *s1) = (true, Self::isect(s2, s1))
            }
        }
    }

    fn not(&mut self) {
        match self {
            SBind::In(b, _) => *b = !*b,
        }
    }
}

impl E {
    // typeck succeeding does not guarantee correctness, but failure does
    // indicate incorrectness. It's intended as a quick check for known
    // invalid expressions.
    fn typeck(&self, env: TyEnv) -> Result<Ty, String> {
        fn invalid_type<'s, T>(
            ctx: impl Display,
            got_expected: impl AsRef<[(&'s Ty, &'s str)]>,
        ) -> Result<T, String> {
            let mut s = String::new();
            let got_expected = got_expected.as_ref();
            s.push_str("unexpected type for ");
            s.push_str(&format!("{ctx}"));
            s.push_str(": ");
            s.push_str(" expected (");
            for (_, e) in got_expected {
                s.push_str(&format!("{e},"));
            }
            s.push_str(") got (");
            for (t, _) in got_expected {
                s.push_str(&format!("{t},"));
            }
            s.push_str(")");
            Err(s)
        }

        match self {
            E::Val(v) => match v {
                Val::Atom(a) if a == "true" => Ok(Ty::Bool),
                Val::Atom(a) if a == "false" => Ok(Ty::Bool),
                Val::Atom(a) => Ok(Ty::Atom),
                Val::Num(_) => Ok(Ty::Nat),
                Val::Set(_) => Ok(Ty::Set(Box::new(Ty::Any))),
                Val::Tup(_) => Ok(Ty::Map(Box::new(Ty::Nat), Box::new(Ty::Any))),
                Val::Unbound => Ok(Ty::Any),
            },
            E::Var(_) => Ok(Ty::Any),
            E::Next(_) => Ok(Ty::Any),
            E::Op1(op, e) => match (op, e.typeck(env)?) {
                (EOp1::Subset, Ty::Any) => Ok(Ty::Set(Box::new(Ty::Any))),
                (EOp1::Subset, Ty::Set(_)) => Ok(Ty::Set(Box::new(Ty::Any))),
                (EOp1::Subset, t) => invalid_type("SUBSET e", [(&t, "any|set(_)")]),
                (EOp1::Union, Ty::Any) => Ok(Ty::Set(Box::new(Ty::Any))),
                (EOp1::Union, Ty::Set(t)) => Ok(*t),
                (EOp1::Union, t) => invalid_type("UNION e", [(&t, "any|set(_)")]),
                (EOp1::Unchanged, _) => Ok(Ty::Bool),
                (EOp1::Enabled, _) => todo!(),
                (EOp1::Ever, Ty::Any | Ty::Bool | Ty::Temp) => Ok(Ty::Temp),
                (EOp1::Ever, t) => invalid_type("[]e", [(&t, "any|bool|temp")]),
                (EOp1::Anon, Ty::Any | Ty::Bool | Ty::Temp) => Ok(Ty::Temp),
                (EOp1::Anon, t) => invalid_type("<>e", [(&t, "any|bool|temp")]),
            },
            E::Op2(op, e1, e2) => match (op, e1.typeck(env.clone())?, e2.typeck(env)?) {
                (EOp2::In, Ty::Any, Ty::Any | Ty::Set(_)) => Ok(Ty::Bool),
                (EOp2::In, t1, Ty::Set(t2)) if t1 == *t2 => Ok(Ty::Bool),
                (EOp2::In, t1, t2) => {
                    invalid_type("e1 \\in e2", [(&t1, "t1"), (&t2, "any|set(t1)")])
                }
                (EOp2::Subset, Ty::Any | Ty::Set(_), Ty::Any | Ty::Set(_)) => Ok(Ty::Bool),
                (EOp2::SetSub | EOp2::Isect | EOp2::Union, Ty::Set(t1), Ty::Set(t2))
                    if t1 == t2 =>
                {
                    Ok(Ty::Set(t1))
                }
                (
                    EOp2::SetSub | EOp2::Isect | EOp2::Union,
                    Ty::Any | Ty::Set(_),
                    Ty::Any | Ty::Set(_),
                ) => Ok(Ty::Set(Box::new(Ty::Any))),
                (op @ (EOp2::Subset | EOp2::SetSub | EOp2::Isect | EOp2::Union), t1, t2) => {
                    invalid_type(
                        &format!("{}", op),
                        [(&t1, "any|set(_)"), (&t2, "any|set(_)")],
                    )
                }
                (EOp2::Arrow, t1, t2) => Ok(Ty::Set(Box::new(Ty::Map(Box::new(t1), Box::new(t2))))),
                (EOp2::Apply, Ty::Map(t1, t2), t3) if *t1 == t3 || *t1 == Ty::Any => Ok(*t2),
                (EOp2::Apply, Ty::Any, _) => Ok(Ty::Any),
                (EOp2::Apply, t1, t2) => {
                    invalid_type(EOp2::Apply, [(&t1, "[t1 -> t2]|any"), (&t2, "t1")])
                }
                (EOp2::Eq | EOp2::Neq, _, _) => Ok(Ty::Bool),
                (EOp2::Imply, Ty::Bool | Ty::Any, Ty::Bool | Ty::Any) => Ok(Ty::Bool),
                (EOp2::Imply, Ty::Temp, Ty::Temp | Ty::Bool | Ty::Any)
                | (EOp2::Imply, Ty::Temp | Ty::Bool | Ty::Any, Ty::Temp) => Ok(Ty::Temp),
                (EOp2::Imply, t1, t2) => invalid_type(
                    EOp2::Imply,
                    [(&t1, "temp|bool|any"), (&t2, "temp|bool|any")],
                ),
                (EOp2::TImply, Ty::Bool | Ty::Any, Ty::Bool | Ty::Any) => Ok(Ty::Temp),
                (EOp2::TImply, t1, t2) => {
                    invalid_type(EOp2::TImply, [(&t1, "bool|any"), (&t2, "bool|any")])
                }
                (EOp2::TStep | EOp2::WFair | EOp2::SFair, t1, Ty::Bool | Ty::Any)
                    if t1 != Ty::Temp =>
                {
                    Ok(Ty::Temp)
                }
                (op @ (EOp2::TStep | EOp2::WFair | EOp2::SFair), t1, t2) => {
                    invalid_type(op, [(&t1, "bool|nat|set(_)|_->_|any"), (&t2, "bool|any")])
                }
            },
            E::Opn(op, e1, en) => match (op, &**e1, en.iter().map(|e| e.typeck(env.clone()))) {
                (EOpn::And | EOpn::Or, e1, tn) => {
                    tn.fold(e1.typeck(env.clone()), |t1, t2| match (t1?, t2?) {
                        (Ty::Bool | Ty::Any, Ty::Bool | Ty::Any) => Ok(Ty::Bool),
                        (Ty::Temp | Ty::Bool | Ty::Any, Ty::Temp)
                        | (Ty::Temp, Ty::Temp | Ty::Bool | Ty::Any) => Ok(Ty::Temp),
                        (t1, t2) => {
                            invalid_type(op, [(&t1, "temp|bool|any"), (&t2, "temp|bool|any")])
                        }
                    })
                }
                (EOpn::Call, E::Var(name), tn) => {
                    let mut env1 = env.clone();
                    match env.op_lookup(name) {
                        Some((args, body)) => {
                            for (i, t) in tn.enumerate() {
                                env1.bind(&args[i], t?);
                            }
                            body.typeck(env1)
                        }
                        None => Err(format!("operator {name}/{} is not defined", tn.len())),
                    }
                }
                (EOpn::Call, e0, _) => {
                    unreachable!("should not have parsed anything other than string literal: {e0}")
                }
            },
            E::Set(es) => Ok(Ty::Set(Box::new(
                es.iter()
                    .map(|e| e.typeck(env.clone()))
                    .reduce(|a, b| Ok(a?.superset(b?)))
                    .unwrap_or(Ok(Ty::Any))?,
            ))),
            E::Tup(es) => Ok(Ty::Map(
                Box::new(Ty::Nat),
                Box::new(
                    es.iter()
                        .map(|e| e.typeck(env.clone()))
                        .reduce(|a, b| Ok(a?.superset(b?)))
                        .unwrap_or(Ok(Ty::Any))?,
                ),
            )),
            E::Iter(op, bs, e) => match op {
                EOpi::All | EOpi::Any => {
                    let mut env = env;
                    for (ns, e) in bs {
                        let t = e.typeck(env.clone())?;
                        for n in ns {
                            env.bind(n, t.clone());
                        }
                    }
                    match e.typeck(env)? {
                        Ty::Bool | Ty::Any => Ok(Ty::Bool),
                        Ty::Temp => Ok(Ty::Temp),
                        _ => todo!(),
                    }
                }
                EOpi::Choose => {
                    let mut env = env;
                    let (ns, set) = &bs[0];
                    let t = set.typeck(env.clone())?;
                    env.bind(&ns[0], t.clone());
                    match e.typeck(env)? {
                        Ty::Bool | Ty::Any => Ok(t),
                        t => invalid_type("CHOOSE ...: p", [(&t, "bool|any")]),
                    }
                }
                EOpi::Set => {
                    let mut env = env;
                    for (ns, e) in bs {
                        let t = e.typeck(env.clone())?;
                        for n in ns {
                            env.bind(n, t.clone());
                        }
                    }
                    Ok(Ty::Set(Box::new(e.typeck(env)?)))
                }
                EOpi::Map => {
                    let mut env = env;
                    let (ns, set) = &bs[0];
                    let t = set.typeck(env.clone())?;
                    env.bind(&ns[0], t.clone());
                    let s = e.typeck(env)?;
                    Ok(Ty::Map(Box::new(t), Box::new(s)))
                }
                EOpi::Let => {
                    let mut env = env;
                    for (ns, e) in bs {
                        let t = e.typeck(env.clone())?;
                        for n in ns {
                            env.bind(n, t.clone());
                        }
                    }
                    e.typeck(env)
                }
                EOpi::Filter => todo!(),
            },
            E::Except(m, a, e) => match (m.typeck(env.clone())?, a.typeck(env.clone())?) {
                (Ty::Any, _) | (_, Ty::Any) => Ok(Ty::Any),
                (Ty::Map(t1, t2), t3) if *t1 == t3 => Ok(t2.superset(e.typeck(env)?)),
                (m, a) => invalid_type("[e1 EXCEPT ![e2] = _]", [(&m, "t1->t2|any"), (&a, "t1")]),
            },
        }
    }

    fn eval(&self, env: Env) -> Result<Vec<(StateConstraints, Val)>, String> {
        match self {
            E::Val(v) => Ok(vec![(vec![], v.clone())]),
            E::Var(x) => match env.lookup(x) {
                Some((a, e)) if a.is_empty() => e.eval(env.clone()),
                _ => Err(format!("variable {x} not defined")),
            },
            E::Next(x) => Ok(vec![(vec![(x.to_string(), SBind::new())], Val::Unbound)]),
            E::Op1(op, e) => {
                let vs = e
                    .eval(env.clone())?
                    .into_iter()
                    .map(|(cs, v)| match (op, v) {
                        (EOp1::Subset, v) => (cs, Val::powset([v])),
                        (EOp1::Union, Val::Set(vs)) if vs.is_empty() => (cs, Val::Set(vec![])),
                        (EOp1::Union, Val::Set(vs)) => {
                            vs.into_iter().reduce(|a, b| match (a, b) {
                                (Val::Unbound, _) | (_, Val::Unbound) => Val::Unbound,
                                (Val::Set(a), Val::Set(b)) => Val::Set(Val::union(a, b)),
                                _ => todo!(),
                            });
                            todo!()
                        }
                        (EOp1::Union, Val::Unbound) => (cs, Val::Unbound),
                        (EOp1::Union, _) => todo!(),
                        (EOp1::Unchanged, Val::Set(vs) | Val::Tup(vs)) => todo!(),
                        (EOp1::Unchanged, Val::Unbound) => todo!(),
                        (EOp1::Unchanged, Val::Atom(_) | Val::Num(_)) => {
                            (cs, Val::Atom("true".to_string()))
                        }
                        (EOp1::Enabled, Val::Atom(_)) => todo!(),
                        (EOp1::Enabled, Val::Num(_)) => todo!(),
                        (EOp1::Enabled, Val::Set(_)) => todo!(),
                        (EOp1::Enabled, Val::Tup(_)) => todo!(),
                        (EOp1::Enabled, Val::Unbound) => todo!(),
                        (EOp1::Ever, Val::Atom(_)) => todo!(),
                        (EOp1::Ever, Val::Num(_)) => todo!(),
                        (EOp1::Ever, Val::Set(_)) => todo!(),
                        (EOp1::Ever, Val::Tup(_)) => todo!(),
                        (EOp1::Ever, Val::Unbound) => todo!(),
                        (EOp1::Anon, Val::Atom(_)) => todo!(),
                        (EOp1::Anon, Val::Num(_)) => todo!(),
                        (EOp1::Anon, Val::Set(_)) => todo!(),
                        (EOp1::Anon, Val::Tup(_)) => todo!(),
                        (EOp1::Anon, Val::Unbound) => todo!(),
                    })
                    .collect();
                Ok(vs)
            }
            E::Op2(_, _, _) => todo!(),
            E::Opn(_, _, _) => todo!(),
            E::Set(_) => todo!(),
            E::Tup(_) => todo!(),
            E::Iter(_, _, _) => todo!(),
            E::Except(_, _, _) => todo!(),
        }
    }
}

//
//
// e1'Vv1  e2'Vv2
// ------------------
// (e1+e2)' V v1+v2
// (e1*e2)' V v1*v2
// (e1/\e2)' V v1/\v2
//
// big-step is weird when there's a prime state, s'
//
// e1Vv1
// -------------
// (e1+s') V ???
//
// we could just limit s' to only appear in _=e, _#e, _\in e
// e V v
// -------------------
// s'=e V s' \in {v}
// s'#e V s' \nin {v}
//
// e V {v...}
// ------------------------
// s' \in e V s' \in {v...}
//
// e V true
// --------------------
// s' /\ e V s'
// s' \/ e V true
// e => s' V s'
// s' => e V true
//
// e V false
// --------------------
// s' /\ e V false
// s' \/ e V s'
// e => s' V true
// s' => e V !s'
//
// symbolic exec
//
// e1 V s' \in {v...}
// e2 V s' \in {w...}
// ------------------------------------
// e1 /\ e2 V s' \in {v...} \cap {w...}
// e1 \/ e2 V s' \in {v...} \cup {w...}
// !e1 V s' \nin {v...}
// e1 => e2 V s' \nin {v...} \ {w...}
//
// e1 V s' \nin {v...}
// e2 V s' \nin {w...}
// --------------------------------------
// e1 /\ e2 V s' \nin {v...} \cup {w...}
// e1 \/ e2 V s' \nin {v...} \cap {w...}
// !e1 V s' \in {v...}
// e1 => e2 V s' \nin {w...} \ {v...}
//
// e1 V s' \nin {v...}
// e2 V s' \in {w...}
// ----------------------------
// e1 /\ e2 V s' \in {w...} \ {v...}
// e1 \/ e2 V s' \nin {v...} \ {w...}
//
// e V s' \in {v...}
// ----------------------------------
// \E t: []e V \A i > t: s \in {v...}
// \E t: <>e V \E i > t: s \in {v...}
//
// e1 V s' \in {v...}    e2 V s
// --------------------------------
// [e1]_e2 V s' \in {v...} \cup {s}
//

impl E {
    fn map(mut self, f: impl for<'e> Fn(E) -> Result<E, E>) -> E {
        self = match f(self) {
            Ok(e) => return e,
            Err(e) => e,
        };
        match self {
            E::Val(_) | E::Var(_) | E::Next(_) => self.clone(),
            E::Op1(op, e) => E::Op1(op, Box::new(e.map(f))),
            E::Op2(op, e0, e1) => E::Op2(op, Box::new(e0.map(&f)), Box::new(e1.map(f))),
            E::Opn(op, e0, en) => E::Opn(
                op,
                Box::new(e0.map(&f)),
                en.into_iter().map(|e| e.map(&f)).collect(),
            ),
            E::Set(es) => E::Set(es.into_iter().map(|e| e.map(&f)).collect()),
            E::Tup(es) => E::Tup(es.into_iter().map(|e| e.map(&f)).collect()),
            E::Iter(op, binds, e) => E::Iter(
                op,
                binds
                    .into_iter()
                    .map(|(cs, set)| (cs, set.map(&f)))
                    .collect(),
                Box::new(e.map(f)),
            ),
            E::Except(e0, arg, e1) => E::Except(
                Box::new(e0.map(&f)),
                Box::new(arg.map(&f)),
                Box::new(e1.map(f)),
            ),
        }
    }

    fn prime(self) -> E {
        self.map(|e| match e {
            E::Var(v) => Ok(E::Next(v)),
            e => Err(e),
        })
    }
}

fn main() -> Result<(), u16> {
    fn perr<T, E: std::error::Error>(res: Result<T, E>) -> Result<T, u16> {
        match res {
            Ok(v) => Ok(v),
            Err(err) => {
                eprintln!("{err}");
                Err(1)
            }
        }
    }

    let mut args = std::env::args();
    args.next();
    let arg1 = args.next();
    let (fname, src) = match arg1 {
        Some(ref fname) => (fname, perr(std::fs::read_to_string(fname))?),
        None => todo!(),
    };

    let p = parse::TlaParser::new();
    let (rest, ast) = pparseerr((fname, &src), p.parse(&src));

    println!("parsed:");
    for st in &ast {
        println!("{st}");
    }
    println!("rest: {rest}");

    let mut tenv_root = vec![];
    let mut tenv_bind = vec![];
    for st in &ast {
        match st {
            St::Constants(ns) | St::Variables(ns) => {
                tenv_bind.extend(ns.iter().map(|n| (n.clone(), Ty::Any)))
            }
            St::Def(name, args, body) => tenv_root.push((name.clone(), args.clone(), body.clone())),
            _ => {}
        }
    }

    let mut tenv = TyEnv(Rc::new(EnvBind::Root(tenv_root)));
    for b in tenv_bind {
        tenv.bind(b.0, b.1);
    }
    let (args, spec) = tenv.op_lookup("SimpleAllocator").unwrap();
    let (args, spec) = (args.to_vec(), spec.clone());
    for a in args {
        tenv.bind(a, Ty::Any);
    }
    println!("spec: {:?}", spec.typeck(tenv));
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_eparse() {
        let p = super::parse::EParser::new();
        let a = E::Var("a".to_string());
        let b = E::Var("b".to_string());
        assert_eq!(p.parse("a"), Ok(a.clone()));
        assert_eq!(
            p.parse("a /\\ b"),
            Ok(E::Opn(EOpn::And, Box::new(a.clone()), vec![b.clone()]))
        );
        assert_eq!(
            p.parse(r"\A b \in b : \E a \in a : a(b)"),
            Ok(E::Iter(
                EOpi::All,
                vec![(vec!["b".to_string()], b.clone())],
                Box::new(E::Iter(
                    EOpi::Any,
                    vec![(vec!["a".to_string()], a.clone())],
                    Box::new(E::Opn(EOpn::Call, Box::new(a.clone()), vec![b.clone()])),
                ))
            ))
        )
    }

    #[test]
    fn test_tlaparse() {
        let ex = r#"
--- MODULE Foo ---
EXTENDS Nat, Seq \* a comment
CONSTANTS C, A
VARIABLES a, b, c

TypeOK == a \in C
=================
"#;
        let p = parse::TlaParser::new();
        assert_eq!(
            p.parse(ex),
            Ok((
                "Foo".to_string(),
                vec![
                    St::Extends(vec!["Nat".to_string(), "Seq".to_string()]),
                    St::Constants(vec!["C".to_string(), "A".to_string()]),
                    St::Variables(vec!["a".to_string(), "b".to_string(), "c".to_string()]),
                    St::Def(
                        "TypeOK".to_string(),
                        vec![],
                        E::Op2(
                            EOp2::In,
                            Box::new(E::Var("a".to_string())),
                            Box::new(E::Var("C".to_string()))
                        )
                    ),
                ]
            ))
        );
    }
}
