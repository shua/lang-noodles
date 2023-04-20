use std::fmt::Display;

use crate::{EOp1, EOp2, EOpi, EOpn, Env, EnvBind, St, Ty, E};

pub(crate) fn disp_list<I: Display, Sep: Display>(
    f: &mut std::fmt::Formatter<'_>,
    sep: Sep,
    items: &[I],
) -> std::fmt::Result {
    if items.is_empty() {
        return Ok(());
    }
    write!(f, "{}", items[0])?;
    for i in &items[1..] {
        write!(f, "{sep}{i}")?;
    }
    Ok(())
}

impl Display for E {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let p = self.precedence();
        match self {
            E::Val(v) => todo!(),
            E::Var(s) => write!(f, "{s}"),
            E::Next(s) => write!(f, "{s}'"),
            E::Op1(op, e0) => op.display(f, p, e0),
            E::Op2(op, e0, e1) => op.display(f, p, e0, e1),
            E::Opn(op, e0, en) => op.display(f, p, e0, en),
            E::Set(es) => {
                write!(f, "{{")?;
                disp_list(f, ", ", es)?;
                write!(f, "}}")
            }
            E::Tup(es) => {
                write!(f, "<<")?;
                disp_list(f, ", ", es)?;
                write!(f, ">>")
            }
            E::Iter(op, kes, body) => op.display(kes, body, f),
            E::Except(e0, i, e) => write!(f, "[{e0} EXCEPT ![{i}] = {e}]"),
        }
    }
}

impl EOp1 {
    fn display(&self, f: &mut std::fmt::Formatter, p: f64, e: &E) -> std::fmt::Result {
        let mut disp_prefix = |pre| {
            write!(f, "{pre}")?;
            if e.precedence() < p {
                write!(f, "({e})")
            } else {
                write!(f, "{e}")
            }
        };
        match self {
            EOp1::Subset => disp_prefix("SUBSET "),
            EOp1::Union => disp_prefix("UNION "),
            EOp1::Unchanged => disp_prefix("UNCHANGED "),
            EOp1::Enabled => disp_prefix("ENABLED "),
            EOp1::Ever => disp_prefix("[]"),
            EOp1::Anon => disp_prefix("<>"),
        }
    }
}
impl Display for EOp2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            EOp2::In => "e1 \\in e2",
            EOp2::Subset => "e1 \\subseteq e2",
            EOp2::Arrow => "[e1 -> e2]",
            EOp2::Apply => "e1[e2]",
            EOp2::Eq => "e1 = e2",
            EOp2::Neq => "e1 # e2",
            EOp2::Union => "e1 \\cup e2",
            EOp2::Isect => "e1 \\cap e2",
            EOp2::SetSub => "e1 \\ e2",
            EOp2::Imply => "e1 => e2",
            EOp2::TImply => "e1 ~> e2",
            EOp2::TStep => "[e2]_e1",
            EOp2::WFair => "WF_e1(e2)",
            EOp2::SFair => "SF_e1(e2)",
        })
    }
}
impl EOp2 {
    fn display(&self, f: &mut std::fmt::Formatter, p: f64, e0: &E, e1: &E) -> std::fmt::Result {
        let mut disp_infix = |sep| {
            if e0.precedence() <= p {
                write!(f, "({e0})")?;
            } else {
                write!(f, "{e0}")?;
            }
            write!(f, "{sep}")?;
            if e1.precedence() < p {
                write!(f, "({e1})")
            } else {
                write!(f, "{e1}")
            }
        };

        match self {
            EOp2::In => disp_infix(" \\in "),
            EOp2::Subset => disp_infix(" \\subseteq "),
            EOp2::SetSub => disp_infix(" \\ "),
            EOp2::Arrow => write!(f, "[{e0} -> {e1}]"),
            EOp2::Apply => write!(f, "{e0}[{e1}]"),
            EOp2::Eq => disp_infix(" = "),
            EOp2::Neq => disp_infix(" # "),
            EOp2::Union => disp_infix(" \\cup "),
            EOp2::Isect => disp_infix(" \\cap "),
            EOp2::Imply => disp_infix(" => "),
            EOp2::TImply => disp_infix(" ~> "),
            EOp2::TStep => write!(f, "[{e1}]_{e0}"),
            EOp2::WFair => write!(f, "WF_{e0}({e1})"),
            EOp2::SFair => write!(f, "SF_{e0}({e1})"),
        }
    }
}
impl Display for EOpn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            EOpn::And => "e1 /\\ e2",
            EOpn::Or => "e1 \\/ e2",
            EOpn::Call => "Name(args...)",
        })
    }
}
impl EOpn {
    fn display(&self, f: &mut std::fmt::Formatter, p: f64, e0: &E, en: &[E]) -> std::fmt::Result {
        match self {
            EOpn::And => {
                write!(f, "{e0}")?;
                for e in en {
                    write!(f, " /\\ {e}")?;
                }
                Ok(())
            }
            EOpn::Or => {
                write!(f, "{e0}")?;
                for e in en {
                    write!(f, " \\/ {e}")?;
                }
                Ok(())
            }
            EOpn::Call => {
                write!(f, "{e0}(")?;
                disp_list(f, ", ", en)?;
                write!(f, ")")
            }
        }
    }
}
impl EOpi {
    fn display(
        &self,
        kes: &[(Vec<String>, E)],
        body: &E,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        fn dkes(kes: &[(Vec<String>, E)], f: &mut std::fmt::Formatter) -> std::fmt::Result {
            if kes.is_empty() {
                return Ok(());
            }
            disp_list(f, ", ", &kes[0].0)?;
            write!(f, " \\in {}", kes[0].1)?;
            for (k, e) in &kes[1..] {
                write!(f, ", ")?;
                disp_list(f, ", ", k)?;
                write!(f, " \\in {e}")?;
            }
            Ok(())
        }
        match self {
            EOpi::All => {
                write!(f, "\\A ")?;
                dkes(kes, f)?;
                write!(f, ": {body}")
            }
            EOpi::Any => {
                write!(f, "\\E ")?;
                dkes(kes, f)?;
                write!(f, ": {body}")
            }
            EOpi::Choose => {
                write!(f, "CHOOSE ")?;
                dkes(kes, f)?;
                write!(f, ": {body}")
            }
            EOpi::Set => {
                write!(f, "{{{body} : ")?;
                dkes(kes, f)?;
                write!(f, "}}")
            }
            EOpi::Map => {
                write!(f, "[")?;
                dkes(kes, f)?;
                write!(f, " |-> {body}]")
            }
            EOpi::Let => {
                write!(f, "LET {} = {}", kes[0].0[0], kes[0].1)?;
                for (k, v) in &kes[1..] {
                    write!(f, ", {} = {v}", k[0])?;
                }
                write!(f, "IN {body}")
            }
            EOpi::Filter => {
                write!(f, "{{")?;
                dkes(kes, f)?;
                write!(f, " : {body}}}")
            }
        }
    }
}

impl Display for St {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            St::Extends(ms) => {
                write!(f, "EXTENDS ")?;
                disp_list(f, ", ", ms)
            }
            St::Constants(cs) => {
                write!(f, "CONSTANTS ")?;
                disp_list(f, ", ", cs)
            }
            St::Variables(vs) => {
                write!(f, "VARIABLES ")?;
                disp_list(f, ", ", vs)
            }
            St::Assume(e) => write!(f, "ASSUME {e}"),
            St::Def(name, args, body) if args.is_empty() => write!(f, "{name} == {body}"),
            St::Def(name, args, body) => {
                write!(f, "{name}(")?;
                disp_list(f, ", ", args)?;
                write!(f, ") == {body}")
            }
            St::Theorem(e) => write!(f, "THEOREM {e}"),
        }
    }
}

impl Env {
    fn display(&self, f: &mut std::fmt::Formatter, first: &mut bool) -> std::fmt::Result {
        fn dbind(
            f: &mut std::fmt::Formatter,
            name: &str,
            args: &[String],
            val: &E,
        ) -> std::fmt::Result {
            if args.is_empty() {
                write!(f, "{name} = {val}")
            } else {
                write!(f, "{name}(")?;
                disp_list(f, ", ", args)?;
                write!(f, ")")
            }
        }
        match &*self.0 {
            EnvBind::Root(bs) if bs.is_empty() => Ok(()),
            EnvBind::Root(bs) => {
                *first = false;
                dbind(f, &bs[0].0, &bs[0].1, &bs[0].2)?;
                for (n, a, v) in &bs[1..] {
                    write!(f, ", ")?;
                    dbind(f, n, a, v)?;
                }
                Ok(())
            }
            EnvBind::Bind(parent, bs) => {
                if !*first {
                    write!(f, ", ")?;
                }
                *first = false;
                dbind(f, &bs[0].0, &[], &E::Val(bs[0].1.clone()))?;
                for (n, v) in &bs[1..] {
                    write!(f, ", ")?;
                    dbind(f, n, &[], &E::Val(v.clone()))?;
                }
                Ok(())
            }
        }
    }
}
impl Display for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let first = &mut true;
        self.display(f, first)?;
        if *first {
            write!(f, "{{}}")?;
        }
        Ok(())
    }
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Any => f.write_str("any"),
            Ty::Atom => f.write_str("atom"),
            Ty::Bool => f.write_str("bool"),
            Ty::Nat => f.write_str("nat"),
            Ty::Temp => f.write_str("temp"),
            Ty::Map(t1, t2) => write!(f, "[t1 -> t2]"),
            Ty::Set(t) => write!(f, "{{{t}}}"),
        }
    }
}
