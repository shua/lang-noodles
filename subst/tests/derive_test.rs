#![allow(dead_code)]
use subst::SubstAny;

#[derive(SubstAny)]
pub(crate) enum E<C> {
    A,
    B(#[subst_skip] usize),
    C { x: C, y: C },
    D(D),
}

#[derive(SubstAny)]
enum C {
    C,
}
impl<T> subst::Subst<T> for C {}

#[derive(SubstAny)]
struct D {
    #[subst_bind]
    d: C,
}

impl<T> subst::Subst<T> for D {}

#[test]
fn test() {
    let _: &dyn SubstAny<u8> = &E::<C>::A;
}
