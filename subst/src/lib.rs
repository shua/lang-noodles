pub use subst_derive::SubstAny;

pub trait SubstAny<T> {
    fn subst_any(&mut self, x: usize, v: T);
}

pub trait Subst<T>: SubstAny<T> {
    fn subst(&mut self, x: usize, v: T) {
        self.subst_any(x, v)
    }
}

pub struct Binding<T>(T);

impl<T, X: Subst<T>> SubstAny<T> for Binding<X> {
    fn subst_any(&mut self, x: usize, v: T) {
        self.0.subst(x + 1, v);
    }
}
impl<T, X: Subst<T>> Subst<T> for Binding<X> {}

// convenience impls
impl<T, X: Subst<T>> SubstAny<T> for Box<X> {
    fn subst_any(&mut self, x: usize, v: T) {
        X::subst(&mut **self, x, v)
    }
}
impl<T, X: Subst<T>> Subst<T> for Box<X> {}

impl<T, X: Subst<T>> SubstAny<T> for &mut X {
    fn subst_any(&mut self, x: usize, v: T) {
        X::subst(&mut **self, x, v)
    }
}
impl<T, X: Subst<T>> Subst<T> for &mut X {}

impl<T: Clone, X: Subst<T>> SubstAny<T> for Vec<X> {
    fn subst_any(&mut self, x: usize, v: T) {
        for xx in self {
            xx.subst(x, v.clone());
        }
    }
}
impl<T: Clone, X: Subst<T>> Subst<T> for Vec<X> {}
impl<T: Clone, X: Subst<T>> SubstAny<T> for [X] {
    fn subst_any(&mut self, x: usize, v: T) {
        for xx in self {
            xx.subst(x, v.clone());
        }
    }
}
impl<T: Clone, X: Subst<T>> Subst<T> for [X] {}
impl<T: Clone, X: Subst<T>, const N: usize> SubstAny<T> for [X; N] {
    fn subst_any(&mut self, x: usize, v: T) {
        for xx in self {
            xx.subst(x, v.clone());
        }
    }
}
impl<T: Clone, X: Subst<T>, const N: usize> Subst<T> for [X; N] {}

macro_rules! impl_tup {
    ($($x:ident)*) => {
        impl<T: Clone  $(,$x: Subst<T>)*> SubstAny<T> for ($($x,)*) {
            #[allow(unused)]
            fn subst_any(&mut self, x: usize, v: T) {
                #[allow(non_snake_case)]
                let ($($x,)*) = self;
                $($x.subst(x, v.clone());)*
            }
        }
        impl<T: Clone $(,$x: Subst<T>)*> Subst<T> for ($($x,)*) { }
        impl_tup!{@pop $($x)*}
    };
    (@pop $x0:ident $($x:ident)*) => { impl_tup!{$($x)*} };
    (@pop) => {};
}

impl_tup! { T12 T11 T10 T9 T8 T7 T6 T5 T4 T3 T2 T1 }
