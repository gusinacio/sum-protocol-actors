use std::{
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops::Deref,
};

struct Polynomial<T, const SIZE: usize>(PhantomData<T>);

impl<T, const SIZE: usize> Polynomial<T, SIZE> {
    pub fn call(&self, _val: &[T]) -> T {
        todo!()
    }
}

impl<T> Deref for Polynomial<T, 1>
where
    T: 'static,
{
    type Target = dyn Fn(T) -> T;

    fn deref(&self) -> &Self::Target {
        let uninit_callable = MaybeUninit::<Self>::uninit();
        let uninit_closure =
            move |arg: T| Self::call(unsafe { &*uninit_callable.as_ptr() }, &[arg]);
        let size_of_closure = mem::size_of_val(&uninit_closure);
        fn second<'a, T>(_a: &T, b: &'a T) -> &'a T {
            b
        }
        let reference_to_closure = second(&uninit_closure, unsafe { mem::transmute(self) });
        mem::forget(uninit_closure);
        assert_eq!(size_of_closure, mem::size_of::<Self>());

        (reference_to_closure as &dyn Fn(T) -> T) as _
    }
}

impl<T> Deref for Polynomial<T, 4>
where
    T: 'static,
{
    type Target = dyn Fn(T, T, T, T) -> T;

    fn deref(&self) -> &Self::Target {
        let uninit_callable = MaybeUninit::<Self>::uninit();
        let uninit_closure = move |arg: T, arg2: T, arg3: T, arg4: T| {
            Self::call(
                unsafe { &*uninit_callable.as_ptr() },
                &[arg, arg2, arg3, arg4],
            )
        };
        let size_of_closure = mem::size_of_val(&uninit_closure);
        fn second<'a, T>(_a: &T, b: &'a T) -> &'a T {
            b
        }
        let reference_to_closure = second(&uninit_closure, unsafe { mem::transmute(self) });
        mem::forget(uninit_closure);
        assert_eq!(size_of_closure, mem::size_of::<Self>());

        (reference_to_closure as &dyn Fn(T, T, T, T) -> T) as _
    }
}

macro_rules! polynomial {
    ($a:expr) => {
        // SparsePolynomial::default()
        Polynomial::<u32, 4>(PhantomData)
    };
}

#[cfg(test)]
mod test {
    use std::marker::PhantomData;

    use super::Polynomial;

    #[test]
    fn my_test() {
        let g = polynomial! { (1 - x1) * x2 * ((x3 + x4) - (x3 * x4)) };

        let x1 = 1;
        let x2 = 2;
        let x3 = 3;
        let x4 = 4;

        let y = g(x1, x2, x3, x4);

        let g2 = Polynomial::<u32, 1>(PhantomData);
        let a = g2(x1);
    }
}
