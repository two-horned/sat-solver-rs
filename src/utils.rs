use core::alloc::Allocator;
use core::cmp::Ordering;
use core::ptr::copy;

impl<T> ExpSearchInsert<T> for [T] {
    type Item = T;

    fn exponential_search_for_insert_by<F>(&self, item: &T, f: F) -> usize
    where
        F: Fn(&Self::Item, &Self::Item) -> Ordering,
    {
        let mut increment;
        let mut lower = 0;
        let mut upper = self.len();
        while lower < upper {
            increment = 1;
            while lower < upper && f(&self[lower], item) == Ordering::Less {
                lower += increment;
                increment <<= 1;
            }
            increment >>= 1;
            if increment == 1 {
                break;
            }
            upper = usize::min(upper, lower);
            lower -= increment;
        }
        lower
    }

    fn exponential_search_for_insert_back_by<F>(&self, item: &T, f: F) -> usize
    where
        F: Fn(&Self::Item, &Self::Item) -> Ordering,
    {
        let mut increment;
        let mut lower = 0 as isize;
        let mut upper = self.len() as isize;
        while lower < upper {
            increment = 1;
            while lower < upper && f(&self[upper as usize - 1], item) == Ordering::Greater {
                upper -= increment;
                increment <<= 1;
            }
            increment >>= 1;
            if increment == 1 {
                break;
            }
            lower = isize::max(lower, upper);
            upper += increment;
        }
        upper as usize
    }
}

trait ExpSearchInsert<T> {
    type Item;
    fn exponential_search_for_insert_by<F>(&self, item: &T, f: F) -> usize
    where
        F: Fn(&Self::Item, &Self::Item) -> Ordering;
    fn exponential_search_for_insert_back_by<F>(&self, item: &T, f: F) -> usize
    where
        F: Fn(&Self::Item, &Self::Item) -> Ordering;
}

impl<T, A> Ascent for Vec<T, A>
where
    A: Allocator,
{
    type Item = T;

    fn ascend_by<F>(&mut self, k: usize, f: F) -> usize
    where
        F: Fn(&Self::Item, &Self::Item) -> Ordering,
    {
        let idx = {
            let slice = &self[k + 1..];
            k + slice.exponential_search_for_insert_by(&self[k], f)
        };
        if idx != k {
            unsafe {
                let cpy = self.as_ptr().add(k).read();
                let src = self.as_mut_ptr().add(k + 1);
                let dst = self.as_mut_ptr().add(k);
                copy(src, dst, idx - k);
                src.add(idx - k).write(cpy);
            }
        }
        idx
    }
}

pub trait Ascent {
    type Item;
    fn ascend_by<F>(&mut self, k: usize, f: F) -> usize
    where
        F: Fn(&Self::Item, &Self::Item) -> Ordering;

    fn ascend_by_key<F, T>(&mut self, k: usize, f: F) -> usize
    where
        F: Fn(&Self::Item) -> T,
        T: Ord,
    {
        self.ascend_by(k, |x, y| Ord::cmp(&f(x), &f(y)))
    }

    fn ascend(&mut self, k: usize) -> usize
    where
        Self::Item: Ord,
    {
        self.ascend_by(k, Ord::cmp)
    }
}

impl<T, A> Descent for Vec<T, A>
where
    A: Allocator,
{
    type Item = T;

    fn descend_by<F>(&mut self, k: usize, f: F) -> usize
    where
        F: Fn(&Self::Item, &Self::Item) -> Ordering,
    {
        let idx = {
            let slice = &self[..k];
            slice.exponential_search_for_insert_back_by(&self[k], f)
        };
        if idx != k {
            unsafe {
                let cpy = self.as_ptr().add(k).read();
                let src = self.as_mut_ptr().add(idx);
                let dst = self.as_mut_ptr().add(idx + 1);
                copy(src, dst, k - idx);
                src.write(cpy);
            }
        }
        idx
    }
}

pub trait Descent {
    type Item;
    fn descend_by<F>(&mut self, k: usize, f: F) -> usize
    where
        F: Fn(&Self::Item, &Self::Item) -> Ordering;

    fn descend_by_key<F, T>(&mut self, k: usize, f: F) -> usize
    where
        F: Fn(&Self::Item) -> T,
        T: Ord,
    {
        self.descend_by(k, |x, y| Ord::cmp(&f(x), &f(y)))
    }

    fn descend(&mut self, k: usize) -> usize
    where
        Self::Item: Ord,
    {
        self.descend_by(k, Ord::cmp)
    }
}
