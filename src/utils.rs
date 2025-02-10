use core::alloc::Allocator;
use core::ptr::{copy, drop_in_place};

impl<T, A: Allocator> ExtractIn<T> for Vec<T, A> {
    fn extract_in<F>(&mut self, other: &mut Self, f: F)
    where
        F: Fn(&T) -> bool,
    {
        let mut deleted = 0;
        let len = self.len();

        unsafe {
            for i in 0..len {
                let src = self.as_mut_ptr().add(i);
                if f(&self[i]) {
                    other.push(src.read());
                    deleted += 1;
                } else {
                    let dst = self.as_mut_ptr().add(i - deleted);
                    copy(src, dst, 1);
                }
            }
            self.set_len(len - deleted);
        }
    }
}

pub trait ExtractIn<T> {
    fn extract_in<F>(&mut self, other: &mut Self, f: F)
    where
        F: Fn(&T) -> bool;
}

impl<T, A: Allocator> RetainFrom<T> for Vec<T, A> {
    fn retain_from<F>(&mut self, f: F, start: usize)
    where
        F: Fn(&T) -> bool,
    {
        let mut deleted = 0;
        let len = self.len();

        unsafe {
            for i in start..len {
                let src = self.as_mut_ptr().add(i);
                if f(&self[i]) {
                    let dst = self.as_mut_ptr().add(i - deleted);
                    copy(src, dst, 1);
                } else {
                    drop_in_place(src);
                    deleted += 1;
                }
            }
            self.set_len(len - deleted);
        }
    }
}

pub trait RetainFrom<T> {
    fn retain_from<F>(&mut self, f: F, start: usize)
    where
        F: Fn(&T) -> bool;
}

impl<T: PartialOrd> ExpSearchInsert<T> for [T] {
    fn exponential_search_for_insert(&self, item: &T) -> usize {
        let mut increment;
        let mut lower = 0;
        let mut upper = self.len();

        while lower < upper {
            increment = 1;

            while lower < upper && self[lower] < *item {
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

    fn exponential_search_for_insert_back(&self, item: &T) -> usize {
        let mut increment;
        let mut lower = 0 as isize;
        let mut upper = self.len() as isize;

        while lower < upper {
            increment = 1;

            while lower < upper && self[upper as usize - 1] > *item {
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

trait ExpSearchInsert<T: PartialOrd> {
    fn exponential_search_for_insert(&self, item: &T) -> usize;
    fn exponential_search_for_insert_back(&self, item: &T) -> usize;
}

impl<T, A> Ascent for Vec<T, A>
where
    A: Allocator,
    T: PartialOrd,
{
    fn ascend(&mut self, k: usize) -> usize {
        let idx = {
            let slice = &self[k + 1..];
            k + slice.exponential_search_for_insert(&self[k])
        };

        (k..idx).for_each(|x| self.swap(x, x + 1));
        //assert!(self.is_sorted());
        idx
    }
}

pub trait Ascent {
    fn ascend(&mut self, k: usize) -> usize;
}

impl<T, A> Descent for Vec<T, A>
where
    A: Allocator,
    T: PartialOrd,
{
    fn descend(&mut self, k: usize) -> usize {
        let idx = {
            let slice = &self[..k];
            slice.exponential_search_for_insert_back(&self[k])
        };

        (idx..k).rev().for_each(|x| self.swap(x, x + 1));
        //assert!(self.is_sorted());
        idx
    }
}

pub trait Descent {
    fn descend(&mut self, k: usize) -> usize;
}
