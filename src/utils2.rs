use core::ptr::{copy, drop_in_place};
use core::alloc::Allocator;

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

impl<T: PartialOrd> BinSearchInsert<T> for [T] {
    fn binary_search_for_insert(&self, item: &T) -> usize {
        let mut inner = 0;
        let mut outer = self.len();

        while inner != outer {
            let middle = inner + (outer - inner) / 2;
            if self[middle] < *item {
                inner = middle + 1;
            } else {
                outer = middle;
            }
        }
        inner
    }
}

trait BinSearchInsert<T: PartialOrd> {
    fn binary_search_for_insert(&self, item: &T) -> usize;
}

impl<T, A> Ascent for Vec<T, A>
where
    A: Allocator,
    T: PartialOrd,
{
    fn ascend(&mut self, k: usize) -> usize {
        let idx = {
            let slice = &self[k+1..];
            slice.binary_search_for_insert(&self[k])
        };

        unsafe {
            let src = self.as_ptr().add(k + 1);
            let dst = self.as_mut_ptr().add(k);
            let cpy = dst.read();
            copy(src, dst, idx - k - 1);
            self.as_mut_ptr().sub(idx - 1).write(cpy);
        }
        assert!(self.is_sorted());
        idx - 1
    }
}

pub trait Ascent {
    fn ascend(&mut self, k: usize) -> usize;
}

impl<T, A> Descent for Vec<T, A>
where
    A: Allocator,
    T: PartialOrd + std::fmt::Debug,
{
    fn descend(&mut self, k: usize) -> usize {
        let idx = {
            let slice = &self[..k];
            slice.binary_search_for_insert(&self[k])
        };

        unsafe {
            let src = self.as_ptr().add(idx);
            let dst = self.as_mut_ptr().add(idx + 1);
            let cpy = dst.read();
            copy(src, dst, k - idx);
            dst.sub(1).write(cpy);
        }
        assert!(self.is_sorted());
        idx
    }
}

pub trait Descent {
    fn descend(&mut self, k: usize) -> usize;
}
