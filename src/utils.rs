use core::ptr;
use std::alloc::Allocator;

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
                    ptr::copy(src, dst, 1);
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
                    ptr::copy(src, dst, 1);
                } else {
                    ptr::drop_in_place(src);
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

impl<T, A> Ascend for Vec<T, A>
where
    A: Allocator,
    T: PartialOrd,
{
    fn ascent(&mut self, mut k: usize) -> usize {
        while k + 1 < self.len() && self[k] > self[k + 1] {
            self.swap(k, k + 1);
            k += 1;
        }
        k
    }
}

pub trait Ascend {
    fn ascent(&mut self, k: usize) -> usize;
}

impl<T, A> Descend for Vec<T, A>
where
    A: Allocator,
    T: PartialOrd,
{
    fn descent(&mut self, mut k: usize) -> usize {
        while k > 0 && self[k - 1] > self[k] {
            self.swap(k - 1, k);
            k -= 1;
        }
        k
    }
}

pub trait Descend {
    fn descent(&mut self, k: usize) -> usize;
}
