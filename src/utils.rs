use core::alloc::Allocator;
use core::ptr::{copy, drop_in_place};

impl<T, A: Allocator> ExtractIn<T> for Vec<T, A> {
    fn extract_in<F>(&mut self, other: &mut Self, f: F)
    where
        F: Fn(&T) -> bool,
    {
        let mut deleted = 0;
        let mut consequtives = 0;
        let len = self.len();

        unsafe {
            let mut i = 0;
            while i < len && !f(&self[i]) {
                i += 1;
            }
            for j in i..len {
                if !f(&self[j]) {
                    consequtives += 1;
                } else {
                    if consequtives != 0 {
                        let from = j - consequtives;
                        let src = self.as_ptr().add(from);
                        let dst = self.as_mut_ptr().add(from - deleted);
                        copy(src, dst, consequtives);
                        consequtives = 0;
                    }
                    let cpy = self.as_ptr().add(j).read();
                    other.push(cpy);
                    deleted += 1;
                }
            }

            if deleted != 0 && consequtives != 0 {
                let from = len - consequtives;
                let src = self.as_ptr().add(from);
                let dst = self.as_mut_ptr().add(from - deleted);
                copy(src, dst, consequtives);
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
        let mut consequtives = 0;
        let len = self.len();

        unsafe {
            let mut i = start;
            while i < len && f(&self[i]) {
                i += 1;
            }
            for j in i..len {
                if f(&self[j]) {
                    consequtives += 1;
                } else {
                    if consequtives != 0 {
                        let from = j - consequtives;
                        let src = self.as_ptr().add(from);
                        let dst = self.as_mut_ptr().add(from - deleted);
                        copy(src, dst, consequtives);
                        consequtives = 0;
                    }
                    drop_in_place(self.as_mut_ptr().add(j));
                    deleted += 1;
                }
            }

            if deleted != 0 && consequtives != 0 {
                let from = len - consequtives;
                let src = self.as_ptr().add(from);
                let dst = self.as_mut_ptr().add(from - deleted);
                copy(src, dst, consequtives);
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
    fn descend(&mut self, k: usize) -> usize;
}
