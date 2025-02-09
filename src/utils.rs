use core::ptr;

impl<T> Extract<T> for Vec<T> {
    fn extract<F>(&mut self, f: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        let mut deleted = 0;
        let mut v = Vec::with_capacity(self.len() / 2);
        let len = self.len();

        unsafe {
            for i in 0..len {
                let src = self.as_mut_ptr().add(i);
                if f(&self[i]) {
                    v.push(src.read());
                    deleted += 1;
                } else {
                    let dst = self.as_mut_ptr().add(i - deleted);
                    ptr::copy(src, dst, 1);
                }
            }
            self.set_len(len - deleted);
        }
        v
    }
}

pub trait Extract<T> {
    fn extract<F>(&mut self, f: F) -> Self
    where
        F: Fn(&T) -> bool;
}

impl<T> RetainFrom<T> for Vec<T> {
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

impl<T> Ascend for Vec<T>
where
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

impl<T> Descend for Vec<T>
where
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
