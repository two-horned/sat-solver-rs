impl<T> Extract<T> for Vec<T> {
    fn extract<F>(&mut self, f: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        let mut deleted = 0;
        for i in 0..self.len() {
            if f(&self[i]) {
                self.swap(i - deleted, i);
            } else {
                deleted += 1;
            }
        }
        self.split_off(self.len() - deleted)
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
        for i in start..self.len() {
            if f(&self[i]) {
                self.swap(i - deleted, i);
            } else {
                deleted += 1;
            }
        }
        self.truncate(self.len() - deleted);
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
