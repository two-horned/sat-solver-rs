use core::alloc::Allocator;
use core::ptr::NonNull;
use std::alloc::Layout;

const MASK: usize = usize::BITS as usize - 1;
const POWR: usize = MASK.trailing_ones() as usize;

const fn indices(index: usize) -> (usize, usize) {
    (index >> POWR, index & MASK)
}

const fn integers_needed(bits: usize) -> usize {
    bits + MASK >> POWR
}

macro_rules! impl_mut_row_col_access {
    ($func_name:ident) => {
        pub(crate) fn $func_name(&mut self, row: usize, col: usize) {
            assert!(row < self.row_count, "Row is out of bound.");
            assert!(col < self.col_count, "Col is out of bound.");

            let (mut i, j) = indices(col);
            i += row * integers_needed(self.col_capac);

            let num = unsafe { self.rc_memory.unwrap().add(i).as_mut() };
            num.$func_name(j);

            let s = self.integers_needed_rows();
            let (mut i, j) = indices(row);
            i += s + col * integers_needed(self.row_capac);

            let num = unsafe { self.rc_memory.unwrap().add(i).as_mut() };
            num.$func_name(j);
        }
    };
}

impl<A: Allocator> BitMatrix<A> {
    pub(crate) fn new_in(a: A) -> Self {
        Self {
            allocator: a,
            row_count: 0,
            col_count: 0,
            row_capac: 0,
            col_capac: 0,
            rc_memory: None,
        }
    }

    pub(crate) fn with_capacity_in(row_capac: usize, col_capac: usize, a: A) -> Self {
        let mut tmp = Self::new_in(a);
        tmp.row_capac = row_capac;
        tmp.col_capac = col_capac;
        tmp.rc_memory = Some(tmp.allocate());

        tmp
    }

    pub(crate) fn read(&self, row: usize, col: usize) -> bool {
        assert!(row < self.row_count, "Row is out of bound.");
        assert!(col < self.col_count, "Col is out of bound.");

        let (mut i, j) = indices(col);
        i += row * integers_needed(self.col_capac);

        let num = *unsafe { self.rc_memory.unwrap().add(i).as_ref() };
        let res = num.read(j);
        debug_assert_eq!(res, self.read_alt(row, col), "Data inconsistency.");
        res
    }

    fn read_alt(&self, row: usize, col: usize) -> bool {
        assert!(row < self.row_count, "Row is out of bound.");
        assert!(col < self.col_count, "Col is out of bound.");

        let s = self.integers_needed_rows();
        let (mut i, j) = indices(row);
        i += s + col * integers_needed(self.row_capac);

        let num = *unsafe { self.rc_memory.unwrap().add(i).as_ref() };
        num.read(j)
    }

    pub(crate) fn write(&mut self, row: usize, col: usize, value: bool) {
        if value {
            self.set(row, col);
        } else {
            self.unset(row, col);
        }
    }

    impl_mut_row_col_access!(set);
    impl_mut_row_col_access!(unset);
    impl_mut_row_col_access!(flip);

    pub(crate) fn push_empty_row(&mut self) {
        self.row_count += 1;

        if self.row_count <= self.row_capac - (self.row_capac >> 2) {
            return;
        }

        if let Some(old_ptr) = self.rc_memory {
            let old_layout = self.layout();
            let old_capac = integers_needed(self.row_capac);
            let old_size = self.integers_needed_rows();

            self.row_capac = (self.row_capac << 1) + 1;
            let new_ptr = self.allocate();
            let new_capac = integers_needed(self.row_capac);
            let new_size = self.integers_needed_rows();

            unsafe {
                old_ptr.copy_to(new_ptr, old_size);
                {
                    let old_ptr = old_ptr.add(old_size);
                    let new_ptr = new_ptr.add(new_size);
                    for i in 0..self.col_count {
                        old_ptr
                            .add(i * old_capac)
                            .copy_to(new_ptr.add(i * new_capac), old_capac);
                    }
                }

                self.allocator.deallocate(old_ptr.cast(), old_layout);
            }
            self.rc_memory = Some(new_ptr);
        } else {
            self.row_capac = (self.row_capac << 1) + 1;
            if self.col_capac == 0 {
                return;
            }
            self.rc_memory = Some(self.allocate());
        }
    }

    pub(crate) fn push_empty_col(&mut self) {
        self.col_count += 1;

        if self.col_count <= self.col_capac - (self.col_capac >> 2) {
            return;
        }

        if let Some(old_ptr) = self.rc_memory {
            let old_layout = self.layout();
            let old_capac = integers_needed(self.col_capac);
            let old_size_r = self.integers_needed_rows();
            let old_size_c = self.integers_needed_cols();

            self.col_capac = (self.col_capac << 1) + 1;
            let new_ptr = self.allocate();
            let new_capac = integers_needed(self.col_capac);
            let new_size_r = self.integers_needed_rows();
            unsafe {
                old_ptr
                    .add(old_size_r)
                    .copy_to(new_ptr.add(new_size_r), old_size_c);
                for i in 0..self.row_count {
                    old_ptr
                        .add(i * old_capac)
                        .copy_to(new_ptr.add(i * new_capac), old_capac);
                }

                self.allocator.deallocate(old_ptr.cast(), old_layout);
            }
            self.rc_memory = Some(new_ptr);
        } else {
            self.col_capac = (self.col_capac << 1) + 1;
            if self.row_capac != 0 {
                self.rc_memory = Some(self.allocate());
            }
        }
    }

    pub(crate) fn swap_remove_row(&mut self, row: usize) {
        assert!(row <= self.row_count);
        self.row_count -= 1;
        if let Some(ptr) = self.rc_memory {
            unsafe {
                let n = integers_needed(self.col_capac);
                ptr.add(n * self.row_count).copy_to(ptr.add(n * row), n);

                let ptr = ptr.add(self.integers_needed_rows());
                let n = integers_needed(self.row_capac);

                let (a, b) = indices(row);
                let (x, y) = indices(self.row_count);
                for i in 0..self.col_count {
                    let tow = ptr.add(i * n + a).as_mut();
                    let tor = ptr.add(i * n + x).as_mut();
                    tow.write(b, tor.read(y));
                }
            }
        }
    }

    pub(crate) fn swap_remove_col(&mut self, col: usize) {
        assert!(col <= self.col_count);
        self.col_count -= 1;
        if let Some(ptr) = self.rc_memory {
            unsafe {
                {
                    let ptr = ptr.add(self.integers_needed_rows());
                    let n = integers_needed(self.row_capac);
                    ptr.add(n * self.col_count).copy_to(ptr.add(n * col), n);
                }

                let n = integers_needed(self.col_capac);
                let (a, b) = indices(col);
                let (x, y) = indices(self.col_count);
                for i in 0..self.row_count {
                    let tow = ptr.add(i * n + a).as_mut();
                    let tor = ptr.add(i * n + x).as_mut();
                    tow.write(b, tor.read(y));
                }
            }
        }
    }

    const fn integers_needed(&self) -> usize {
        self.integers_needed_rows() + self.integers_needed_cols()
    }

    const fn integers_needed_rows(&self) -> usize {
        self.row_capac * integers_needed(self.col_capac)
    }

    const fn integers_needed_cols(&self) -> usize {
        self.col_capac * integers_needed(self.row_capac)
    }

    fn layout(&self) -> Layout {
        let (layout, _) = Layout::new::<usize>()
            .repeat(self.integers_needed())
            .expect("Arithmetic overflow on layout creation.");
        layout
    }

    fn allocate(&self) -> NonNull<usize> {
        let layout = self.layout();
        self.allocator
            .allocate_zeroed(layout)
            .expect("Allocation failed.")
            .cast()
    }
}

impl<A: Allocator> Drop for BitMatrix<A> {
    fn drop(&mut self) {
        if let Some(ptr) = self.rc_memory {
            unsafe { self.allocator.deallocate(ptr.cast(), self.layout()) }
        }
    }
}

fn content_to_str<A: Allocator>(bm: &BitMatrix<A>) -> String {
    if bm.col_count == 0 {
        return "<>".to_owned();
    }

    (0..bm.row_count)
        .flat_map(|r| {
            (0..bm.col_count)
                .map(move |c| if bm.read(r, c) { '1' } else { '0' })
                .chain(Some('\n'))
        })
        .collect()
}

impl<A: Allocator> std::fmt::Display for BitMatrix<A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("BitMatrix\n")?;
        f.write_str(&content_to_str(self))
    }
}

impl<A: Allocator> std::fmt::Debug for BitMatrix<A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!(
            "BitMatrix . [counts](rows {})-(cols {}) . [capac](rows {})-(cols {})\n",
            self.row_count, self.col_count, self.row_capac, self.col_capac
        ))?;
        f.write_str(&content_to_str(self))
    }
}

pub(crate) struct BitMatrix<A: Allocator> {
    allocator: A,
    row_count: usize,
    col_count: usize,
    row_capac: usize,
    col_capac: usize,
    rc_memory: Option<NonNull<usize>>,
}

macro_rules! impl_bit_manipulation {
    ($integer:ty) => {
        impl Bits for $integer {
            fn read(&self, i: usize) -> bool {
                self >> i & 1 != 0
            }
            fn write(&mut self, i: usize, value: bool) {
                if value {
                    self.set(i);
                } else {
                    self.unset(i);
                }
            }
            fn set(&mut self, i: usize) {
                *self |= 1 << i;
            }
            fn unset(&mut self, i: usize) {
                *self &= !(1 << i);
            }
            fn flip(&mut self, i: usize) {
                *self ^= 1 << i;
            }
        }
    };
}

trait Bits {
    fn read(&self, i: usize) -> bool;
    fn write(&mut self, i: usize, value: bool);
    fn set(&mut self, i: usize);
    fn unset(&mut self, i: usize);
    fn flip(&mut self, i: usize);
}

impl_bit_manipulation!(usize);
