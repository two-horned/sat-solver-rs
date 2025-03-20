use crate::bits::bit_tools::{Bits, indices, integers_needed};

use core::alloc::{Allocator, Layout};
use core::ptr::NonNull;

macro_rules! impl_mut_row_col_access {
    ($func_name:ident) => {
        pub(crate) fn $func_name(&mut self, row: usize, col: usize) {
            assert!(row < self.row_count, "Row is out of bound.");
            assert!(col < self.col_count, "Col is out of bound.");
            debug_assert!(self.is_consistent(), "Data is inconsistent before this func.");

            let (mut i, j) = indices(col);
            i += row * self.integers_needed_each_row();

            let num = unsafe { self.rc_memory.unwrap().add(i).as_mut() };
            num.$func_name(j);

            let s = self.integers_needed_rows();
            let (mut i, j) = indices(row);
            i += s + col * self.integers_needed_each_col();

            let num = unsafe { self.rc_memory.unwrap().add(i).as_mut() };
            num.$func_name(j);
            debug_assert!(self.is_consistent(), "Data is inconsistent after this func.");
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

        if row_capac + col_capac != 0 {
            tmp.rc_memory = Some(tmp.allocate());
        }
        tmp
    }

    pub(crate) const fn allocator(&self) -> &A {
        &self.allocator
    }

    pub(crate) const fn rows(&self) -> usize {
        self.row_count
    }

    pub(crate) const fn cols(&self) -> usize {
        self.col_count
    }

    pub(crate) const fn row_capacity(&self) -> usize {
        self.row_capac
    }

    pub(crate) const fn col_capacity(&self) -> usize {
        self.col_capac
    }

    pub(crate) fn read(&self, row: usize, col: usize) -> bool {
        assert!(row < self.row_count, "Row is out of bound.");
        assert!(col < self.col_count, "Col is out of bound.");

        let (mut i, j) = indices(col);
        i += row * self.integers_needed_each_row();

        let num = *unsafe { self.rc_memory.unwrap().add(i).as_ref() };
        let res = num.read(j);
        res
    }

    fn read_alt(&self, row: usize, col: usize) -> bool {
        assert!(row < self.row_count, "Row is out of bound.");
        assert!(col < self.col_count, "Col is out of bound.");

        let s = self.integers_needed_rows();
        let (mut i, j) = indices(row);
        i += s + col * self.integers_needed_each_col();

        let num = *unsafe { self.rc_memory.unwrap().add(i).as_ref() };
        num.read(j)
    }

    fn is_consistent(&self) -> bool {
        for r in 0..self.row_count {
            for c in 0..self.col_count {
                if self.read(r, c) != self.read_alt(r, c) {
                    return false;
                }
            }
        }
        true
    }

    pub(crate) fn write(&mut self, row: usize, col: usize, value: bool) {
        debug_assert!(self.is_consistent(), "Data is inconsistent before write.");
        if value {
            self.set(row, col);
        } else {
            self.unset(row, col);
        }
        debug_assert!(self.is_consistent(), "Data is inconsistent after write.");
    }

    impl_mut_row_col_access!(set);
    impl_mut_row_col_access!(unset);
    impl_mut_row_col_access!(flip);

    pub(crate) fn row_data(&self, row: usize) -> &[usize] {
        assert!(row < self.row_count);
        if let Some(ptr) = self.rc_memory {
            unsafe {
                let n = self.integers_needed_each_row();
                let u = self.integers_used_each_row();
                return NonNull::slice_from_raw_parts(ptr.add(row * n), u).as_ref();
            }
        }
        &[]
    }

    pub(crate) fn col_data(&self, col: usize) -> &[usize] {
        assert!(col < self.col_count);
        if let Some(ptr) = self.rc_memory {
            unsafe {
                let n = self.integers_needed_each_col();
                let u = self.integers_used_each_col();
                let s = self.integers_needed_rows();
                return NonNull::slice_from_raw_parts(ptr.add(s + col * n), u).as_ref();
            }
        }
        &[]
    }

    pub(crate) fn push_empty_row(&mut self) {
        debug_assert!(self.is_consistent(), "Data is inconsistent before pushing empty row.");
        self.row_count += 1;

        if self.row_count <= self.row_capac {
            return;
        }

        if let Some(old_ptr) = self.rc_memory {
            let old_layout = self.layout();
            let old_capac = self.integers_needed_each_col();
            let old_size = self.integers_needed_rows();

            self.row_capac = (self.row_capac << 1) + 1;
            let new_ptr = self.allocate();
            let new_capac = self.integers_needed_each_col();
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
        debug_assert!(self.is_consistent(), "Data is inconsistent after pushing empty row.");
    }

    pub(crate) fn push_empty_col(&mut self) {
        debug_assert!(self.is_consistent(), "Data is inconsistent before pushing empty col.");
        self.col_count += 1;

        if self.col_count <= self.col_capac {
            return;
        }

        if let Some(old_ptr) = self.rc_memory {
            let old_layout = self.layout();
            let old_capac = self.integers_needed_each_row();
            let old_size_r = self.integers_needed_rows();
            let old_size_c = self.integers_needed_cols();

            self.col_capac = (self.col_capac << 1) + 1;
            let new_ptr = self.allocate();
            let new_capac = self.integers_needed_each_row();
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
        debug_assert!(self.is_consistent(), "Data is inconsistent after pushing empty col.");
    }

    pub(crate) fn swap_remove_row(&mut self, row: usize) {
        assert!(row <= self.row_count);
        debug_assert!(self.is_consistent(), "Data is inconsistent before swap removing row.");
        self.row_count -= 1;
        if let Some(ptr) = self.rc_memory {
            unsafe {
                let n = self.integers_needed_each_row();
                let [s, d] = [self.row_count, row].map(|k| k * n);
                ptr.add(s).copy_to(ptr.add(d), n);
                ptr.add(s).write_bytes(0, size_of::<usize>() * n);

                let ptr = ptr.add(self.integers_needed_rows());
                let n = self.integers_needed_each_col();
                let (a, b) = indices(row);
                let (x, y) = indices(self.row_count);
                for i in 0..self.col_count {
                    let [s, d] = [x, a].map(|k| k + i * n);
                    let value = ptr.add(s).as_ref().read(y);
                    ptr.add(d).as_mut().write(b, value);
                    ptr.add(s).as_mut().unset(y);
                }
            }
        }
        debug_assert!(self.is_consistent(), "Data is inconsistent after swap removing row.");
    }

    pub(crate) fn swap_remove_col(&mut self, col: usize) {
        assert!(col <= self.col_count);
        debug_assert!(self.is_consistent(), "Data is inconsistent before swap removing col.");
        self.col_count -= 1;
        if let Some(ptr) = self.rc_memory {
            unsafe {
                {
                    let ptr = ptr.add(self.integers_needed_rows());
                    let n = self.integers_needed_each_col();
                    let [s, d] = [self.col_count, col].map(|k| k * n);
                    ptr.add(s).copy_to(ptr.add(d), n);
                    ptr.add(s).write_bytes(0, size_of::<usize>() * n);
                }

                let n = self.integers_needed_each_row();
                let (a, b) = indices(col);
                let (x, y) = indices(self.col_count);
                for i in 0..self.row_count {
                    let [s, d] = [x, a].map(|k| k + i * n);
                    let value = ptr.add(s).as_ref().read(y);
                    ptr.add(d).as_mut().write(b, value);
                    ptr.add(s).as_mut().unset(y);
                }
            }
        }
        debug_assert!(self.is_consistent(), "Data is inconsistent after swap removing col.");
    }

    const fn integers_needed(&self) -> usize {
        self.integers_needed_rows() + self.integers_needed_cols()
    }

    const fn integers_needed_rows(&self) -> usize {
        self.row_capac * self.integers_needed_each_row()
    }

    const fn integers_needed_cols(&self) -> usize {
        self.col_capac * self.integers_needed_each_col()
    }

    pub(crate) const fn integers_needed_each_row(&self) -> usize {
        integers_needed(self.col_capac)
    }

    pub(crate) const fn integers_needed_each_col(&self) -> usize {
        integers_needed(self.row_capac)
    }

    pub(crate) const fn integers_used_each_row(&self) -> usize {
        integers_needed(self.col_count)
    }

    pub(crate) const fn integers_used_each_col(&self) -> usize {
        integers_needed(self.row_count)
    }

    pub(crate) fn layout(&self) -> Layout {
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

impl<A: Allocator + Clone> Clone for BitMatrix<A> {
    fn clone(&self) -> Self {
        debug_assert!(self.is_consistent(), "Data is inconsistent before cloning.");
        let allocator = self.allocator.clone();
        let mut res = Self::with_capacity_in(self.row_count, self.col_count, allocator);

        if let Some(dst) = res.rc_memory {
            let src = self.rc_memory.unwrap();

            unsafe {
                let src_needed = self.integers_needed_each_row();
                let dst_needed = res.integers_needed_each_row();
                for r in 0..self.row_count {
                    src.add(r * src_needed)
                        .copy_to(dst.add(r * dst_needed), dst_needed);
                }

                let src = src.add(self.integers_needed_rows());
                let dst = dst.add(res.integers_needed_rows());
                let src_needed = self.integers_needed_each_col();
                let dst_needed = res.integers_needed_each_col();
                for c in 0..self.col_count {
                    src.add(c * src_needed)
                        .copy_to(dst.add(c * dst_needed), dst_needed);
                }
            }
        }
        res.row_count = self.row_count;
        res.col_count = self.col_count;
        debug_assert!(res.is_consistent(), "Data is inconsistent of clone.");
        res
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
