use crate::bits::bit_matrix::BitMatrix;
use crate::bits::bit_tools::{BITS, Bits, indices, iter_ones_slice_usize};

use core::alloc::Allocator;
use core::iter::{repeat_n, zip};

impl<A: Allocator + Copy> Problem<A> {
    pub(crate) fn new_in(a: A) -> Self {
        Self(BitMatrix::new_in(a))
    }

    pub(crate) fn add_clause<I>(&mut self, literals: I)
    where
        I: Iterator<Item = isize>,
    {
        let row = self.0.rows();
        self.0.push_empty_row();
        for l in literals {
            let i = (l.abs() as usize) << 1;
            let j = l.is_negative() as usize;
            self.0.set(row, i + j - 2);
        }
    }

    pub(crate) fn del_clause(&mut self, clause: usize) {
        self.0.swap_remove_row(clause);
    }

    const fn allocator(&self) -> &A {
        self.0.allocator()
    }

    const fn buffer<T>(&self) -> Vec<T, A> {
        Vec::new_in(*self.0.allocator())
    }

    fn buffer_with_capacity<T>(&self, capacity: usize) -> Vec<T, A> {
        Vec::with_capacity_in(capacity, *self.0.allocator())
    }

    /// Remove all clauses, s.t. ∀i,j : lᵢ ∈ Cⱼ ⇒ (lⱼ) ∉ Cⱼ.
    fn remove_tautologies(&mut self) {
        let mut to_delete = self.buffer();
        to_delete.extend(repeat_n(0, self.0.integers_used_each_col()));

        for i in (0..self.0.cols()).step_by(2) {
            to_delete
                .iter_mut()
                .zip(zip(self.0.col_data(i), self.0.col_data(i + 1)).map(|(x, y)| x & y))
                .for_each(|(x, y)| *x |= y);
        }

        let mut w = self.buffer();
        w.extend(iter_ones_slice_usize(&to_delete));
        w.into_iter().rev().for_each(|i| self.del_clause(i));
    }

    fn remove_pure_literals(&mut self) {
        let mut i = 0;
        while i < self.0.cols() {
            let pos_data = self.0.col_data(i);
            let neg_data = self.0.col_data(i + 1);
            if pos_data.iter().all(|&x| x == 0) || neg_data.iter().all(|&x| x == 0) {
                self.0.swap_remove_col(i + 1);
                self.0.swap_remove_col(i);
            } else {
                i += 2;
            }
        }
    }

    /// Shrink clause *i*, s.t. ∀j : Cⱼ ∖ Cᵢ = {l} ⇒ (-l) ∉ Cᵢ.
    fn shrink_clause(&mut self, clause: usize) {
        let row_count = self.0.rows();
        assert!(clause <= row_count);

        let (used_each_col, last_col, mask_col) = {
            let (i, j) = indices(row_count - 1);
            (i + 1, i, usize::MAX >> (BITS - j - 1))
        };

        let mut tmp_row = self.buffer();
        let mut tmp_col = self.buffer();

        loop {
            let row = self.0.row_data(clause);
            tmp_row.extend(row.iter().map(|x| !x));
            let mut literal_to_delete = None;

            for l in iter_ones_slice_usize(row) {
                tmp_row.flip(l ^ 1);
                tmp_row.flip(l);

                tmp_col.extend(repeat_n(0, used_each_col));

                for t in iter_ones_slice_usize(&tmp_row) {
                    tmp_col
                        .iter_mut()
                        .zip(self.0.col_data(t))
                        .for_each(|(x, y)| *x |= y);
                }

                tmp_col.iter_mut().for_each(|x| *x = !*x);
                tmp_col[last_col] &= mask_col;

                if tmp_col.iter().any(|&x| x != 0) {
                    literal_to_delete = Some(l);
                    tmp_col.clear();
                    break;
                }

                tmp_col.clear();
                tmp_row.flip(l ^ 1);
                tmp_row.flip(l);
            }

            if let Some(x) = literal_to_delete {
                self.0.flip(clause, x);
                tmp_row.clear();
                continue;
            }
            break;
        }
    }

    fn handle_shrinked(&mut self, mut shrinked: Vec<usize>) {
        let row_count = self.0.rows();
        assert!(shrinked.iter().all(|&i| i < row_count));

        let (used_each_col, last_col, mask_col) = {
            let (i, j) = indices(row_count - 1);
            (i + 1, i, usize::MAX >> (BITS - j - 1))
        };

        let mut to_delete = self.buffer();
        to_delete.extend(repeat_n(0, used_each_col));

        let mut tmp_row = self.buffer();
        let mut tmp_col = self.buffer();
        let mut cpy_row = self.buffer();
        while let Some(x) = shrinked.pop() {
            if to_delete.read(x) {
                continue;
            }

            self.shrink_clause(x);
            let row = self.0.row_data(x);

            // Subsumption ellminiation (mark only).
            {
                tmp_col.extend(repeat_n(usize::MAX, used_each_col));
                tmp_col[last_col] &= mask_col;

                for i in iter_ones_slice_usize(row) {
                    tmp_col
                        .iter_mut()
                        .zip(self.0.col_data(i))
                        .for_each(|(x, y)| *x &= y);
                }
                tmp_col.flip(x);
                to_delete
                    .iter_mut()
                    .zip(&tmp_col)
                    .for_each(|(x, y)| *x |= y);
                tmp_col.clear();
            }

            // Shrink clauses and feed back into stack.
            {
                cpy_row.extend_from_slice(row);
                tmp_row.extend_from_slice(row);
                for l in iter_ones_slice_usize(&cpy_row) {
                    tmp_row.flip(l ^ 1);
                    tmp_row.flip(l);

                    // Like Subsumption ellminiation (mark only).
                    {
                        tmp_col.extend(repeat_n(usize::MAX, used_each_col));
                        tmp_col[last_col] &= mask_col;

                        for i in iter_ones_slice_usize(&cpy_row) {
                            tmp_col
                                .iter_mut()
                                .zip(self.0.col_data(i))
                                .for_each(|(x, y)| *x &= y);
                        }
                        tmp_col.flip(x);
                        for i in iter_ones_slice_usize(&tmp_col) {
                            self.0.flip(i, l ^ 1);
                            shrinked.push(i);
                        }
                        tmp_col.clear();
                    }

                    tmp_row.flip(l ^ 1);
                    tmp_row.flip(l);
                }
                cpy_row.clear();
                tmp_row.clear();
            }
        }
    }

    fn choose(&self) -> Option<usize> {
        let mut max = None;
        for i in 0..self.0.cols() {
            let x: u32 = self.0.col_data(i).iter().map(|x| x.count_ones()).sum();
            debug_assert!(x > 0);
            match max {
                Some((_, y)) if y >= x => (),
                _ => max = Some((i, x)),
            }
        }

        max.map(|x| x.0)
    }

    fn resolve(&mut self, literal: usize) {
        let mut tmp = self.buffer();

        tmp.extend(self.0.col_data(literal ^ 1));
        for i in iter_ones_slice_usize(&tmp) {
            self.0.flip(i, literal ^ 1);
        }

        tmp.clear();

        tmp.extend(iter_ones_slice_usize(self.0.col_data(literal)));
        tmp.into_iter().rev().for_each(|i| self.del_clause(i));
    }

    fn kernelize(&mut self) {
        loop {
            let old_len = self.0.rows();
            self.remove_pure_literals();
            if old_len == self.0.rows() {
                break;
            }
        }
    }

    pub(crate) fn prepare(&mut self) {
        self.remove_tautologies();
    }

    pub(crate) fn solve(&mut self) -> bool {
        self.kernelize();
        if self.0.rows() == 0 {
            return true;
        }
        if self.0.rows() == 1 {
            return false;
        }

        let mut cpy = self.clone();

        let choice = self.choose().expect("Should have some variables left.");

        self.resolve(choice);
        if self.solve() {
            return true;
        }

        cpy.resolve(choice ^ 1);
        if cpy.solve() {
            return true;
        }

        false
    }
}

#[derive(Clone)]
pub(crate) struct Problem<A: Allocator + Copy>(BitMatrix<A>);
