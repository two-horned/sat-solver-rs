use crate::bits::bit_matrix::BitMatrix;
use crate::bits::bit_tools::{BITS, Bits, indices, iter_ones_slice_usize};

use core::alloc::Allocator;
use core::iter::{Map, Zip, repeat_n, zip};
use core::ops::{BitAnd, BitAndAssign, BitOrAssign};

fn zip_with<I, J, F, T, S, R>(
    lhs: I,
    rhs: J,
    f: F,
) -> Map<Zip<<I as IntoIterator>::IntoIter, <J as IntoIterator>::IntoIter>, impl (FnMut((T, S)) -> R)>
where
    I: IntoIterator<Item = T>,
    J: IntoIterator<Item = S>,
    F: Fn(T, S) -> R,
{
    zip(lhs, rhs).map(move |(x, y)| f(x, y))
}

fn zip_for_each<I, J, F, T, S>(lhs: I, rhs: J, f: F)
where
    I: IntoIterator<Item = T>,
    J: IntoIterator<Item = S>,
    F: Fn(T, S) -> (),
{
    zip(lhs, rhs).for_each(|(x, y)| f(x, y));
}

impl<A: Allocator + Copy> Problem<A> {
    pub(crate) fn new_in(a: A) -> Self {
        Self(BitMatrix::new_in(a))
    }

    pub(crate) fn with_capacity_in(clauses: usize, variables: usize, a: A) -> Self {
        Self(BitMatrix::with_capacity_in(clauses, variables << 1, a))
    }

    pub(crate) const fn clauses(&self) -> usize {
        self.0.rows()
    }

    pub(crate) const fn literals(&self) -> usize {
        self.0.cols()
    }

    pub(crate) const fn variables(&self) -> usize {
        self.literals() >> 1
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

            let k = i + 1 - 2;
            while k >= self.0.cols() {
                self.0.push_empty_col(); // Quick'n'dirty
            }
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
        Vec::new_in(*self.allocator())
    }

    /// Remove all clauses, s.t. ∀i,j : lᵢ ∈ Cⱼ ⇒ (lᵢ) ∉ Cⱼ.
    fn remove_tautologies(&mut self) {
        let mut to_delete = self.buffer();
        to_delete.extend(repeat_n(0, self.0.integers_used_each_col()));

        for i in (0..self.literals()).step_by(2) {
            zip_for_each(
                to_delete.iter_mut(),
                zip_with(self.0.col_data(i), self.0.col_data(i + 1), BitAnd::bitand),
                BitOrAssign::bitor_assign,
            );
        }

        let mut tmp = self.buffer();
        tmp.extend(iter_ones_slice_usize(&to_delete));
        tmp.into_iter().rev().for_each(|i| self.del_clause(i));
    }

    /// Remove (and resolve) pure literals.
    fn remove_pure_literals(&mut self) {
        let mut tmp = self.buffer();

        let mut i = 0;
        while i < self.literals() {
            let pos_data = self.0.col_data(i);
            let neg_data = self.0.col_data(i + 1);
            if pos_data.iter().all(|&x| x == 0) {
                tmp.extend(iter_ones_slice_usize(neg_data));
                tmp.iter().rev().for_each(|&i| self.del_clause(i));
                self.0.swap_remove_col(i + 1);
                self.0.swap_remove_col(i);
                tmp.clear();
            } else if neg_data.iter().all(|&x| x == 0) {
                tmp.extend(iter_ones_slice_usize(pos_data));
                tmp.iter().rev().for_each(|&i| self.del_clause(i));
                self.0.swap_remove_col(i + 1);
                self.0.swap_remove_col(i);
                tmp.clear();
            } else {
                i += 2;
            }
        }
    }

    /// Shrink clause *i*, s.t. ∀j : Cⱼ ∖ Cᵢ = {l} ⇒ (-l) ∉ Cᵢ.
    fn shrink_clause(&mut self, clause: usize) {
        let (row_count, col_count) = (self.0.rows(), self.0.cols());
        assert!(clause <= row_count);
        if col_count == 0 {
            return;
        }

        let (used_each_col, last_col, mask_col) = {
            let (i, j) = indices(row_count - 1);
            (i + 1, i, usize::MAX >> (BITS - j - 1))
        };

        let (last_row, mask_row) = {
            let (i, j) = indices(col_count - 1);
            (i, usize::MAX >> (BITS - j - 1))
        };

        let mut tmp_row = self.buffer();
        let mut tmp_col = self.buffer();

        loop {
            let row = self.0.row_data(clause);
            tmp_row.extend(row.iter().map(|x| !x));
            tmp_row[last_row] &= mask_row;
            let mut literal_to_delete = None;

            for l in iter_ones_slice_usize(row) {
                tmp_row.flip(l ^ 1);
                tmp_row.flip(l);

                tmp_col.extend(repeat_n(0, used_each_col));

                for t in iter_ones_slice_usize(&tmp_row) {
                    zip_for_each(
                        tmp_col.iter_mut(),
                        self.0.col_data(t),
                        BitOrAssign::bitor_assign,
                    );
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

    fn handle_shrinked<B: Allocator>(&mut self, mut shrinked: Vec<usize, B>) {
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
                    zip_for_each(
                        tmp_col.iter_mut(),
                        self.0.col_data(i),
                        BitAndAssign::bitand_assign,
                    );
                }
                tmp_col.flip(x);
                zip_for_each(to_delete.iter_mut(), &tmp_col, BitOrAssign::bitor_assign);
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
                            zip_for_each(
                                tmp_col.iter_mut(),
                                self.0.col_data(i),
                                BitAndAssign::bitand_assign,
                            );
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

    /// Returns the literals with highest occurance.
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

    /// Resolve a literal and restore invariants afterwards.
    fn resolve(&mut self, literal: usize) {
        let mut tmp = self.buffer();

        tmp.extend(iter_ones_slice_usize(self.0.col_data(literal)));
        tmp.iter().rev().for_each(|&i| self.del_clause(i));
        tmp.clear();

        tmp.extend(iter_ones_slice_usize(self.0.col_data(literal ^ 1)));
        tmp.iter().for_each(|&i| self.0.flip(i, literal ^ 1));

        let mut cols = [literal ^ 1, literal];
        cols.sort();
        cols.into_iter()
            .rev()
            .for_each(|i| self.0.swap_remove_col(i));

        self.handle_shrinked(tmp);
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

    /// Establishes invariances.
    pub(crate) fn prepare(&mut self) {
        self.remove_tautologies();
        let mut tmp = self.buffer();
        tmp.extend(0..self.0.rows());
        self.handle_shrinked(tmp);
    }

    pub(crate) fn solve(mut self) -> bool {
        if self.0.rows() == 1 {
            if self.0.row_data(0).iter().all(|&x| x == 0) {
                return false;
            } else {
                return true;
            }
        }

        self.kernelize();
        if self.0.rows() == 0 {
            return true;
        }

        let mut cpy = self.clone();

        let choice = {
            match self.choose() {
                Some(x) => x,
                _ => return false,
            }
        };

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
