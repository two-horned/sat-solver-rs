use core::alloc::{Allocator, Layout};
use core::iter;
use core::mem;
use core::pin::Pin;

use rand::seq::IndexedRandom;

use crate::alloc::PoolAlloc;
use crate::data::{blocks_needed, bytes_needed, Clause};
use crate::utils::*;

impl Solver {
    pub fn new(var_numbr: usize, cls_numbr: usize) -> Self {
        let cls_alloc = {
            let bytes = bytes_needed(var_numbr);
            let layout = Layout::from_size_align(bytes * cls_numbr, 32).unwrap();
            Box::into_raw(Box::new(PoolAlloc::new(
                layout,
                100 + var_numbr * cls_numbr,
            )))
        };

        let vec_alloc = {
            let layout =
                Layout::from_size_align(size_of::<Clause<&PoolAlloc>>() * cls_numbr, 32).unwrap();
            Box::into_raw(Box::new(PoolAlloc::new(
                layout,
                100 + var_numbr * cls_numbr,
            )))
        };

        let task_todo = Problem::new(var_numbr, cls_numbr, unsafe { &*cls_alloc }, unsafe {
            &*vec_alloc
        });

        Self {
            var_numbr,
            cls_numbr,
            cls_alloc,
            vec_alloc,
            task_todo,
        }
    }

    pub fn need_to_add(&self) -> bool {
        self.task_todo.clauses.len() < self.cls_numbr
    }

    pub fn add_clause(&mut self, literals: Vec<isize>) -> Result<(), SolverError> {
        let mut new_clause = {
            let blocks = blocks_needed(self.var_numbr);
            Clause::new(blocks, unsafe { &*self.cls_alloc })
        };

        for i in literals {
            if i == 0 {
                return Err(SolverError::VariableIsZero);
            }
            if i.abs() > self.var_numbr as isize {
                return Err(SolverError::VariableTooLarge(i));
            }
            new_clause.set(i);
        }
        self.task_todo.clauses.push(new_clause);
        Ok(())
    }

    pub fn solve(&mut self) -> Option<Vec<isize>> {
        self.task_todo.prepare();
        self.task_todo.solve()
    }
}

pub struct Solver {
    var_numbr: usize,
    cls_numbr: usize,
    cls_alloc: *mut PoolAlloc,
    vec_alloc: *mut PoolAlloc,
    task_todo: Problem<&'static PoolAlloc, &'static PoolAlloc>,
}

impl<A, B> Problem<A, B>
where
    A: Allocator + Copy + std::fmt::Debug,
    B: Allocator + Copy,
{
    fn new(vrs: usize, cls: usize, a: A, b: B) -> Self {
        let blocks = blocks_needed(vrs);
        Problem {
            guessed: Clause::new(blocks, a),
            deduced: Clause::new(blocks, a),
            clauses: Vec::with_capacity_in(cls, b),
            recents: Vec::new(),
        }
    }

    fn sort(&mut self) {
        self.clauses.sort_by_key(Clause::elements)
    }

    fn descend(&mut self, k: usize) -> usize {
        self.descend_by_key(k, Clause::elements)
    }

    fn ascend(&mut self, k: usize) -> usize {
        self.ascend_by_key(k, Clause::elements)
    }

    fn subsumption_from(&mut self, k: usize) {
        let c = self.clauses[k].clone();
        self.clauses.retain_from(|x| !c.subset_of(x), k + 1)
    }

    fn count_supersets_of_till(&self, of: usize, till: usize) -> usize {
        self.count_supersets_of_from_till(of, of + 1, till)
    }

    fn count_supersets_of_from(&self, of: usize, from: usize) -> usize {
        let x = &self.clauses[of];
        self.clauses
            .iter()
            .skip(from)
            .filter(|y| x.subset_of(y))
            .count()
    }

    fn count_supersets_of_from_till(&self, of: usize, from: usize, till: usize) -> usize {
        let x = &self.clauses[of];
        self.clauses
            .iter()
            .take(till + 1)
            .skip(from)
            .filter(|y| x.subset_of(y))
            .count()
    }

    fn remove_tautologies(&mut self) {
        self.clauses.retain(Clause::disjoint_switched_self)
    }

    fn remove_pure_literals(&mut self) {
        self.clauses
            .iter()
            .for_each(|x| self.deduced.unsafe_union_in(x));

        self.deduced = self.deduced.difference_switched_self();
        self.clauses.retain(|x| self.deduced.disjoint(x));
    }

    fn remove_long_clauses(&mut self) {
        while let Some(x) = self.clauses.last() {
            if x.elements() < self.clauses.len() {
                return;
            }
            self.clauses.pop();
        }
    }

    fn combine_from(&mut self, mut k: usize) -> usize {
        loop {
            k = self.descend(k);
            let x = &self.clauses[k];
            match self
                .clauses
                .iter()
                .take(k)
                .find_map(|y| y.unsafe_symmetry_in(x))
            {
                Some(badness) => {
                    self.clauses[k].unset(badness);
                }
                _ => break,
            }
        }
        k
    }

    fn choice(&self) -> Option<isize> {
        let literals: Vec<isize> = self.clauses[0].iter_literals().collect();
        literals.choose(&mut rand::rng()).copied()
    }

    fn consume_recents(&mut self) {
        while let Some(k) = self.recents.pop() {
            let c = self.clauses[k].clone();
            let mut i = k;
            while i < self.clauses.len() {
                if let Some(badness) = c.unsafe_symmetry_in(&self.clauses[i]) {
                    i -= self.delete_literal(i, badness);
                }
                i += 1;
            }
        }
    }

    fn delete_literal(&mut self, at: usize, literal: isize) -> usize {
        println!("K is {}", at);
        println!("deleting {}", literal);
        self.clauses[at].unset(literal);
        let k = self.combine_from(at);
        self.recents
            .retain(|&x| x > k && !self.clauses[k].subset_of(&self.clauses[x]));
        println!(
            "{:?}",
            iter::zip(
                self.recents.iter(),
                self.recents
                    .iter()
                    .map(|&x| self.clauses[k].subset_of(&self.clauses[x]))
            )
            .collect::<Vec<_>>()
        );
        println!(
            "{:?}",
            self.clauses
                .iter()
                .map(|x| self.clauses[k].subset_of(x))
                .collect::<Vec<_>>()
        );
        let res = {
            let mut res = 0;
            let mut r = 0;
            for i in 0..self.recents.len() {
                let tmp = self.count_supersets_of_from_till(k, r, self.recents[i]);
                res += tmp;
                self.recents[i] -= tmp;
                r = self.recents[i];
            }
            res += self.count_supersets_of_from(k, r);
            println!("Returning {}", res);
            res
        };
        self.subsumption_from(k);
        self.recents.push(k);
        self.recents.descend(self.recents.len() - 1);
        res - 1
    }

    fn resolve(&mut self, literal: isize) {
        self.guessed.set(literal);
        self.clauses.retain(|x| !x.read(literal));
        let mut i = 0;
        while i < self.clauses.len() {
            if self.clauses[i].read(-literal) {
                i -= self.delete_literal(i, -literal);
            }
            i += 1;
        }
        self.consume_recents();
    }

    fn prepare(&mut self) {
        self.remove_tautologies();
        self.sort();

        let mut i = 0;
        while i < self.clauses.len() {
            self.subsumption_from(i);
            i += 1;
        }

        i = 0;
        while i < self.clauses.len() {
            let x = &self.clauses[i];
            match self
                .clauses
                .iter()
                .take(i)
                .find_map(|y| y.unsafe_symmetry_in(x))
            {
                Some(badness) => i -= self.delete_literal(i, badness),
                _ => (),
            }
            i += 1;
        }
        self.consume_recents();
    }

    fn kernelize(&mut self) {
        loop {
            let old_length = self.clauses.len();
            self.remove_long_clauses();
            self.remove_pure_literals();
            if old_length == self.clauses.len() {
                break;
            }
        }
    }

    fn solve(&mut self) -> Option<Vec<isize>> {
        println!("ok, solving...");
        for x in &self.clauses {
            x.iter_literals().for_each(|y| print!("{} ", y));
            println!();
        }

        self.kernelize();
        if self.clauses.len() == 0 {
            let mut solution: Vec<_> = self.guessed.iter_literals().collect();
            solution.sort_by_key(|x| x.abs());
            return Some(solution);
        }

        if let Some(c) = self.choice() {
            let mut copy = self.clone();
            self.resolve(c);
            if let Some(r) = self.solve() {
                return Some(r);
            }
            copy.resolve(-c);
            if let Some(r) = copy.solve() {
                return Some(r);
            }
        }
        None
    }
}

impl<A, B> Descent for Problem<A, B>
where
    A: Allocator + Copy + std::fmt::Debug,
    B: Allocator + Copy,
{
    type Item = Clause<A>;

    fn descend_by<F>(&mut self, k: usize, f: F) -> usize
    where
        F: Fn(&Self::Item, &Self::Item) -> std::cmp::Ordering,
    {
        self.clauses.descend_by(k, f)
    }
}

impl<A, B> Ascent for Problem<A, B>
where
    A: Allocator + Copy + std::fmt::Debug,
    B: Allocator + Copy,
{
    type Item = Clause<A>;

    fn ascend_by<F>(&mut self, k: usize, f: F) -> usize
    where
        F: Fn(&Self::Item, &Self::Item) -> std::cmp::Ordering,
    {
        self.clauses.ascend_by(k, f)
    }
}

#[derive(Clone)]
struct Problem<A, B>
where
    A: Allocator + Copy + std::fmt::Debug,
    B: Allocator + Copy,
{
    guessed: Clause<A>,
    deduced: Clause<A>,
    clauses: Vec<Clause<A>, B>,
    recents: Vec<usize>,
}

#[derive(Debug)]
pub enum SolverError {
    VariableIsZero,
    VariableTooLarge(isize),
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe {
            Box::from_raw(self.cls_alloc);
            Box::from_raw(self.vec_alloc);
        }
    }
}
