use core::alloc::{Allocator, Layout};
use std::iter::FusedIterator;

use crate::alloc::PoolAlloc;
use crate::data::{blocks_needed, bytes_needed, Clause};
use crate::utils::*;
use core::iter::Iterator;
use rand::seq::IndexedRandom;

impl Solver {
    pub fn new(var_numbr: usize, cls_numbr: usize) -> Self {
        let cls_alloc = {
            let bytes = bytes_needed(var_numbr);
            let layout = Layout::from_size_align(bytes, 32).unwrap();
            Box::into_raw(Box::new(PoolAlloc::new(
                layout,
                100 + var_numbr * cls_numbr,
            )))
        };

        let vec_alloc = {
            let bytes = size_of::<Clause<&PoolAlloc>>() * cls_numbr;
            let layout = Layout::from_size_align(bytes, 32).unwrap();
            Box::into_raw(Box::new(PoolAlloc::new(layout, 100 + var_numbr)))
        };

        let work_onto = Task::Todo(Problem::new(
            var_numbr,
            cls_numbr,
            unsafe { &*cls_alloc },
            unsafe { &*vec_alloc },
        ));
        Self {
            var_numbr,
            cls_numbr,
            cls_alloc,
            vec_alloc,
            work_onto,
        }
    }

    pub fn need_to_add(&self) -> bool {
        match &self.work_onto {
            Task::Todo(x) => x.clauses.len() < self.cls_numbr,
            _ => false,
        }
    }

    pub fn add_clause(&mut self, literals: Vec<isize>) -> Result<(), SolverError> {
        match &mut self.work_onto {
            Task::Todo(x) if x.clauses.len() < self.cls_numbr => {
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
                x.clauses.push(new_clause);
                Ok(())
            }
            _ => Err(SolverError::TooManyClauses),
        }
    }

    pub fn solve(&mut self) -> Result<Option<Vec<isize>>, SolverError> {
        match &mut self.work_onto {
            Task::Done(x) => Ok(x.clone()),
            Task::Todo(x) => {
                if x.clauses.len() < self.cls_numbr {
                    Err(SolverError::TooFewClauses)
                } else {
                    x.prepare();
                    let res = x.solve();
                    self.work_onto = Task::Done(res.clone());
                    Ok(res)
                }
            }
        }
    }
}

pub struct Solver {
    var_numbr: usize,
    cls_numbr: usize,
    cls_alloc: *mut PoolAlloc,
    vec_alloc: *mut PoolAlloc,
    work_onto: Task<Problem<&'static PoolAlloc, &'static PoolAlloc>, Option<Vec<isize>>>,
}

enum Task<A, B> {
    Todo(A),
    Done(B),
}

impl<A, B> Problem<A, B>
where
    A: Allocator + Copy,
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
        self.clauses.sort_by_key(Clause::len)
    }

    fn descend(&mut self, k: usize) -> usize {
        self.descend_by_key(k, Clause::len)
    }

    fn ascend(&mut self, k: usize) -> usize {
        self.ascend_by_key(k, Clause::len)
    }

    fn subsumption_from(&mut self, k: usize) {
        let c = self.clauses[k].clone();
        self.clauses.retain_from(|x| !c.subset_of(x), k + 1)
    }

    fn count_supersets_of_till(&self, of: usize, till: usize) -> usize {
        self.count_supersets_of_from_till(of, of + 1, till)
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
            if x.len() < self.clauses.len() {
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
                Some(badness) => self.clauses[k].unset(badness),
                _ => return k,
            }
        }
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
        self.clauses[at].unset(literal);
        let k = self.combine_from(at);
        self.recents
            .retain(|&x| x > k && !self.clauses[k].subset_of(&self.clauses[x]));
        let res = self.count_supersets_of_till(k, at);

        {
            let mut res = 0;
            let mut r = k + 1;
            for i in 0..self.recents.len() {
                if self.recents[i] <= k + 1 {
                    continue;
                }
                res += self.count_supersets_of_from_till(k, r, self.recents[i]);
                self.recents[i] -= res;
                r = self.recents[i];
            }
        }

        self.subsumption_from(k);
        self.recents.push(k);
        self.recents.descend(self.recents.len() - 1);
        res
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
        self.kernelize();
        if self.clauses.len() == 0 {
            let mut solution: Vec<_> = self.guessed.iter_literals().collect();
            solution.sort_by_key(|x| x.abs());
            return Some(solution);
        }
        if self.clauses.len() == 1 {
            return None;
        }

        let comps = {
            let mut tmp: Vec<_> = ComponentsIter::new(self).collect();
            tmp.sort_by_key(|x| x.clauses.len());
            tmp
        };

        for mut comp in comps {
            let c = comp.choice()?;
            let mut copy = comp.clone();
            comp.resolve(c);
            if comp.solve().is_some() {
                self.guessed.unsafe_union_in(&comp.guessed);
                self.deduced.unsafe_union_in(&comp.deduced);
                continue;
            }

            copy.resolve(-c);
            if copy.solve().is_some() {
                self.guessed.unsafe_union_in(&copy.guessed);
                self.deduced.unsafe_union_in(&copy.deduced);
                continue;
            }
            return None;
        }

        let mut solution: Vec<_> = self.guessed.iter_literals().collect();
        solution.sort_by_key(|x| x.abs());
        Some(solution)
    }
}

impl<A, B> Descent for Problem<A, B>
where
    A: Allocator + Copy,
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
    A: Allocator + Copy,
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
    A: Allocator + Copy,
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
    TooManyClauses,
    TooFewClauses,
}

impl Drop for Solver {
    fn drop(&mut self) {
        self.work_onto = Task::Done(None);
        unsafe {
            let _ = Box::from_raw(self.cls_alloc);
            let _ = Box::from_raw(self.vec_alloc);
        }
    }
}

impl<'a, A, B> FusedIterator for ComponentsIter<'a, A, B>
where
    A: Allocator + Copy,
    B: Allocator + Copy,
{
}

impl<'a, A, B> Iterator for ComponentsIter<'a, A, B>
where
    A: Allocator + Copy,
    B: Allocator + Copy,
{
    type Item = Problem<A, B>;
    fn next(&mut self) -> Option<Self::Item> {
        let x = self.problem.clauses.pop()?;
        let b = *Vec::allocator(&self.problem.clauses);
        let mut v = Vec::with_capacity_in(self.problem.clauses.capacity(), b);
        let mut e = Vec::with_capacity_in(self.problem.clauses.capacity(), b);
        let mut r = x.variables();
        v.push(x);
        loop {
            self.problem
                .clauses
                .extract_in(&mut e, |x| x.unsafe_has_variables(&r));
            if e.is_empty() {
                break;
            }
            e.iter().for_each(|x| x.unsafe_enrich_variables(&mut r));
            while let Some(x) = e.pop() {
                v.push(x);
            }
        }

        v.sort_by_key(Clause::len);
        return Some(Problem {
            guessed: self.problem.guessed.clone(),
            deduced: self.problem.deduced.clone(),
            clauses: v,
            recents: self.problem.recents.clone(),
        });
    }
}

impl<A, B> ComponentsIter<'_, A, B>
where
    A: Allocator + Copy,
    B: Allocator + Copy,
{
    fn new<'a>(problem: &'a mut Problem<A, B>) -> ComponentsIter<'a, A, B> {
        ComponentsIter { problem }
    }
}

struct ComponentsIter<'a, A, B>
where
    A: Allocator + Copy,
    B: Allocator + Copy,
{
    problem: &'a mut Problem<A, B>,
}
