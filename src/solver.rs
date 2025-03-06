use core::alloc::{Allocator, Layout};
use std::iter::FusedIterator;

use crate::alloc::PoolAlloc;
use crate::data::{Clause, blocks_needed, bytes_needed};
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
            let bytes = size_of::<Clause<&PoolAlloc>>() * cls_numbr * var_numbr;
            let layout = Layout::from_size_align(bytes, 32).unwrap();
            Box::into_raw(Box::new(PoolAlloc::new(layout, 3)))
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
                    let mut guesses = 0;
                    loop {
                        guesses += 1;
                        let mut copy = x.clone();
                        if copy.guess() {
                            let solution = {
                                let mut tmp: Vec<_> = copy.guessed.iter_literals().collect();
                                tmp.sort_by_key(|x| x.abs());
                                Some(tmp)
                            };
                            self.work_onto = Task::Done(solution.clone());
                            println!("Guesses needed {}", guesses);
                            return Ok(solution);
                        }

                        if copy.guessed.is_null() {
                            self.work_onto = Task::Done(None);
                            println!("Guesses needed {}", guesses);
                            return Ok(None);
                        }

                        x.clauses.push(copy.guessed.evil_twin());
                        let k = x.combine_from(x.clauses.len() - 1);
                        x.subsumption_from(k);
                        x.recents.push(k);
                        x.consume_recents();
                    }
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

    fn remove_tautologies(&mut self) {
        self.clauses.retain(Clause::disjoint_switched_self)
    }

    fn subsumption_from(&mut self, k: usize) {
        let c = self.clauses[k].clone();
        self.clauses.retain_from(|x| !c.subset_of(x), k + 1)
    }

    fn remove_pure_literals(&mut self) {
        let mut acc = self.deduced.create_sibling();
        self.clauses.iter().for_each(|x| acc.union_in(x));

        acc.difference_switched_self();
        if !acc.is_null() {
            self.clauses.retain(|x| acc.disjoint(x));
            self.deduced.union_in(&acc);
        }
    }

    fn remove_long_clauses(&mut self) {
        let mut i = self.clauses.len();
        while i > 1 && self.clauses[i - 1].len() >= self.clauses.len() {
            i -= 1;
        }
        self.clauses.drain(i..);
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

    fn find_badness(&self, k: usize) -> Option<isize> {
        let x = &self.clauses[k];
        self.clauses.iter().take(k).find_map(|y| y.symmetry_in(x))
    }

    fn combine_from(&mut self, mut k: usize) -> usize {
        loop {
            k = self.descend(k);
            match self.find_badness(k) {
                Some(badness) => self.clauses[k].unset(badness),
                _ => return k,
            }
        }
    }

    fn consume_recents(&mut self) {
        while let Some(k) = self.recents.pop() {
            let c = self.clauses[k].clone();
            let mut i = k;
            while i < self.clauses.len() {
                if let Some(badness) = c.symmetry_in(&self.clauses[i]) {
                    i -= self.delete_literal(i, badness);
                }
                i += 1;
            }
        }
    }

    fn update_recents(&mut self, cause: usize) {
        if let Some(i) = self.recents.iter().position(|&x| x >= cause) {
            self.recents
                .retain_from(|&x| !self.clauses[cause].subset_of(&self.clauses[x]), i);

            let (mut a, mut r) = (0, cause + 1);

            for j in i..self.recents.len() {
                a += self.count_supersets_of_from_till(cause, r, self.recents[j]);
                r = self.recents[j];
                self.recents[j] -= a;
            }
        }
    }

    fn delete_literal(&mut self, at: usize, literal: isize) -> usize {
        self.clauses[at].unset(literal);
        let k = self.combine_from(at);
        let res = self.count_supersets_of_till(k, at);
        self.update_recents(k);
        self.subsumption_from(k);
        self.recents.push(k);
        self.recents.descend(self.recents.len() - 1);
        res
    }

    fn choice(&self) -> Option<isize> {
        let literals: Vec<isize> = self.clauses[0].iter_literals().collect();
        literals.choose(&mut rand::rng()).copied()
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

    fn subsumption_ellimination(&mut self) {
        let mut i = 0;
        while i < self.clauses.len() {
            self.subsumption_from(i);
            i += 1;
        }
    }

    fn break_enabled_symmetry(&mut self) {
        let mut i = 0;
        while i < self.clauses.len() {
            match self.find_badness(i) {
                Some(badness) => i -= self.delete_literal(i, badness),
                _ => (),
            }
            i += 1;
        }
    }

    fn prepare(&mut self) {
        self.remove_tautologies();
        self.sort();
        self.subsumption_ellimination();
        self.break_enabled_symmetry();
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

    fn guess(&mut self) -> bool {
        loop {
            self.kernelize();
            if self.clauses.is_empty() {
                return true;
            }
            match self.choice() {
                Some(c) => self.resolve(c),
                _ => return false,
            }
        }
    }

    fn remove_single_occurance(&mut self, literal: isize) {
        let k = self.clauses.iter().position(|x| x.read(literal)).unwrap();

        self.recents.extend(
            self.clauses
                .iter()
                .enumerate()
                .filter_map(|(i, x)| if x.read(-literal) { Some(i) } else { None }),
        );
    }

    fn remove_two_two_occurance(&mut self, literal: usize) {}

    fn remove_rarest_literal(&mut self) {
        let mut once = self.guessed.create_sibling();
        let mut twice = self.guessed.create_sibling();
        let mut thrice = self.guessed.create_sibling();

        once.difference_in(&twice);
        twice.difference_in(&thrice);

        for now in self.clauses.iter() {
            once.union_in(now);
            twice.union_with_joined_in(now, &once);
            thrice.union_with_joined_in(&once, &twice);
        }
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
            v.extend(e.drain(..));
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
