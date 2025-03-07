use crate::alloc::PoolAlloc;
use crate::data::{Clause, blocks_needed, bytes_needed};
use crate::utils::*;
use core::alloc::{Allocator, Layout};
use core::iter::{FusedIterator, Iterator};
use core::mem;
use core::ops::Neg;
use rand::seq::IndexedRandom;

impl Solver {
    pub fn new(var_numbr: usize, cls_numbr: usize) -> Self {
        let max_steps = usize::min(var_numbr, cls_numbr / 3 + 3);

        let cls_alloc = {
            let bytes = bytes_needed(var_numbr);
            let layout = Layout::from_size_align(bytes, 32).unwrap();
            Box::into_raw(Box::new(PoolAlloc::new(
                layout,
                100 + max_steps * cls_numbr,
            )))
        };

        let vec_alloc = {
            let bytes = size_of::<Clause<&PoolAlloc>>() * cls_numbr * 2;
            let layout = Layout::from_size_align(bytes, 32).unwrap();
            Box::into_raw(Box::new(PoolAlloc::new(layout, 100 + max_steps)))
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
                x.clauses
                    .push_within_capacity(new_clause)
                    .unwrap_or_else(|_| panic!("Not enough capacity"));
                Ok(())
            }
            _ => Err(SolverError::TooManyClauses),
        }
    }

    pub fn solve(&mut self) -> Result<Solution, SolverError> {
        match &mut self.work_onto {
            Task::Done(x) => Ok(x.clone()),
            Task::Todo(x) => {
                if x.clauses.len() < self.cls_numbr {
                    return Err(SolverError::TooFewClauses);
                }
                x.prepare();
                let solution = if x.solve() {
                    let mut tmp: Vec<_> = x.guessed.iter_literals().collect();
                    tmp.sort_by_key(|x| x.abs());
                    Solution::Satisfiable(tmp)
                } else {
                    Solution::Unsatisfiable
                };

                self.work_onto = Task::Done(solution.clone());
                return Ok(solution);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Solution {
    Satisfiable(Vec<isize>),
    Unsatisfiable,
}

pub struct Solver {
    var_numbr: usize,
    cls_numbr: usize,
    cls_alloc: *mut PoolAlloc,
    vec_alloc: *mut PoolAlloc,
    work_onto: Task<Problem<&'static PoolAlloc, &'static PoolAlloc>, Solution>,
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
        Self {
            guessed: Clause::new(blocks, a),
            deduced: Clause::new(blocks, a),
            clauses: Vec::with_capacity_in(cls, b),
            recents: Vec::new(),
        }
    }

    fn new_for_clauses(guessed: Clause<A>, deduced: Clause<A>, clauses: Vec<Clause<A>, B>) -> Self {
        Self {
            guessed,
            deduced,
            clauses,
            recents: Vec::new(),
        }
    }

    fn sort(&mut self) {
        self.clauses.sort_by_key(Clause::len)
    }

    fn descend(&mut self, k: usize) -> usize {
        self.descend_by_key(k, Clause::len)
    }

    // fn ascend(&mut self, k: usize) -> usize {
    //     self.ascend_by_key(k, Clause::len)
    // }

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
        literals.choose(&mut rand::rng()).copied().map(Neg::neg)
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
            self.remove_long_clauses();

            let old_length = self.clauses.len();
            self.remove_pure_literals();
            if old_length != self.clauses.len() {
                continue;
            }

            let old_length = self.clauses.len();
            self.remove_rarest_literal();
            if old_length != self.clauses.len() {
                continue;
            }

            break;
        }
    }

    fn solve(&mut self) -> bool {
        self.kernelize();
        if self.clauses.len() == 0 {
            return true;
        }
        if self.clauses.len() == 1 {
            return false;
        }

        let comps = {
            let mut tmp = Vec::new_in(*Vec::allocator(&self.clauses));
            mem::swap(&mut tmp, &mut self.clauses);
            Components::new(self.guessed.clone(), self.deduced.clone(), tmp)
        };

        for mut comp in comps {
            let copy = comp.clone();
            comp.resolve(comp.choice().unwrap());
            if comp.solve() {
                self.guessed.union_in(&comp.guessed);
                self.deduced.union_in(&comp.deduced);
                continue;
            }
            comp = copy;
            comp.resolve(comp.choice().unwrap());
            if comp.solve() {
                self.guessed.union_in(&comp.guessed);
                self.deduced.union_in(&comp.deduced);
                continue;
            }
            return false;
        }
        true
    }

    fn remove_single_occurance(&mut self, literal: isize) {
        let mut buf = Vec::with_capacity_in(self.clauses.len(), *Vec::allocator(&self.clauses));
        self.clauses.extract_in(&mut buf, |x| x.read(-literal));
        let k = self.clauses.iter().position(|x| x.read(literal)).unwrap();
        let mut x = self.clauses.remove(k);
        x.unset(literal);

        buf.iter_mut().for_each(|y| {
            assert!(y.read(-literal));
            y.unset(-literal);
            y.union_in(&x)
        });

        buf.retain(Clause::disjoint_switched_self);
        buf.retain(|x| self.clauses.iter().find(|y| y.subset_of(&x)).is_none());

        buf.drain(..).for_each(|x| {
            self.clauses
                .push_within_capacity(x)
                .unwrap_or_else(|_| panic!("Not enough capacity"));
            let k = self.combine_from(self.clauses.len() - 1);
            self.subsumption_from(k);
            self.recents.push(k);
            self.consume_recents();
        });
    }

    fn remove_rarest_literal(&mut self) {
        let mut once = self.guessed.create_sibling();
        let mut twice = self.guessed.create_sibling();

        self.clauses.iter().for_each(|now| {
            once.union_in(now);
            twice.union_with_joined_in(now, &once);
        });

        once.difference_in(&twice);

        if let Some(literal) = once.iter_literals().next() {
            self.remove_single_occurance(literal);
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
        unsafe {
            let _ = Box::from_raw(self.cls_alloc);
            let _ = Box::from_raw(self.vec_alloc);
        }
    }
}

impl<A, B> FusedIterator for Components<A, B>
where
    A: Allocator + Copy,
    B: Allocator + Copy,
{
}

impl<A, B> Iterator for Components<A, B>
where
    A: Allocator + Copy,
    B: Allocator + Copy,
{
    type Item = Problem<A, B>;
    fn next(&mut self) -> Option<Self::Item> {
        let x = self.clauses.pop()?;
        let (mut v, mut e) = {
            let b = *Vec::allocator(&self.clauses);
            (
                Vec::with_capacity_in(self.clauses.len(), b),
                Vec::with_capacity_in(self.clauses.len(), b),
            )
        };
        let mut r = x.variables();
        v.push_within_capacity(x)
            .unwrap_or_else(|_| panic!("Not enough capacity"));
        loop {
            self.clauses.extract_in(&mut e, |x| x.has_variables(&r));
            if e.is_empty() {
                break;
            }
            e.iter().for_each(|x| x.enrich_variables(&mut r));
            v.extend(e.drain(..));
        }

        v.sort_by_key(Clause::len);
        return Some(Problem::new_for_clauses(
            self.guessed.clone(),
            self.deduced.clone(),
            v,
        ));
    }
}

impl<A, B> Components<A, B>
where
    A: Allocator + Copy,
    B: Allocator + Copy,
{
    fn new<'a>(
        guessed: Clause<A>,
        deduced: Clause<A>,
        clauses: Vec<Clause<A>, B>,
    ) -> Components<A, B> {
        Components {
            guessed,
            deduced,
            clauses,
        }
    }
}

struct Components<A, B>
where
    A: Allocator + Copy,
    B: Allocator + Copy,
{
    guessed: Clause<A>,
    deduced: Clause<A>,
    clauses: Vec<Clause<A>, B>,
}
