use crate::alloc::PoolAlloc;
use std::cell::OnceCell;
use std::iter::FusedIterator;
use std::{cmp, usize};

const BLOCK_SIZE: usize = usize::BITS as usize;

#[derive(Debug)]
pub enum ParseProblemError {
    MissingHeader,
    TooLargeVariable,
    NotANumber(String),
    NegativeNumber(String),
}

pub fn blocks_needed(vrs: usize) -> usize {
    vrs / BLOCK_SIZE + if vrs % BLOCK_SIZE == 0 { 0 } else { 1 }
}

pub fn create_clause_blocks<'a>(blocks: usize, a: &'a PoolAlloc) -> Clause<'a> {
    Clause {
        pos: BitVec {
            ones: OnceCell::new(),
            content: unsafe { Box::new_zeroed_slice_in(blocks, a).assume_init() },
        },
        neg: BitVec {
            ones: OnceCell::new(),
            content: unsafe { Box::new_zeroed_slice_in(blocks, a).assume_init() },
        },
    }
}

impl Clause<'_> {
    pub fn elements(&self) -> usize {
        self.pos.ones() + self.neg.ones()
    }

    pub fn zip_clause<F>(&self, rhs: &Self, f: F) -> Self
    where
        F: Fn(usize, usize) -> usize,
    {
        Self {
            pos: self.pos.zip_bits(&rhs.pos, &f),
            neg: self.neg.zip_bits(&rhs.pos, f),
        }
    }

    pub fn unsafe_zip_clause_in<F>(&mut self, rhs: &Self, f: F)
    where
        F: Fn(&mut usize, usize) -> (),
    {
        self.pos.unsafe_zip_bits_in(&rhs.pos, &f);
        self.neg.unsafe_zip_bits_in(&rhs.neg, f);
    }

    pub fn unsafe_zip3_clause_in<F>(&mut self, rhs: &Self, rsh: &Self, f: F)
    where
        F: Fn(&mut usize, usize, usize) -> (),
    {
        self.pos.unsafe_zip3_bits_in(&rhs.pos, &rsh.pos, &f);
        self.neg.unsafe_zip3_bits_in(&rhs.neg, &rsh.neg, &f);
    }

    pub fn subset_of(&self, rhs: &Self) -> bool {
        self.pos.subset_of(&rhs.pos) && self.neg.subset_of(&rhs.neg)
    }

    pub fn difference_switched_self(&self) -> Self {
        let pos = self.pos.difference(&self.neg);
        let neg = self.neg.difference(&self.pos);
        Self { pos, neg }
    }

    pub fn read(&self, index: isize) -> bool {
        if index < 0 {
            self.neg.read(-index as usize - 1)
        } else {
            self.pos.read(index as usize - 1)
        }
    }

    pub fn set(&mut self, index: isize) {
        if index < 0 {
            self.neg.set(-index as usize - 1)
        } else {
            self.pos.set(index as usize - 1)
        }
    }
    pub fn unset(&mut self, index: isize) {
        if index < 0 {
            self.neg.unset(-index as usize - 1)
        } else {
            self.pos.unset(index as usize - 1)
        }
    }

    pub fn variables(&self) -> BitVec {
        self.pos.zip_bits(&self.neg, |x, y| x | y)
    }

    pub fn unsafe_enrich_variables(&self, vrs: &mut BitVec) {
        for i in 0..vrs.content.len() {
            vrs.content[i] |= self.pos.content[i] | self.neg.content[i];
        }
    }

    pub fn unsafe_has_variables(&self, vrs: &BitVec) -> bool {
        for i in 0..vrs.content.len() {
            if 0 != (self.pos.content[i] | self.neg.content[i]) & vrs.content[i] {
                return true;
            }
        }
        false
    }

    pub fn disjoint(&self, rhs: &Self) -> bool {
        self.pos.disjoint(&rhs.pos) && self.neg.disjoint(&rhs.neg)
    }

    pub fn disjoint_switched_self(&self) -> bool {
        self.pos.disjoint(&self.neg)
    }

    pub fn capacity(&self) -> usize {
        BLOCK_SIZE * self.pos.content.len()
    }

    pub fn content_length(&self) -> usize {
        self.pos.content.len()
    }

    pub fn iter_literals(&self) -> impl Iterator<Item = isize> + use<'_> {
        self.pos
            .iter_ones()
            .map(|x| x as isize + 1)
            .chain(self.neg.iter_ones().map(|x| -(1 + x as isize)))
    }
    pub fn unsafe_iter_differences<'b>(
        &self,
        rhs: &'b Self,
    ) -> impl Iterator<Item = isize> + use<'_, 'b> {
        self.pos
            .unsafe_iter_bin_op(&rhs.pos)
            .map(|x| x as isize + 1)
            .chain(
                self.neg
                    .unsafe_iter_bin_op(&rhs.neg)
                    .map(|x| -(1 + x as isize)),
            )
    }

    pub fn is_null(&self) -> bool {
        self.pos.is_null() && self.neg.is_null()
    }
}

impl PartialOrd for Clause<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.elements().partial_cmp(&other.elements())
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Clause<'a> {
    pos: BitVec<'a>,
    neg: BitVec<'a>,
}

impl<F> FusedIterator for BinOpIterOnes<'_, '_, F> where F: Fn(usize, usize) -> usize {}

impl<F> Iterator for BinOpIterOnes<'_, '_, F>
where
    F: Fn(usize, usize) -> usize,
{
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
        while self.num == 0 && self.idx < self.op1.len() {
            self.num = (self.f)(self.op1[self.idx], self.op2[self.idx]);
            self.idx += 1;
        }

        if self.num != 0 {
            let res = self.num.trailing_zeros() as usize + (self.idx - 1) * BLOCK_SIZE;
            self.num &= self.num - 1;
            return Some(res);
        }
        None
    }
}

struct BinOpIterOnes<'a, 'b, F>
where
    F: Fn(usize, usize) -> usize,
{
    f: F,
    num: usize,
    idx: usize,
    op1: &'a [usize],
    op2: &'b [usize],
}

impl FusedIterator for IterOnes<'_> {}

impl ExactSizeIterator for IterOnes<'_> {
    fn len(&self) -> usize {
        *self
            .len
            .get_or_init(|| self.vls.iter().map(|x| x.count_ones()).sum::<u32>() as usize)
    }
}

impl Iterator for IterOnes<'_> {
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.vls.len() && self.num == 0 {
            self.num = self.vls[self.idx];
            self.idx += 1;
        }

        if self.num != 0 {
            let res = self.num.trailing_zeros() as usize + (self.idx - 1) * BLOCK_SIZE;
            self.num &= self.num - 1;
            return Some(res);
        }
        None
    }
}

struct IterOnes<'a> {
    num: usize,
    len: OnceCell<usize>,
    idx: usize,
    vls: &'a [usize],
}

impl BitVec<'_> {
    fn ones(&self) -> usize {
        *self
            .ones
            .get_or_init(|| self.content.iter().map(|x| x.count_ones()).sum::<u32>() as usize)
    }

    fn is_null(&self) -> bool {
        self.content.iter().all(|&x| x == 0)
    }

    fn unsafe_iter_bin_op<'b>(
        &self,
        rhs: &'b Self,
    ) -> BinOpIterOnes<'_, 'b, fn(usize, usize) -> usize> {
        BinOpIterOnes {
            f: |x, y| x & !y,
            num: 0,
            idx: 0,
            op1: &self.content,
            op2: &rhs.content,
        }
    }

    fn iter_ones(&self) -> IterOnes<'_> {
        IterOnes {
            len: self.ones.clone(),
            num: 0,
            idx: 0,
            vls: &self.content,
        }
    }

    fn zip_bits<F>(&self, rhs: &Self, f: F) -> Self
    where
        F: Fn(usize, usize) -> usize,
    {
        let mut res = Self {
            ones: OnceCell::new(),
            content: self.content.clone(),
        };
        res.unsafe_zip_bits_in(&rhs, |x, y| *x = f(*x, y));
        res
    }

    fn unsafe_zip_bits_in<F>(&mut self, rhs: &Self, f: F)
    where
        F: Fn(&mut usize, usize) -> (),
    {
        self.ones.take();
        for i in 0..self.content.len() {
            f(&mut self.content[i], rhs.content[i]);
        }
    }

    fn unsafe_zip3_bits_in<F>(&mut self, rhs: &Self, rsh: &Self, f: F)
    where
        F: Fn(&mut usize, usize, usize) -> (),
    {
        self.ones.take();
        for i in 0..self.content.len() {
            f(&mut self.content[i], rhs.content[i], rsh.content[i]);
        }
    }

    fn set(&mut self, index: usize) {
        self.ones.take();
        self.content[index / BLOCK_SIZE] |= 1 << (index % BLOCK_SIZE);
    }

    fn unset(&mut self, index: usize) {
        self.ones.take();
        self.content[index / BLOCK_SIZE] &= !(1 << (index % BLOCK_SIZE));
    }

    fn read(&self, index: usize) -> bool {
        self.content[index / BLOCK_SIZE] & 1 << (index % BLOCK_SIZE) != 0
    }

    fn difference(&self, rhs: &Self) -> Self {
        self.zip_bits(rhs, |x, y| x & !y)
    }

    fn subset_of(&self, rhs: &Self) -> bool {
        self.content
            .iter()
            .zip(rhs.content.iter())
            .all(|(x, y)| x & !y == 0)
    }

    fn disjoint(&self, rhs: &Self) -> bool {
        for i in 0..usize::min(self.content.len(), rhs.content.len()) {
            if self.content[i] & rhs.content[i] != 0 {
                return false;
            }
        }
        true
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BitVec<'a> {
    ones: OnceCell<usize>,
    content: Box<[usize], &'a PoolAlloc>,
}
