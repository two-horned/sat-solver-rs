use std::iter::{self, FusedIterator};
use std::{cmp, usize};

const BLOCK_SIZE: usize = usize::BITS as usize;

pub struct Problem {
    pub vrcount: usize,
    pub clauses: Vec<Clause>,
    pub deduced: Clause,
    pub guessed: Clause,
}

#[derive(Debug)]
pub enum ParseProblemError {
    MissingHeader,
    TooLargeVariable,
    NotANumber(String),
    NegativeNumber(String),
}

impl Clause {
    pub fn new(capacity: usize) -> Self {
        let len = capacity / BLOCK_SIZE + if capacity % BLOCK_SIZE == 0 { 0 } else { 1 };
        Self {
            pos: BitVec {
                content: iter::repeat_n(0, len).collect(),
            },
            neg: BitVec {
                content: iter::repeat_n(0, len).collect(),
            },
        }
    }

    pub fn new_blocks(blocks: usize) -> Self {
        Self {
            pos: BitVec {
                content: iter::repeat_n(0, blocks).collect(),
            },
            neg: BitVec {
                content: iter::repeat_n(0, blocks).collect(),
            },
        }
    }

    pub fn count_ones(&self) -> u32 {
        self.pos.count_ones() + self.neg.count_ones()
    }

    pub fn content_pos(&self) -> &[usize] {
        &self.pos.content
    }
    pub fn content_neg(&self) -> &[usize] {
        &self.neg.content
    }

    pub fn content_pos_mut(&mut self) -> &mut [usize] {
        &mut self.pos.content
    }
    pub fn content_neg_mut(&mut self) -> &mut [usize] {
        &mut self.neg.content
    }

    pub fn zip_clause_in<F>(&mut self, rhs: &Self, f: F)
    where
        F: Fn(&mut usize, usize) -> (),
    {
        self.pos.zip_bits_in(&rhs.pos, &f);
        self.neg.zip_bits_in(&rhs.neg, f);
    }

    pub fn subset_of(&self, rhs: &Self) -> bool {
        self.pos.subset_of(&rhs.pos) && self.neg.subset_of(&rhs.neg)
    }

    pub fn difference(&self, rhs: &Self) -> Self {
        let pos = self.pos.difference(&rhs.pos);
        let neg = self.neg.difference(&rhs.neg);
        Self { pos, neg }
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

    pub fn enrich_variables(&self, vrs: &mut BitVec) {
        for i in 0..usize::min(vrs.content.len(), self.pos.content.len()) {
            vrs.content[i] |= self.pos.content[i] | self.neg.content[i];
        }
    }

    pub fn has_variables(&self, vrs: &BitVec) -> bool {
        for i in 0..usize::min(self.content_length(), vrs.content.len()) {
            if 0 != (self.pos.content[i] | self.neg.content[i]) & vrs.content[i] {
                return true;
            }
        }
        false
    }

    pub fn related(&self, rhs: &Self) -> bool {
        for i in 0..usize::min(self.content_length(), rhs.content_length()) {
            if 0 != (self.pos.content[i] | self.neg.content[i])
                & (rhs.pos.content[i] | rhs.neg.content[i])
            {
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

    pub fn find_shared(&self, rhs: &Self) -> Option<isize> {
        match self.pos.find_shared(&rhs.pos) {
            Some(x) => return Some(x as isize),
            _ => (),
        }
        match self.neg.find_shared(&rhs.neg) {
            Some(x) => return Some(-(x as isize)),
            _ => (),
        }
        None
    }

    pub fn find_shared_switched(&self, rhs: &Self) -> Option<isize> {
        match self.pos.find_shared(&rhs.neg) {
            Some(x) => return Some(x as isize + 1),
            _ => (),
        }
        match self.neg.find_shared(&rhs.pos) {
            Some(x) => return Some(-(x as isize) - 1),
            _ => (),
        }
        None
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

    pub fn iter_pos_literals(&self) -> IterOnes<'_> {
        self.pos.iter_ones()
    }

    pub fn iter_neg_literals(&self) -> IterOnes<'_> {
        self.neg.iter_ones()
    }

    pub fn is_null(&self) -> bool {
        self.pos.is_null() && self.neg.is_null()
    }
}

impl PartialOrd for Clause {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.count_ones().partial_cmp(&other.count_ones())
    }
}

impl Ord for Clause {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.count_ones().cmp(&other.count_ones())
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Clause {
    pos: BitVec,
    neg: BitVec,
}

impl FusedIterator for IterOnes<'_> {}

impl ExactSizeIterator for IterOnes<'_> {
    fn len(&self) -> usize {
        self.vls
            .iter()
            .fold(0, |acc, x| acc + x.count_ones() as usize)
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

pub struct IterOnes<'a> {
    num: usize,
    idx: usize,
    vls: &'a [usize],
}

impl BitVec {
    fn is_null(&self) -> bool {
        self.content.iter().all(|&x| x == 0)
    }

    fn count_ones(&self) -> u32 {
        self.content.iter().fold(0, |acc, x| acc + x.count_ones())
    }

    fn iter_ones(&self) -> IterOnes<'_> {
        IterOnes {
            num: 0,
            idx: 0,
            vls: &self.content,
        }
    }

    fn zip_bits<F>(&self, rhs: &Self, f: F) -> Self
    where
        F: Fn(usize, usize) -> usize,
    {
        let content = self
            .content
            .iter()
            .zip(&rhs.content)
            .map(|(&x, &y)| f(x, y))
            .collect();
        Self { content }
    }

    fn zip_bits_in<F>(&mut self, rhs: &Self, f: F)
    where
        F: Fn(&mut usize, usize) -> (),
    {
        for i in 0..usize::min(self.content.len(), rhs.content.len()) {
            f(&mut self.content[i], rhs.content[i]);
        }
    }

    fn set(&mut self, index: usize) {
        self.content[index / BLOCK_SIZE] |= 1 << (index % BLOCK_SIZE);
    }

    fn unset(&mut self, index: usize) {
        self.content[index / BLOCK_SIZE] &= !(1 << (index % BLOCK_SIZE));
    }

    fn read(&self, index: usize) -> bool {
        self.content[index / BLOCK_SIZE] & 1 << (index % BLOCK_SIZE) != 0
    }

    fn difference(&self, rhs: &Self) -> Self {
        self.zip_bits(rhs, |x, y| x & !y)
    }

    fn subset_of(&self, rhs: &Self) -> bool {
        for i in 0..usize::min(self.content.len(), rhs.content.len()) {
            if self.content[i] & !rhs.content[i] != 0 {
                return false;
            }
        }
        true
    }

    fn find_shared(&self, rhs: &Self) -> Option<usize> {
        for i in 0..usize::min(self.content.len(), rhs.content.len()) {
            let test = self.content[i] & rhs.content[i];
            if test != 0 {
                return Some(i * BLOCK_SIZE + test.trailing_zeros() as usize);
            }
        }
        None
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
pub struct BitVec {
    content: Box<[usize]>,
}
