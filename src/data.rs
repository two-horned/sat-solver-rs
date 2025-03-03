use core::alloc::Allocator;
use core::cell::OnceCell;
use core::iter::{self, FusedIterator};
use core::usize;

const BLOCK_SIZE: usize = usize::BITS as usize;
const BLOCK_BYTE: usize = size_of::<usize>();

pub(crate) const fn bytes_needed(vrs: usize) -> usize {
    blocks_needed(vrs) * BLOCK_BYTE
}

pub(crate) const fn blocks_needed(vrs: usize) -> usize {
    vrs / BLOCK_SIZE + if vrs % BLOCK_SIZE == 0 { 0 } else { 1 }
}

impl<A> Clause<A>
where
    A: Allocator + Copy,
{
    pub(crate) fn new(blocks: usize, a: A) -> Self
    where
        A: Allocator,
    {
        Self {
            pos: BitVec::new(blocks, a),
            neg: BitVec::new(blocks, a),
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.pos.ones() + self.neg.ones()
    }

    pub(crate) fn zip_clause<F>(&self, rhs: &Self, f: F) -> Self
    where
        F: Fn(usize, usize) -> usize,
    {
        Self {
            pos: self.pos.zip_bits(&rhs.pos, &f),
            neg: self.neg.zip_bits(&rhs.pos, f),
        }
    }

    pub(crate) fn unsafe_zip_clause_in<F>(&mut self, rhs: &Self, f: F)
    where
        F: Fn(&mut usize, usize) -> (),
    {
        self.pos.unsafe_zip_bits_in(&rhs.pos, &f);
        self.neg.unsafe_zip_bits_in(&rhs.neg, f);
    }

    pub(crate) fn unsafe_union_in(&mut self, rhs: &Self) {
        self.unsafe_zip_clause_in(rhs, |x, y| *x |= y);
    }

    pub(crate) fn unsafe_zip3_clause_in<F>(&mut self, rhs: &Self, rsh: &Self, f: F)
    where
        F: Fn(&mut usize, usize, usize) -> (),
    {
        self.pos.unsafe_zip3_bits_in(&rhs.pos, &rsh.pos, &f);
        self.neg.unsafe_zip3_bits_in(&rhs.neg, &rsh.neg, &f);
    }

    pub(crate) fn subset_of(&self, rhs: &Self) -> bool {
        self.pos.subset_of(&rhs.pos) && self.neg.subset_of(&rhs.neg)
    }

    pub(crate) fn difference_switched_self(&self) -> Self {
        let pos = self.pos.zip_bits(&self.neg, |x, y| x & !y);
        let neg = self.neg.zip_bits(&self.pos, |x, y| x & !y);
        Self { pos, neg }
    }

    pub(crate) fn read(&self, index: isize) -> bool {
        if index < 0 {
            self.neg.read(-index as usize - 1)
        } else {
            self.pos.read(index as usize - 1)
        }
    }

    pub(crate) fn set(&mut self, index: isize) {
        if index < 0 {
            self.neg.set(-index as usize - 1)
        } else {
            self.pos.set(index as usize - 1)
        }
    }

    pub(crate) fn unset(&mut self, index: isize) {
        if index < 0 {
            self.neg.unset(-index as usize - 1)
        } else {
            self.pos.unset(index as usize - 1)
        }
    }

    pub(crate) fn variables(&self) -> BitVec<A>
    where
        A: Allocator,
    {
        self.pos.zip_bits(&self.neg, |x, y| x | y)
    }

    pub(crate) fn unsafe_enrich_variables(&self, vrs: &mut BitVec<A>)
    where
        A: Allocator,
    {
        for i in 0..vrs.content.len() {
            vrs.content[i] |= self.pos.content[i] | self.neg.content[i];
        }
    }

    pub(crate) fn unsafe_has_variables(&self, vrs: &BitVec<A>) -> bool {
        (0..vrs.content.len())
            .any(|i| 0 != (self.pos.content[i] | self.neg.content[i]) & vrs.content[i])
    }

    pub(crate) fn disjoint(&self, rhs: &Self) -> bool {
        self.pos.disjoint(&rhs.pos) && self.neg.disjoint(&rhs.neg)
    }

    pub(crate) fn disjoint_switched_self(&self) -> bool {
        self.pos.disjoint(&self.neg)
    }

    pub(crate) fn capacity(&self) -> usize {
        BLOCK_SIZE * self.pos.content.len()
    }

    pub(crate) fn content_length(&self) -> usize {
        self.pos.content.len()
    }

    pub(crate) fn iter_literals(&self) -> impl Iterator<Item = isize> + use<'_, A> {
        iter::chain(
            self.pos.iter_ones().map(|x| x as isize + 1),
            self.neg.iter_ones().map(|x| -(1 + x as isize)),
        )
    }

    pub(crate) fn unsafe_iter_differences<'b>(
        &self,
        rhs: &'b Self,
    ) -> impl Iterator<Item = isize> + use<'_, 'b, A> {
        iter::chain(
            self.pos
                .unsafe_iter_bin_op(&rhs.pos, |x, y| x & !y)
                .map(|x| x as isize + 1),
            self.neg
                .unsafe_iter_bin_op(&rhs.neg, |x, y| x & !y)
                .map(|x| -(1 + x as isize)),
        )
    }

    pub(crate) fn unsafe_symmetry_in(&self, rhs: &Self) -> Option<isize> {
        let (badness, control) = {
            let mut difference = self.unsafe_iter_differences(&rhs);
            (difference.next(), difference.next())
        };
        if control.is_none() {
            return badness.map(|x| if rhs.read(-x) { Some(-x) } else { None })?;
        }
        None
    }

    pub(crate) fn is_null(&self) -> bool {
        self.pos.is_null() && self.neg.is_null()
    }
}

#[derive(Clone)]
pub(crate) struct Clause<A>
where
    A: Allocator + Copy,
{
    pub(crate) pos: BitVec<A>,
    pub(crate) neg: BitVec<A>,
}

impl IterOne {
    fn new(num: usize) -> Self {
        Self { num }
    }
}

impl ExactSizeIterator for IterOne {
    fn len(&self) -> usize {
        self.num.count_ones() as usize
    }
}

impl FusedIterator for IterOne {}

impl Iterator for IterOne {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.num == 0 {
            return None;
        } else {
            let tmp = self.num.trailing_zeros() as usize;
            self.num &= self.num - 1;
            Some(tmp)
        }
    }
}

struct IterOne {
    num: usize,
}

impl<A> BitVec<A>
where
    A: Allocator + Copy,
{
    fn new(len: usize, a: A) -> Self {
        Self {
            ones: OnceCell::new(),
            content: unsafe { Box::new_zeroed_slice_in(len, a).assume_init() },
        }
    }

    fn ones(&self) -> usize {
        *self
            .ones
            .get_or_init(|| self.content.iter().map(|x| x.count_ones()).sum::<u32>() as usize)
    }

    fn is_null(&self) -> bool {
        self.content.iter().all(|&x| x == 0)
    }

    fn unsafe_iter_bin_op<'b, F>(
        &self,
        rhs: &'b Self,
        f: F,
    ) -> impl Iterator<Item = usize> + use<'_, 'b, A, F>
    where
        F: Fn(usize, usize) -> usize,
    {
        iter::zip(&self.content, &rhs.content)
            .enumerate()
            .flat_map(move |(i, (&x, &y))| IterOne::new(f(x, y)).map(move |z| i * BLOCK_SIZE + z))
    }

    fn iter_ones(&self) -> impl Iterator<Item = usize> + use<'_, A> {
        self.content
            .iter()
            .enumerate()
            .flat_map(|(i, &x)| IterOne::new(x).map(move |y| i * BLOCK_SIZE + y))
    }

    fn zip_bits<F>(&self, rhs: &Self, f: F) -> Self
    where
        F: Fn(usize, usize) -> usize,
    {
        let mut res = Self::new(self.content.len(), *Box::allocator(&self.content));
        res.unsafe_zip_bits_in(rhs, |x, y| *x = f(*x, y));
        res
    }

    fn unsafe_zip_bits_in<F>(&mut self, rhs: &Self, f: F)
    where
        F: Fn(&mut usize, usize) -> (),
    {
        self.ones.take();
        for i in 0..self.content.len() {
            f(&mut self.content[i], rhs.content[i])
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

    fn subset_of(&self, rhs: &Self) -> bool {
        iter::zip(&self.content, &rhs.content).all(|(&x, &y)| x & !y == 0)
    }

    fn disjoint(&self, rhs: &Self) -> bool {
        iter::zip(&self.content, &rhs.content).all(|(&x, &y)| x & y == 0)
    }
}

#[derive(Clone)]
pub(crate) struct BitVec<A>
where
    A: Allocator + Copy,
{
    pub(crate) ones: OnceCell<usize>,
    pub(crate) content: Box<[usize], A>,
}
