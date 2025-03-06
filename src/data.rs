use core::alloc::Allocator;
use core::cell::OnceCell;
use core::iter::{self, FusedIterator};
use core::usize;

const BLOCK_SIZE: usize = usize::BITS as usize;
const BLOCK_BYTE: usize = size_of::<usize>();

pub(crate) const fn bytes_needed(vrs: usize) -> usize {
    2 * blocks_needed(vrs) * BLOCK_BYTE
}

pub(crate) const fn blocks_needed(vrs: usize) -> usize {
    vrs / BLOCK_SIZE + (vrs % BLOCK_SIZE > 0) as usize
}

impl<A> Clause<A>
where
    A: Allocator + Copy,
{
    pub(crate) fn new(blocks: usize, a: A) -> Self
    where
        A: Allocator,
    {
        Self(BitVec::new(blocks * 2, a))
    }

    pub(crate) fn create_sibling(&self) -> Self {
        Self(self.0.create_sibling())
    }

    pub(crate) fn len(&self) -> usize {
        self.0.ones()
    }

    pub(crate) fn is_null(&self) -> bool {
        self.0.is_null()
    }

    const fn half_cap(&self) -> usize {
        self.0.content.len() / 2
    }

    const fn half_idx(&self, i: usize) -> usize {
        self.half_cap() + i
    }

    pub(crate) fn evil_twin(&self) -> Self {
        let mut res = self.create_sibling();
        (0..self.half_cap()).for_each(|i| {
            let j = self.half_idx(i);
            res.0.content[i] = self.0.content[j];
            res.0.content[j] = self.0.content[i];
        });
        res
    }

    fn zip_clause<F>(&self, rhs: &Self, f: F) -> Self
    where
        F: Fn(usize, usize) -> usize,
    {
        Self(BitVec::zip_bits(&self.0, &rhs.0, f))
    }

    fn unsafe_zip_clause_in<F>(&mut self, rhs: &Self, f: F)
    where
        F: Fn(&mut usize, usize) -> (),
    {
        BitVec::unsafe_zip_bits_in(&mut self.0, &rhs.0, f);
    }

    pub(crate) fn union_in(&mut self, rhs: &Self) {
        self.unsafe_zip_clause_in(rhs, |x, y| *x |= y);
    }

    pub(crate) fn difference_in(&mut self, rhs: &Self) {
        self.unsafe_zip_clause_in(rhs, |x, y| *x &= !y);
    }

    pub(crate) fn union_with_joined_in(&mut self, rhs: &Self, rsh: &Self) {
        self.unsafe_zip3_clause_in(rhs, rsh, |x, y, z| *x |= y & z);
    }

    fn unsafe_zip3_clause_in<F>(&mut self, rhs: &Self, rsh: &Self, f: F)
    where
        F: Fn(&mut usize, usize, usize) -> (),
    {
        BitVec::unsafe_zip3_bits_in(&mut self.0, &rhs.0, &rsh.0, f);
    }

    pub(crate) fn subset_of(&self, rhs: &Self) -> bool {
        BitVec::subset_of(&self.0, &rhs.0)
    }

    pub(crate) fn difference_switched_self(&mut self) {
        (0..self.half_cap()).for_each(|i| {
            let j = self.half_idx(i);
            let (a, b) = (self.0.content[i], self.0.content[j]);
            self.0.content[i] = a & !b;
            self.0.content[j] = b & !a;
        });
    }

    const fn true_idx(&self, index: isize) -> usize {
        if index < 0 {
            return -index as usize - 1 + self.half_cap() * BLOCK_SIZE;
        }
        index as usize - 1
    }

    pub(crate) const fn read(&self, index: isize) -> bool {
        self.0.read(self.true_idx(index))
    }

    pub(crate) fn set(&mut self, index: isize) {
        self.0.set(self.true_idx(index));
    }

    pub(crate) fn unset(&mut self, index: isize) {
        self.0.unset(self.true_idx(index));
    }

    pub(crate) fn variables(&self) -> BitVec<A>
    where
        A: Allocator,
    {
        let mut res = BitVec::new(self.half_cap(), *Box::allocator(&self.0.content));
        (0..self.half_cap())
            .for_each(|i| res.content[i] = self.0.content[i] | self.0.content[self.half_idx(i)]);
        res
    }

    pub(crate) fn unsafe_enrich_variables(&self, vrs: &mut BitVec<A>)
    where
        A: Allocator,
    {
        (0..vrs.content.len())
            .for_each(|i| vrs.content[i] |= self.0.content[i] | self.0.content[self.half_idx(i)]);
    }

    pub(crate) fn unsafe_has_variables(&self, vrs: &BitVec<A>) -> bool {
        (0..vrs.content.len())
            .any(|i| (self.0.content[i] | self.0.content[self.half_idx(i)]) & vrs.content[i] != 0)
    }

    pub(crate) fn disjoint(&self, rhs: &Self) -> bool {
        BitVec::disjoint(&self.0, &rhs.0)
    }

    pub(crate) fn disjoint_switched_self(&self) -> bool {
        (0..self.half_cap()).all(|i| self.0.content[i] & self.0.content[self.half_idx(i)] == 0)
    }

    pub(crate) fn iter_literals(&self) -> impl Iterator<Item = isize> + use<'_, A> {
        iter::chain(
            iter_ones(self.0.content[..self.half_cap()].iter().copied()).map(|x| x as isize + 1),
            iter_ones(self.0.content[self.half_cap()..].iter().copied()).map(|x| -(1 + x as isize)),
        )
    }

    pub(crate) fn unsafe_iter_differences<'b>(
        &self,
        rhs: &'b Self,
    ) -> impl Iterator<Item = isize> + use<'_, 'b, A> {
        iter::chain(
            iter_ones(
                iter::zip(
                    &self.0.content[..self.half_cap()],
                    &rhs.0.content[..self.half_cap()],
                )
                .map(|(&x, &y)| x & !y),
            )
            .map(|x| x as isize + 1),
            iter_ones(
                iter::zip(
                    &self.0.content[self.half_cap()..],
                    &rhs.0.content[self.half_cap()..],
                )
                .map(|(&x, &y)| x & !y),
            )
            .map(|x| -(x as isize + 1)),
        )
    }

    pub(crate) fn symmetry_in(&self, rhs: &Self) -> Option<isize> {
        let mut difference = self.unsafe_iter_differences(&rhs);

        if let Some(x) = difference.next() {
            let badness = -x;
            if rhs.read(badness) && difference.next().is_none() {
                return Some(badness);
            }
        }
        None
    }
}

#[derive(Clone)]
pub(crate) struct Clause<A>(BitVec<A>)
where
    A: Allocator + Copy;

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
        }
        let tmp = self.num.trailing_zeros() as usize;
        self.num &= self.num - 1;
        Some(tmp)
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

    fn create_sibling(&self) -> Self {
        Self {
            ones: OnceCell::new(),
            content: unsafe {
                Box::new_zeroed_slice_in(self.content.len(), *Box::allocator(&self.content))
                    .assume_init()
            },
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

    fn zip_bits<F>(&self, rhs: &Self, f: F) -> Self
    where
        F: Fn(usize, usize) -> usize,
    {
        let mut res = Self::new(self.content.len(), *Box::allocator(&self.content));
        (0..self.content.len()).for_each(|i| res.content[i] = f(self.content[i], rhs.content[i]));
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

    const fn read(&self, index: usize) -> bool {
        self.content[index / BLOCK_SIZE] & 1 << (index % BLOCK_SIZE) != 0
    }

    fn subset_of(&self, rhs: &Self) -> bool {
        iter::zip(&self.content, &rhs.content).all(|(&x, &y)| x & !y == 0)
    }

    fn disjoint(&self, rhs: &Self) -> bool {
        iter::zip(&self.content, &rhs.content).all(|(&x, &y)| x & y == 0)
    }
}

fn iter_ones<I>(iterator: I) -> impl Iterator<Item = usize>
where
    I: Iterator<Item = usize>,
{
    iterator
        .enumerate()
        .flat_map(|(i, x)| IterOne::new(x).map(move |y| i * BLOCK_SIZE + y))
}

#[derive(Clone)]
pub(crate) struct BitVec<A>
where
    A: Allocator + Copy,
{
    pub(crate) ones: OnceCell<usize>,
    pub(crate) content: Box<[usize], A>,
}
