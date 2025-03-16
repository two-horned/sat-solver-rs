use core::iter::{ExactSizeIterator, FusedIterator};

pub(crate) const BITS: usize = usize::BITS as usize;
pub(crate) const MASK: usize = BITS - 1;
pub(crate) const POWR: usize = MASK.trailing_ones() as usize;

pub(crate) const fn indices(index: usize) -> (usize, usize) {
    (index >> POWR, index & MASK)
}

pub(crate) const fn integers_needed(bits: usize) -> usize {
    bits + MASK >> POWR
}

macro_rules! impl_bit_manipulation {
    ($integer:ty) => {
        impl Bits for $integer {
            fn read(&self, i: usize) -> bool {
                self >> i & 1 != 0
            }
            fn write(&mut self, i: usize, value: bool) {
                if value {
                    self.set(i);
                } else {
                    self.unset(i);
                }
            }
            fn set(&mut self, i: usize) {
                *self |= 1 << i;
            }
            fn unset(&mut self, i: usize) {
                *self &= !(1 << i);
            }
            fn flip(&mut self, i: usize) {
                *self ^= 1 << i;
            }
        }
    };
}

pub(crate) trait Bits {
    fn read(&self, i: usize) -> bool;
    fn write(&mut self, i: usize, value: bool);
    fn set(&mut self, i: usize);
    fn unset(&mut self, i: usize);
    fn flip(&mut self, i: usize);
}

impl_bit_manipulation!(usize);

macro_rules! uint_iter_ones {
    (
        $uint:ty,
        $IterOnes:ident
        ) => {
        impl DoubleEndedIterator for $IterOnes {
            fn next_back(&mut self) -> Option<Self::Item> {
                if self.0 == 0 {
                    return None;
                }
                let res = self.0.leading_zeros() as usize;
                self.0 ^= 1 << res;
                Some(res)
            }
        }

        impl ExactSizeIterator for $IterOnes {
            fn len(&self) -> usize {
                self.0.count_ones() as usize
            }
        }

        impl FusedIterator for $IterOnes {}

        impl Iterator for $IterOnes {
            type Item = usize;

            pub(crate) fn next(&mut self) -> Option<Self::Item> {
                if self.0 == 0 {
                    return None;
                }

                let res = self.0.trailing_zeros() as usize;
                self.0 &= self.0 - 1;
                Some(res)
            }
        }

        pub(crate) struct $IterOnes($uint);
    };
}

macro_rules! uint_slice_iter_ones {
    (
        $uint:ty,
        $IterOnesSlice:ident
    ) => {
        impl $IterOnesSlice<'_> {
            pub(crate) const fn new<'a>(slice: &'a [$uint]) -> $IterOnesSlice<'a> {
                $IterOnesSlice(0, 0, slice)
            }
        }

        impl ExactSizeIterator for $IterOnesSlice<'_> {
            fn len(&self) -> usize {
                self.0.count_ones() as usize
                    + self
                        .2
                        .iter()
                        .map(|x| x.count_ones() as usize)
                        .sum::<usize>()
            }
        }

        impl FusedIterator for $IterOnesSlice<'_> {}

        impl Iterator for $IterOnesSlice<'_> {
            type Item = usize;

            fn next(&mut self) -> Option<Self::Item> {
                if self.0 == 0 {
                    if self.2.is_empty() {
                        return None;
                    }
                    self.0 = self.2[0];
                    self.1 += BITS;
                    self.2 = &self.2[1..];
                }

                let res = self.0.trailing_zeros() as usize + self.1;
                self.0 &= self.0 - 1;
                Some(res)
            }
        }

        pub(crate) struct $IterOnesSlice<'a>($uint, $uint, &'a [$uint]);
    };
}

uint_slice_iter_ones!(usize, IterOnesSliceUsize);
