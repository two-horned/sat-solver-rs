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
        impl Bits for [$integer] {
            fn read(&self, i: usize) -> bool {
                let (i, j) = indices(i);
                self[i].read(j)
            }
            fn write(&mut self, i: usize, value: bool) {
                let (i, j) = indices(i);
                self[i].write(j, value);
            }

            fn set(&mut self, i: usize) {
                let (i, j) = indices(i);
                self[i].set(j);
            }
            fn unset(&mut self, i: usize) {
                let (i, j) = indices(i);
                self[i].unset(j);
            }
            fn flip(&mut self, i: usize) {
                let (i, j) = indices(i);
                self[i].flip(j);
            }
        }

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

// macro_rules! uint_iter_ones {
//     (
//         $uint:ty,
//         $IterOnes:ident
//         ) => {
//         impl DoubleEndedIterator for $IterOnes {
//             fn next_back(&mut self) -> Option<Self::Item> {
//                 if self.0 == 0 {
//                     return None;
//                 }
//                 let res = self.0.leading_zeros() as usize;
//                 self.0 ^= 1 << res;
//                 Some(res)
//             }
//         }

//         impl ExactSizeIterator for $IterOnes {
//             fn len(&self) -> usize {
//                 self.0.count_ones() as usize
//             }
//         }

//         impl FusedIterator for $IterOnes {}

//         impl Iterator for $IterOnes {
//             type Item = usize;

//             pub(crate) fn next(&mut self) -> Option<Self::Item> {
//                 if self.0 == 0 {
//                     return None;
//                 }

//                 let res = self.0.trailing_zeros() as usize;
//                 self.0 &= self.0 - 1;
//                 Some(res)
//             }
//         }

//         pub(crate) struct $IterOnes($uint);
//     };
// }

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
                while self.0 == 0 {
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

macro_rules! uint_iterator_iter_ones {
    (
        $uint:ty,
        $IterOnesIterator:ident
    ) => {
        impl<I: Iterator<Item = $uint>> $IterOnesIterator<I> {
            pub(crate) const fn new(iterator: I) -> $IterOnesIterator<I> {
                $IterOnesIterator(0, 0, iterator)
            }
        }

        impl<I> FusedIterator for $IterOnesIterator<I> where
            I: Iterator<Item = $uint> + FusedIterator
        {
        }

        impl<I: Iterator<Item = $uint>> Iterator for $IterOnesIterator<I> {
            type Item = usize;

            fn next(&mut self) -> Option<Self::Item> {
                if self.0 == 0 {
                    let x = self.2.next()?;
                    self.0 = x;
                    self.1 += BITS;
                }

                let res = self.0.trailing_zeros() as usize + self.1;
                self.0 &= self.0 - 1;
                Some(res)
            }
        }

        pub(crate) struct $IterOnesIterator<I: Iterator<Item = $uint>>($uint, $uint, I);
    };
}

uint_iterator_iter_ones!(usize, IterOnesIteratorUsize);

pub(crate) const fn iter_ones_slice_usize(slice: &[usize]) -> IterOnesSliceUsize {
    IterOnesSliceUsize::new(slice)
}
