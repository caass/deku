mod bool;
mod nonzero;
mod option;
mod primitive;
mod slice;
mod tuple;
mod unit;
mod vec;

#[cfg(feature = "std")]
mod cow;

#[cfg(feature = "std")]
mod cstring;

#[cfg(feature = "std")]
mod hashmap;

#[cfg(feature = "std")]
mod hashset;

#[cfg(feature = "std")]
mod ipaddr;

#[cfg(feature = "alloc")]
mod boxed;

#[cfg(test)]
mod test_common {
    use bitvec::{array::BitArray, bitarr, prelude::Msb0, slice::BitSlice};
    use once_cell::sync::Lazy;

    use crate::ctx::{Endian, Limit};

    pub(super) struct Options<T, Predicate>
    where
        Predicate: FnMut(&T) -> bool,
    {
        pub(super) endian: Endian,
        pub(super) bit_size: Option<usize>,
        pub(super) limit: Limit<T, Predicate>,
    }

    impl<T, Predicate> Options<T, Predicate>
    where
        Predicate: FnMut(&T) -> bool,
    {
        pub(super) fn little_endian() -> Self {
            Self {
                endian: Endian::Little,
                bit_size: None,
                limit: Limit::End,
            }
        }

        pub(super) fn big_endian() -> Self {
            Self {
                endian: Endian::Big,
                bit_size: None,
                limit: Limit::End,
            }
        }

        pub(super) fn with_bit_size(mut self, bit_size: usize) -> Self {
            self.bit_size = Some(bit_size);
            self
        }

        pub(super) fn with_limit(mut self, limit: impl Into<Limit<T, Predicate>>) -> Self {
            self.limit = limit.into();
            self
        }
    }

    static DEFAULT_REST_BYTES: &[u8] = &[];
    static DEFAULT_REST_BITS: Lazy<BitArray<[u8; 0], Msb0>> = Lazy::new(|| bitarr![u8, Msb0;]);

    pub(super) struct ReadOutput<'a, T> {
        pub(super) value: T,
        pub(super) rest_bits: &'a BitSlice<u8, Msb0>,
        pub(super) rest_bytes: &'a [u8],
    }

    impl<'a, T> ReadOutput<'a, T> {
        pub(super) fn expected(value: T) -> Self {
            Self {
                value,
                rest_bits: DEFAULT_REST_BITS.as_bitslice(),
                rest_bytes: DEFAULT_REST_BYTES,
            }
        }

        pub(super) fn with_rest_bits(mut self, rest_bits: &'a BitSlice<u8, Msb0>) -> Self {
            self.rest_bits = rest_bits;
            self
        }

        pub(super) fn with_rest_bytes(mut self, rest_bytes: &'a [u8]) -> Self {
            self.rest_bytes = rest_bytes;
            self
        }
    }
}
