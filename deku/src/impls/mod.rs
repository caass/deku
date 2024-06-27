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
    use bitvec::prelude::{bitarr, BitArray, Msb0};

    use crate::ctx::{Endian, Limit};

    #[derive(Debug)]
    pub(super) struct Ctx<T, Predicate = fn(&T) -> bool>
    where
        Predicate: FnMut(&T) -> bool,
    {
        pub(super) endian: Endian,
        pub(super) bit_size: Option<usize>,
        pub(super) limit: Limit<T, Predicate>,
    }

    impl<T, Predicate> Default for Ctx<T, Predicate>
    where
        Predicate: FnMut(&T) -> bool,
    {
        fn default() -> Self {
            Self {
                endian: Endian::default(),
                bit_size: None,
                limit: Limit::End,
            }
        }
    }

    impl<T, Predicate> Ctx<T, Predicate>
    where
        Predicate: FnMut(&T) -> bool,
    {
        pub(super) fn little_endian() -> Self {
            Self {
                endian: Endian::Little,
                ..Default::default()
            }
        }

        pub(super) fn big_endian() -> Self {
            Self {
                endian: Endian::Big,
                ..Default::default()
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

    pub(super) struct ReadOutput<'a, const BITS: usize, T> {
        value: Option<T>,
        pub(super) rest_bits: BitArray<[u8; BITS], Msb0>,
        pub(super) rest_bytes: &'a [u8],
    }

    impl<'a, T: Default> Default for ReadOutput<'a, 0, T> {
        fn default() -> Self {
            Self {
                value: Some(T::default()),
                rest_bits: bitarr![u8, Msb0;],
                rest_bytes: DEFAULT_REST_BYTES,
            }
        }
    }

    impl<'a, T> ReadOutput<'a, 0, T> {
        pub(super) fn expected(value: impl Into<T>) -> Self {
            Self {
                value: Some(value.into()),
                rest_bits: bitarr![u8, Msb0;],
                rest_bytes: DEFAULT_REST_BYTES,
            }
        }

        pub(super) fn should_panic() -> Self {
            Self {
                value: None,
                rest_bits: bitarr![u8, Msb0;],
                rest_bytes: DEFAULT_REST_BYTES,
            }
        }

        pub(super) fn with_rest_bits<const BITS: usize>(
            self,
            rest_bits: BitArray<[u8; BITS], Msb0>,
        ) -> ReadOutput<'a, BITS, T> {
            ReadOutput {
                value: self.value,
                rest_bits,
                rest_bytes: self.rest_bytes,
            }
        }
    }

    impl<'a, const BITS: usize, T> ReadOutput<'a, BITS, T> {
        pub(super) fn with_rest_bytes(mut self, rest_bytes: &'a [u8]) -> Self {
            self.rest_bytes = rest_bytes;
            self
        }

        pub(super) fn value(&self) -> &T {
            self.value
                .as_ref()
                .expect("Attempted to read value when panic was expected")
        }
    }

    #[derive(Default, Debug)]
    pub(super) struct WriteOutput(pub Vec<u8>);

    impl WriteOutput {
        pub(super) fn should_panic() -> Self {
            Self::default()
        }

        pub(super) fn empty() -> Self {
            Self::default()
        }

        pub(super) fn expected(expected: impl Into<Vec<u8>>) -> Self {
            Self(expected.into())
        }
    }

    impl PartialEq<Vec<u8>> for WriteOutput {
        fn eq(&self, other: &Vec<u8>) -> bool {
            self.0.eq(other)
        }
    }
}
