use std::collections::HashSet;
use std::hash::{BuildHasher, Hash};

use crate::writer::Writer;
use no_std_io::io::{Read, Write};

use crate::ctx::*;
use crate::{DekuError, DekuReader, DekuWriter};

/// Read `T`s into a hashset until a given predicate returns true
/// * `capacity` - an optional capacity to pre-allocate the hashset with
/// * `ctx` - The context required by `T`. It will be passed to every `T` when constructing.
/// * `predicate` - the predicate that decides when to stop reading `T`s
/// The predicate takes two parameters: the number of bits that have been read so far,
/// and a borrow of the latest value to have been read. It should return `true` if reading
/// should now stop, and `false` otherwise
#[allow(clippy::type_complexity)]
fn from_reader_with_ctx_hashset_with_predicate<'a, T, S, Ctx, Predicate, R: Read>(
    reader: &mut crate::reader::Reader<R>,
    capacity: Option<usize>,
    ctx: Ctx,
    mut predicate: Predicate,
) -> Result<HashSet<T, S>, DekuError>
where
    T: DekuReader<'a, Ctx> + Eq + Hash,
    S: BuildHasher + Default,
    Ctx: Copy,
    Predicate: FnMut(usize, &T) -> bool,
{
    let mut res = HashSet::with_capacity_and_hasher(capacity.unwrap_or(0), S::default());

    let mut found_predicate = false;
    let orig_bits_read = reader.bits_read;

    while !found_predicate {
        let val = <T>::from_reader_with_ctx(reader, ctx)?;
        found_predicate = predicate(reader.bits_read - orig_bits_read, &val);
        res.insert(val);
    }

    Ok(res)
}

fn from_reader_with_ctx_hashset_to_end<'a, T, S, Ctx, R: Read>(
    reader: &mut crate::reader::Reader<R>,
    capacity: Option<usize>,
    ctx: Ctx,
) -> Result<HashSet<T, S>, DekuError>
where
    T: DekuReader<'a, Ctx> + Eq + Hash,
    S: BuildHasher + Default,
    Ctx: Copy,
{
    let mut res = HashSet::with_capacity_and_hasher(capacity.unwrap_or(0), S::default());

    loop {
        if reader.end() {
            break;
        }
        let val = <T>::from_reader_with_ctx(reader, ctx)?;
        res.insert(val);
    }

    Ok(res)
}

impl<'a, T, S, Ctx, Predicate> DekuReader<'a, (Limit<T, Predicate>, Ctx)> for HashSet<T, S>
where
    T: DekuReader<'a, Ctx> + Eq + Hash,
    S: BuildHasher + Default,
    Ctx: Copy,
    Predicate: FnMut(&T) -> bool,
{
    /// Read `T`s until the given limit
    /// * `limit` - the limiting factor on the amount of `T`s to read
    /// * `inner_ctx` - The context required by `T`. It will be passed to every `T`s when constructing.
    /// # Examples
    /// ```rust
    /// # use deku::ctx::*;
    /// # use deku::DekuReader;
    /// # use std::collections::HashSet;
    /// # use std::io::Cursor;
    /// let mut input = Cursor::new(vec![1u8, 2, 3, 4]);
    /// let expected: HashSet<u32> = vec![0x04030201].into_iter().collect();
    /// let mut reader = deku::reader::Reader::new(&mut input);
    /// let set = HashSet::<u32>::from_reader_with_ctx(&mut reader, (1.into(), Endian::Little)).unwrap();
    /// assert_eq!(expected, set)
    /// ```
    fn from_reader_with_ctx<R: Read>(
        reader: &mut crate::reader::Reader<R>,
        (limit, inner_ctx): (Limit<T, Predicate>, Ctx),
    ) -> Result<Self, DekuError>
    where
        Self: Sized,
    {
        match limit {
            // Read a given count of elements
            Limit::Count(mut count) => {
                // Handle the trivial case of reading an empty hashset
                if count == 0 {
                    return Ok(HashSet::<T, S>::default());
                }

                // Otherwise, read until we have read `count` elements
                from_reader_with_ctx_hashset_with_predicate(
                    reader,
                    Some(count),
                    inner_ctx,
                    move |_, _| {
                        count -= 1;
                        count == 0
                    },
                )
            }

            // Read until a given predicate returns true
            Limit::Until(mut predicate, _) => from_reader_with_ctx_hashset_with_predicate(
                reader,
                None,
                inner_ctx,
                move |_, value| predicate(value),
            ),

            // Read until a given quantity of bits have been read
            Limit::BitSize(size) => {
                let bit_size = size.0;

                // Handle the trivial case of reading an empty hashset
                if bit_size == 0 {
                    return Ok(HashSet::<T, S>::default());
                }

                from_reader_with_ctx_hashset_with_predicate(
                    reader,
                    None,
                    inner_ctx,
                    move |read_bits, _| read_bits == bit_size,
                )
            }

            // Read until a given quantity of bytes have been read
            Limit::ByteSize(size) => {
                let bit_size = size.0 * 8;

                // Handle the trivial case of reading an empty hashset
                if bit_size == 0 {
                    return Ok(HashSet::<T, S>::default());
                }

                from_reader_with_ctx_hashset_with_predicate(
                    reader,
                    None,
                    inner_ctx,
                    move |read_bits, _| read_bits == bit_size,
                )
            }

            // Read until `reader.end()` is true
            Limit::End => from_reader_with_ctx_hashset_to_end(reader, None, inner_ctx),
        }
    }
}

impl<'a, T: DekuReader<'a> + Eq + Hash, S: BuildHasher + Default, Predicate: FnMut(&T) -> bool>
    DekuReader<'a, Limit<T, Predicate>> for HashSet<T, S>
{
    /// Read `T`s until the given limit from input for types which don't require context.
    fn from_reader_with_ctx<R: Read>(
        reader: &mut crate::reader::Reader<R>,
        limit: Limit<T, Predicate>,
    ) -> Result<Self, DekuError>
    where
        Self: Sized,
    {
        Self::from_reader_with_ctx(reader, (limit, ()))
    }
}

impl<T: DekuWriter<Ctx>, S, Ctx: Copy> DekuWriter<Ctx> for HashSet<T, S> {
    /// Write all `T`s in a `HashSet` to bits.
    /// * **inner_ctx** - The context required by `T`.
    /// Note: depending on the Hasher `S`, the order in which the `T`'s are
    /// written may change between executions. Use a deterministic Hasher for your HashSet
    /// instead of the default RandomState hasher if you don't want the order written to change.
    /// # Examples
    /// ```rust
    /// # use deku::{ctx::Endian, DekuWriter};
    /// # use deku::writer::Writer;
    /// # use deku::bitvec::{Msb0, bitvec};
    /// # use std::collections::HashSet;
    /// let mut out_buf = vec![];
    /// let mut writer = Writer::new(&mut out_buf);
    /// let set: HashSet<u8> = vec![1].into_iter().collect();
    /// set.to_writer(&mut writer, Endian::Big).unwrap();
    /// assert_eq!(out_buf, vec![1]);
    /// ```
    fn to_writer<W: Write>(&self, writer: &mut Writer<W>, inner_ctx: Ctx) -> Result<(), DekuError> {
        for v in self {
            v.to_writer(writer, inner_ctx)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::bitvec::{bitarr, Msb0};
    use no_std_io::io::Cursor;
    use rstest::rstest;

    // Note: due to https://github.com/rust-lang/rust/blob/a94483a5f2bae907bc898fc7a8d9cc87db47b693/library/std/src/collections/hash/set.rs#L1039-L1050
    // we use the regular hash set as it's more convenient. It should only slow us down a little in testing.
    use std::collections::HashSet as FxHashSet;

    use crate::reader::Reader;
    use crate::impls::test_common::*;

    use super::*;

    #[rstest]
    #[case::count_0(
        [0xAA],
        Ctx::little_endian().with_bit_size(8).with_limit(0),
        ReadOutput::expected([]).with_rest_bytes(&[0xaa])
    )]
    #[case::count_1(
        [0xAA, 0xBB],
        Ctx::little_endian().with_bit_size(8).with_limit(1),
        ReadOutput::expected([0xAA]).with_rest_bytes(&[0xbb])
    )]
    #[case::count_2(
        [0xAA, 0xBB, 0xCC],
        Ctx::little_endian().with_bit_size(8).with_limit(2),
        ReadOutput::expected([0xAA, 0xBB]).with_rest_bytes(&[0xcc])
    )]
    #[case::until_null(
        [0xAA, 0, 0xBB],
        Ctx::little_endian().with_limit(|v: &u8| *v == 0u8),
        ReadOutput::expected([0xAA, 0]).with_rest_bytes(&[0xbb])
    )]
    #[case::until_empty_bits(
        [0xAA, 0xBB],
        Ctx::little_endian().with_limit(BitSize(0)),
        ReadOutput::expected([]).with_rest_bytes(&[0xaa, 0xbb])
    )]
    #[case::until_empty_bytes(
        [0xAA, 0xBB],
        Ctx::little_endian().with_limit(ByteSize(0)),
        ReadOutput::expected([]).with_rest_bytes(&[0xaa, 0xbb])
    )]
    #[case::until_bits(
        [0xAA, 0xBB],
        Ctx::little_endian().with_limit(BitSize(8)),
        ReadOutput::expected([0xAA]).with_rest_bytes(&[0xbb])
    )]
    #[case::read_all(
        [0xAA, 0xBB],
        Ctx::little_endian().with_limit(Limit::end()),
        ReadOutput::expected([0xAA, 0xBB])
    )]
    #[case::until_bytes(
        [0xAA, 0xBB],
        Ctx::little_endian().with_limit(ByteSize(1)),
        ReadOutput::expected([0xAA]).with_rest_bytes(&[0xbb])
    )]
    #[case::until_count(
        [0xAA, 0xBB], 
        Ctx::little_endian().with_limit(1),
        ReadOutput::expected([0xAA]).with_rest_bytes(&[0xbb])
    )]
    #[case::bits_6(
        [0b0110_1001, 0b1110_1001],
        Ctx::little_endian().with_bit_size(6).with_limit(2),
        ReadOutput::expected([0b00_011010, 0b00_011110]).with_rest_bits(bitarr![u8, Msb0; 1, 0, 0, 1])
    )]
    #[should_panic(expected = "Parse(\"too much data: container of 8 bits cannot hold 9 bits\")")]
    #[case::not_enough_data(
        [],
        Ctx::little_endian().with_bit_size(9).with_limit(1),
        ReadOutput::should_panic()
    )]
    #[should_panic(expected = "Parse(\"too much data: container of 8 bits cannot hold 9 bits\")")]
    #[case::not_enough_data(
        [0xAA],
        Ctx::little_endian().with_bit_size(9).with_limit(1),
        ReadOutput::should_panic()
    )]
    #[should_panic(expected = "Incomplete(NeedSize { bits: 8 })")]
    #[case::not_enough_data(
        [0xAA],
        Ctx::little_endian().with_bit_size(8).with_limit(2),
        ReadOutput::should_panic()
    )]
    #[should_panic(expected = "Incomplete(NeedSize { bits: 8 })")]
    #[case::not_enough_data_until(
        [0xAA],
        Ctx::little_endian().with_bit_size(8).with_limit(|_: &u8| false),
        ReadOutput::should_panic()
    )]
    #[should_panic(expected = "Incomplete(NeedSize { bits: 8 })")]
    #[case::not_enough_data_bits(
        [0xAA],
        Ctx::little_endian().with_bit_size(8).with_limit(BitSize(16)),
        ReadOutput::should_panic()
    )]
    #[should_panic(expected = "Parse(\"too much data: container of 8 bits cannot hold 9 bits\")")]
    #[case::too_much_data(
        [0xAA, 0xBB],
        Ctx::little_endian().with_bit_size(9).with_limit(1),
        ReadOutput::should_panic()
    )]
    fn test_hashset_read<const BITS: usize>(
        #[case] input: impl AsRef<[u8]>,
        #[case] ctx: Ctx<u8, impl FnMut(&u8) -> bool + Copy>,
        #[case] expected: ReadOutput<BITS, FxHashSet<u8>>,
    ) {
        let input = input.as_ref();

        let mut cursor = Cursor::new(input);
        let mut reader = Reader::new(&mut cursor);

        let res_read = match ctx.bit_size {
            Some(bit_size) => FxHashSet::<u8>::from_reader_with_ctx(
                &mut reader,
                (ctx.limit, (ctx.endian, BitSize(bit_size))),
            )
            .unwrap(),
            None => FxHashSet::<u8>::from_reader_with_ctx(&mut reader, (ctx.limit, (ctx.endian))).unwrap(),
        };
        assert_eq!(expected.value, res_read);
        assert_eq!(
            reader.rest(),
            expected.rest_bits.iter().by_vals().collect::<Vec<bool>>()
        );
        let mut buf = vec![];
        cursor.read_to_end(&mut buf).unwrap();
        assert_eq!(expected.rest_bytes, buf);
    }

    #[rstest(input, endian, expected,
        case::normal(vec![0xAABB, 0xCCDD].into_iter().collect(), Endian::Little, vec![0xDD, 0xCC, 0xBB, 0xAA]),
    )]
    fn test_hashset_write(input: FxHashSet<u16>, endian: Endian, expected: Vec<u8>) {
        let mut writer = Writer::new(vec![]);
        input.to_writer(&mut writer, endian).unwrap();
        assert_eq!(expected, writer.inner);
    }

    // Note: These tests also exist in boxed.rs
    #[rstest]
    #[case::normal_le(
        [0xAA, 0xBB, 0xCC, 0xDD],
        Ctx::little_endian().with_bit_size(16).with_limit(2),
        ReadOutput::expected([0xBBAA, 0xDDCC]),
        WriteOutput::expected([0xCC, 0xDD, 0xAA, 0xBB])
    )]
    #[case::normal_be(
        [0xAA, 0xBB, 0xCC, 0xDD],
        Ctx::big_endian().with_bit_size(16).with_limit(2),
        ReadOutput::expected([0xAABB, 0xCCDD]),
        WriteOutput::expected([0xCC, 0xDD, 0xAA, 0xBB])
    )]
    #[case::predicate_le(
        [0xAA, 0xBB, 0xCC, 0xDD],
        Ctx::little_endian().with_bit_size(16).with_limit(|v: &u16| *v == 0xBBAA),
        ReadOutput::expected([0xBBAA]).with_rest_bytes(&[0xcc, 0xdd]),
        WriteOutput::expected([0xAA, 0xBB])
    )]
    #[case::predicate_be(
        [0xAA, 0xBB, 0xCC, 0xDD],
        Ctx::big_endian().with_bit_size(16).with_limit(|v: &u16| *v == 0xAABB),
        ReadOutput::expected([0xAABB]).with_rest_bytes(&[0xcc, 0xdd]),
        WriteOutput::expected([0xAA, 0xBB])
    )]
    #[case::bytes_le(
        [0xAA, 0xBB, 0xCC, 0xDD],
        Ctx::little_endian().with_bit_size(16).with_limit(BitSize(16)),
        ReadOutput::expected([0xBBAA]).with_rest_bytes(&[0xcc, 0xdd]),
        WriteOutput::expected([0xAA, 0xBB])
    )]
    #[case::bytes_be(
        [0xAA, 0xBB, 0xCC, 0xDD],
        Ctx::big_endian().with_bit_size(16).with_limit(BitSize(16)),
        ReadOutput::expected([0xAABB]).with_rest_bytes(&[0xcc, 0xdd]),
        WriteOutput::expected(vec![0xAA, 0xBB])
    )]
    fn test_hashset_read_write<const BITS: usize>(
        #[case] input: impl AsRef<[u8]>,
        #[case] ctx: Ctx<u16, impl FnMut(&u16) -> bool + Copy>,
        #[case] expected: ReadOutput<BITS, FxHashSet<u16>>,
        #[case] expected_write: WriteOutput
    ) {
        let input = input.as_ref();

        // Unwrap here because all test cases are `Some`.
        let bit_size = ctx.bit_size.unwrap();

        let mut cursor = Cursor::new(input);
        let mut reader = Reader::new(&mut cursor);
        let res_read = FxHashSet::<u16>::from_reader_with_ctx(
            &mut reader,
            (ctx.limit, (ctx.endian, BitSize(bit_size))),
        )
        .unwrap();
        assert_eq!(expected.value, res_read);
        assert_eq!(
            reader.rest(),
            expected.rest_bits.iter().by_vals().collect::<Vec<bool>>()
        );
        let mut buf = vec![];
        cursor.read_to_end(&mut buf).unwrap();
        assert_eq!(expected.rest_bytes, buf);

        let mut writer = Writer::new(vec![]);
        res_read
            .to_writer(&mut writer, (ctx.endian, BitSize(bit_size)))
            .unwrap();
        assert_eq!(expected_write, writer.inner);
    }
}
