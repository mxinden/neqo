// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::fmt::Debug;

use crate::hex_with_len;

/// Decoder is a view into a byte array that has a read offset.  Use it for parsing.
pub struct Decoder<'a> {
    buf: &'a [u8],
    offset: usize,
}

impl<'a> Decoder<'a> {
    /// Make a new view of the provided slice.
    #[must_use]
    pub const fn new(buf: &[u8]) -> Decoder {
        Decoder { buf, offset: 0 }
    }

    /// Get the number of bytes remaining until the end.
    #[must_use]
    pub const fn remaining(&self) -> usize {
        self.buf.len() - self.offset
    }

    /// The number of bytes from the underlying slice that have been decoded.
    #[must_use]
    pub const fn offset(&self) -> usize {
        self.offset
    }

    /// Skip n bytes.
    ///
    /// # Panics
    ///
    /// If the remaining quantity is less than `n`.
    pub fn skip(&mut self, n: usize) {
        assert!(self.remaining() >= n, "insufficient data");
        self.offset += n;
    }

    /// Skip helper that panics if `n` is `None` or not able to fit in `usize`.
    fn skip_inner(&mut self, n: Option<u64>) {
        self.skip(usize::try_from(n.expect("invalid length")).unwrap());
    }

    /// Skip a vector.  Panics if there isn't enough space.
    /// Only use this for tests because we panic rather than reporting a result.
    pub fn skip_vec(&mut self, n: usize) {
        let len = self.decode_uint(n);
        self.skip_inner(len);
    }

    /// Skip a variable length vector.  Panics if there isn't enough space.
    /// Only use this for tests because we panic rather than reporting a result.
    pub fn skip_vvec(&mut self) {
        let len = self.decode_varint();
        self.skip_inner(len);
    }

    /// Decodes (reads) a single byte.
    pub fn decode_byte(&mut self) -> Option<u8> {
        if self.remaining() < 1 {
            return None;
        }
        let b = self.buf[self.offset];
        self.offset += 1;
        Some(b)
    }

    /// Provides the next byte without moving the read position.
    #[must_use]
    pub const fn peek_byte(&self) -> Option<u8> {
        if self.remaining() < 1 {
            None
        } else {
            Some(self.buf[self.offset])
        }
    }

    /// Decodes arbitrary data.
    pub fn decode(&mut self, n: usize) -> Option<&'a [u8]> {
        if self.remaining() < n {
            return None;
        }
        let res = &self.buf[self.offset..self.offset + n];
        self.offset += n;
        Some(res)
    }

    /// Decodes an unsigned integer of length 1..=8.
    ///
    /// # Panics
    ///
    /// This panics if `n` is not in the range `1..=8`.
    pub fn decode_uint(&mut self, n: usize) -> Option<u64> {
        assert!(n > 0 && n <= 8);
        if self.remaining() < n {
            return None;
        }
        let mut v = 0_u64;
        for i in 0..n {
            let b = self.buf[self.offset + i];
            v = v << 8 | u64::from(b);
        }
        self.offset += n;
        Some(v)
    }

    /// Decodes a QUIC varint.
    pub fn decode_varint(&mut self) -> Option<u64> {
        let b1 = self.decode_byte()?;
        match b1 >> 6 {
            0 => Some(u64::from(b1 & 0x3f)),
            1 => Some((u64::from(b1 & 0x3f) << 8) | self.decode_uint(1)?),
            2 => Some((u64::from(b1 & 0x3f) << 24) | self.decode_uint(3)?),
            3 => Some((u64::from(b1 & 0x3f) << 56) | self.decode_uint(7)?),
            _ => unreachable!(),
        }
    }

    /// Decodes the rest of the buffer.  Infallible.
    pub fn decode_remainder(&mut self) -> &'a [u8] {
        let res = &self.buf[self.offset..];
        self.offset = self.buf.len();
        res
    }

    fn decode_checked(&mut self, n: Option<u64>) -> Option<&'a [u8]> {
        if let Ok(l) = usize::try_from(n?) {
            self.decode(l)
        } else {
            // sizeof(usize) < sizeof(u64) and the value is greater than
            // usize can hold. Throw away the rest of the input.
            self.offset = self.buf.len();
            None
        }
    }

    /// Decodes a TLS-style length-prefixed buffer.
    pub fn decode_vec(&mut self, n: usize) -> Option<&'a [u8]> {
        let len = self.decode_uint(n);
        self.decode_checked(len)
    }

    /// Decodes a QUIC varint-length-prefixed buffer.
    pub fn decode_vvec(&mut self) -> Option<&'a [u8]> {
        let len = self.decode_varint();
        self.decode_checked(len)
    }
}

// Implement `AsRef` for `Decoder` so that values can be examined without
// moving the cursor.
impl<'a> AsRef<[u8]> for Decoder<'a> {
    #[must_use]
    fn as_ref(&self) -> &'a [u8] {
        &self.buf[self.offset..]
    }
}

impl<'a> Debug for Decoder<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&hex_with_len(self.as_ref()))
    }
}

impl<'a> From<&'a [u8]> for Decoder<'a> {
    #[must_use]
    fn from(buf: &'a [u8]) -> Self {
        Decoder::new(buf)
    }
}

impl<'a, T> From<&'a T> for Decoder<'a>
where
    T: AsRef<[u8]>,
{
    #[must_use]
    fn from(buf: &'a T) -> Self {
        Decoder::new(buf.as_ref())
    }
}

impl<'a, 'b> PartialEq<Decoder<'b>> for Decoder<'a> {
    #[must_use]
    fn eq(&self, other: &Decoder<'b>) -> bool {
        self.buf == other.buf
    }
}

// TODO: Should this be `&mut [u8]`? Does it need to be able to allocate?
/// Encoder is good for building data structures.
#[derive(PartialEq, Eq)]
pub struct Encoder<'a> {
    buf: &'a mut Vec<u8>,
}

impl<'a> Encoder<'a> {
    pub fn new_with_buffer(buf: &'a mut Vec<u8>) -> Self {
        Self { buf }
    }

    /// Static helper function for previewing the results of encoding without doing it.
    ///
    /// # Panics
    ///
    /// When `v` is too large.
    #[must_use]
    pub const fn varint_len(v: u64) -> usize {
        match () {
            () if v < (1 << 6) => 1,
            () if v < (1 << 14) => 2,
            () if v < (1 << 30) => 4,
            () if v < (1 << 62) => 8,
            () => panic!("Varint value too large"),
        }
    }

    /// Static helper to determine how long a varint-prefixed array encodes to.
    ///
    /// # Panics
    ///
    /// When `len` doesn't fit in a `u64`.
    #[must_use]
    pub fn vvec_len(len: usize) -> usize {
        Self::varint_len(u64::try_from(len).unwrap()) + len
    }

    /// Get the length of the underlying buffer: the number of bytes that have
    /// been written to the buffer.
    #[must_use]
    pub fn len(&self) -> usize {
        self.buf.len()
    }

    /// Returns true if the encoder buffer contains no elements.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }

    /// Create a view of the current contents of the buffer.
    /// Note: for a view of a slice, use `Decoder::new(&enc[s..e])`
    #[must_use]
    pub fn as_decoder(&self) -> Decoder {
        Decoder::new(self.buf)
    }

    /// Don't use this except in testing.
    ///
    /// # Panics
    ///
    /// When `s` contains non-hex values or an odd number of values.
    #[must_use]
    pub fn from_hex(mut self, s: impl AsRef<str>) -> Self {
        let s = s.as_ref();
        assert_eq!(s.len() % 2, 0, "Needs to be even length");

        let cap = s.len() / 2;
        self.buf.reserve(cap);

        for i in 0..cap {
            let v = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap();
            self.encode_byte(v);
        }
        self
    }

    #[cfg(test)]
    fn to_hex(&self) -> String {
        crate::hex(&self.buf)
    }

    /// Generic encode routine for arbitrary data.
    pub fn encode(&mut self, data: &[u8]) -> &mut Self {
        self.buf.extend_from_slice(data.as_ref());
        self
    }

    /// Encode a single byte.
    pub fn encode_byte(&mut self, data: u8) -> &mut Self {
        self.buf.push(data);
        self
    }

    /// Encode an integer of any size up to u64.
    ///
    /// # Panics
    ///
    /// When `n` is outside the range `1..=8`.
    pub fn encode_uint<T: Into<u64>>(&mut self, n: usize, v: T) -> &mut Self {
        let v = v.into();
        assert!(n > 0 && n <= 8);
        for i in 0..n {
            self.encode_byte(((v >> (8 * (n - i - 1))) & 0xff) as u8);
        }
        self
    }

    /// Encode a QUIC varint.
    ///
    /// # Panics
    ///
    /// When `v >= 1<<62`.
    pub fn encode_varint<T: Into<u64>>(&mut self, v: T) -> &mut Self {
        let v = v.into();
        match () {
            () if v < (1 << 6) => self.encode_uint(1, v),
            () if v < (1 << 14) => self.encode_uint(2, v | (1 << 14)),
            () if v < (1 << 30) => self.encode_uint(4, v | (2 << 30)),
            () if v < (1 << 62) => self.encode_uint(8, v | (3 << 62)),
            () => panic!("Varint value too large"),
        };
        self
    }

    /// Encode a vector in TLS style.
    ///
    /// # Panics
    ///
    /// When `v` is longer than 2^64.
    pub fn encode_vec(&mut self, n: usize, v: &[u8]) -> &mut Self {
        self.encode_uint(n, u64::try_from(v.as_ref().len()).unwrap())
            .encode(v)
    }

    /// Encode a vector in TLS style using a closure for the contents.
    ///
    /// # Panics
    ///
    /// When `f()` returns a length larger than `2^8n`.
    #[allow(clippy::cast_possible_truncation)]
    pub fn encode_vec_with<F: FnOnce(&mut Self)>(&mut self, n: usize, f: F) -> &mut Self {
        let start = self.buf.len();
        let len = self.buf.len();
        self.buf.resize(len + n, 0);
        f(self);
        let len = self.buf.len() - start - n;
        assert!(len < (1 << (n * 8)));
        for i in 0..n {
            self.buf[start + i] = ((len >> (8 * (n - i - 1))) & 0xff) as u8;
        }
        self
    }

    /// Encode a vector with a varint length.
    ///
    /// # Panics
    ///
    /// When `v` is longer than 2^64.
    pub fn encode_vvec(&mut self, v: &[u8]) -> &mut Self {
        self.encode_varint(u64::try_from(v.as_ref().len()).unwrap())
            .encode(v)
    }

    /// Encode a vector with a varint length using a closure.
    ///
    /// # Panics
    ///
    /// When `f()` writes more than 2^62 bytes.
    pub fn encode_vvec_with<F: FnOnce(&mut Self)>(&mut self, f: F) -> &mut Self {
        let start = self.buf.len();
        // Optimize for short buffers, reserve a single byte for the length.
        let len = self.buf.len();
        self.buf.resize(len + 1, 0);
        f(self);
        let len = self.buf.len() - start - 1;

        // Now to insert a varint for `len` before the encoded block.
        //
        // We now have one zero byte at `start`, followed by `len` encoded bytes:
        //   |  0  | ... encoded ... |
        // We are going to encode a varint by putting the low bytes in that spare byte.
        // Any additional bytes for the varint are put after the encoded blob:
        //   | low | ... encoded ... | varint high |
        // Then we will rotate that entire piece right, by however many bytes we add:
        //   | varint high | low | ... encoded ... |
        // As long as encoding more than 63 bytes is rare, this won't cost much relative
        // to the convenience of being able to use this function.

        let v = u64::try_from(len).expect("encoded value fits in a u64");
        // The lower order byte fits before the inserted block of bytes.
        self.buf[start] = (v & 0xff) as u8;
        let (count, bits) = match () {
            // Great.  The byte we have is enough.
            () if v < (1 << 6) => return self,
            () if v < (1 << 14) => (1, 1 << 6),
            () if v < (1 << 30) => (3, 2 << 22),
            () if v < (1 << 62) => (7, 3 << 54),
            () => panic!("Varint value too large"),
        };
        // Now, we need to encode the high bits after the main block, ...
        self.encode_uint(count, (v >> 8) | bits);
        // ..., then rotate the entire thing right by the same amount.
        self.buf[start..].rotate_right(count);
        self
    }

    /// Truncate the encoder to the given size.
    pub fn truncate(&mut self, len: usize) {
        self.buf.truncate(len);
    }

    /// Pad the buffer to `len` with bytes set to `v`.
    pub fn pad_to(&mut self, len: usize, v: u8) {
        if len > self.buf.len() {
            self.buf.resize(len, v);
        }
    }

    // TODO: rename function and arguments?
    pub fn clone_into<'b>(&'a self, write_buffer: &'b mut Vec<u8>) -> Encoder<'b> {
        write_buffer.extend_from_slice(self.buf);
        Encoder { buf: write_buffer }
    }
}

impl<'a> Debug for Encoder<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&hex_with_len(self))
    }
}

impl<'a> AsRef<[u8]> for Encoder<'a> {
    fn as_ref(&self) -> &[u8] {
        self.buf
    }
}

impl<'a> AsMut<[u8]> for Encoder<'a> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.buf
    }
}

impl<'a> From<Encoder<'a>> for &'a [u8] {
    #[must_use]
    fn from(encoder: Encoder<'a>) -> &'a [u8] {
        encoder.buf
    }
}

// TODO: Should this be test only?
impl<'a> From<Encoder<'a>> for Vec<u8> {
    #[must_use]
    fn from(buf: Encoder) -> Self {
        // TODO: Is allocation intuitive here?
        buf.buf.clone()
    }
}

impl<'a> From<Encoder<'a>> for &'a mut Vec<u8> {
    #[must_use]
    fn from(buf: Encoder<'a>) -> &'a mut Vec<u8> {
        buf.buf
    }
}

#[cfg(test)]
mod tests {
    use super::{Decoder, Encoder};

    #[test]
    fn decode() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("012345");
        let mut dec = enc.as_decoder();
        assert_eq!(dec.decode(2).unwrap(), &[0x01, 0x23]);
        assert!(dec.decode(2).is_none());
    }

    #[test]
    fn decode_byte() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("0123");
        let mut dec = enc.as_decoder();

        assert_eq!(dec.decode_byte().unwrap(), 0x01);
        assert_eq!(dec.decode_byte().unwrap(), 0x23);
        assert!(dec.decode_byte().is_none());
    }

    #[test]
    fn decode_byte_short() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("");
        let mut dec = enc.as_decoder();
        assert!(dec.decode_byte().is_none());
    }

    #[test]
    fn decode_remainder() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("012345");
        let mut dec = enc.as_decoder();
        assert_eq!(dec.decode_remainder(), &[0x01, 0x23, 0x45]);
        assert!(dec.decode(2).is_none());

        let mut dec = Decoder::from(&[]);
        assert_eq!(dec.decode_remainder().len(), 0);
    }

    #[test]
    fn decode_vec() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("012345");
        let mut dec = enc.as_decoder();
        assert_eq!(dec.decode_vec(1).expect("read one octet length"), &[0x23]);
        assert_eq!(dec.remaining(), 1);

        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("00012345");
        let mut dec = enc.as_decoder();
        assert_eq!(dec.decode_vec(2).expect("read two octet length"), &[0x23]);
        assert_eq!(dec.remaining(), 1);
    }

    #[test]
    fn decode_vec_short() {
        // The length is too short.
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("02");
        let mut dec = enc.as_decoder();
        assert!(dec.decode_vec(2).is_none());

        // The body is too short.
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("0200");
        let mut dec = enc.as_decoder();
        assert!(dec.decode_vec(1).is_none());
    }

    #[test]
    fn decode_vvec() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("012345");
        let mut dec = enc.as_decoder();
        assert_eq!(dec.decode_vvec().expect("read one octet length"), &[0x23]);
        assert_eq!(dec.remaining(), 1);

        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("40012345");
        let mut dec = enc.as_decoder();
        assert_eq!(dec.decode_vvec().expect("read two octet length"), &[0x23]);
        assert_eq!(dec.remaining(), 1);
    }

    #[test]
    fn decode_vvec_short() {
        // The length field is too short.
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("ff");
        let mut dec = enc.as_decoder();
        assert!(dec.decode_vvec().is_none());

        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("405500");
        let mut dec = enc.as_decoder();
        assert!(dec.decode_vvec().is_none());
    }

    #[test]
    fn skip() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("ffff");
        let mut dec = enc.as_decoder();
        dec.skip(1);
        assert_eq!(dec.remaining(), 1);
    }

    #[test]
    #[should_panic(expected = "insufficient data")]
    fn skip_too_much() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("ff");
        let mut dec = enc.as_decoder();
        dec.skip(2);
    }

    #[test]
    fn skip_vec() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("012345");
        let mut dec = enc.as_decoder();
        dec.skip_vec(1);
        assert_eq!(dec.remaining(), 1);
    }

    #[test]
    #[should_panic(expected = "insufficient data")]
    fn skip_vec_too_much() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("ff1234");
        let mut dec = enc.as_decoder();
        dec.skip_vec(1);
    }

    #[test]
    #[should_panic(expected = "invalid length")]
    fn skip_vec_short_length() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("ff");
        let mut dec = enc.as_decoder();
        dec.skip_vec(4);
    }
    #[test]
    fn skip_vvec() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("012345");
        let mut dec = enc.as_decoder();
        dec.skip_vvec();
        assert_eq!(dec.remaining(), 1);
    }

    #[test]
    #[should_panic(expected = "insufficient data")]
    fn skip_vvec_too_much() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("0f1234");
        let mut dec = enc.as_decoder();
        dec.skip_vvec();
    }

    #[test]
    #[should_panic(expected = "invalid length")]
    fn skip_vvec_short_length() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("ff");
        let mut dec = enc.as_decoder();
        dec.skip_vvec();
    }

    #[test]
    fn encoded_lengths() {
        assert_eq!(Encoder::varint_len(0), 1);
        assert_eq!(Encoder::varint_len(0x3f), 1);
        assert_eq!(Encoder::varint_len(0x40), 2);
        assert_eq!(Encoder::varint_len(0x3fff), 2);
        assert_eq!(Encoder::varint_len(0x4000), 4);
        assert_eq!(Encoder::varint_len(0x3fff_ffff), 4);
        assert_eq!(Encoder::varint_len(0x4000_0000), 8);
    }

    #[test]
    #[should_panic(expected = "Varint value too large")]
    const fn encoded_length_oob() {
        _ = Encoder::varint_len(1 << 62);
    }

    #[test]
    fn encoded_vvec_lengths() {
        assert_eq!(Encoder::vvec_len(0), 1);
        assert_eq!(Encoder::vvec_len(0x3f), 0x40);
        assert_eq!(Encoder::vvec_len(0x40), 0x42);
        assert_eq!(Encoder::vvec_len(0x3fff), 0x4001);
        assert_eq!(Encoder::vvec_len(0x4000), 0x4004);
        assert_eq!(Encoder::vvec_len(0x3fff_ffff), 0x4000_0003);
        assert_eq!(Encoder::vvec_len(0x4000_0000), 0x4000_0008);
    }

    #[test]
    #[should_panic(expected = "Varint value too large")]
    fn encoded_vvec_length_oob() {
        _ = Encoder::vvec_len(1 << 62);
    }

    #[test]
    fn encode_byte() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer);

        enc.encode_byte(1);
        assert_eq!(enc, Encoder::new_with_buffer(&mut vec![]).from_hex("01"));

        enc.encode_byte(0xfe);
        assert_eq!(enc, Encoder::new_with_buffer(&mut vec![]).from_hex("01fe"));
    }

    #[test]
    fn encode() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer);
        enc.encode(&[1, 2, 3]);
        assert_eq!(
            enc,
            Encoder::new_with_buffer(&mut vec![]).from_hex("010203")
        );
    }

    #[test]
    fn encode_uint() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer);
        enc.encode_uint(2, 10_u8); // 000a
        enc.encode_uint(1, 257_u16); // 01
        enc.encode_uint(3, 0xff_ffff_u32); // ffffff
        enc.encode_uint(8, 0xfedc_ba98_7654_3210_u64);
        assert_eq!(
            enc,
            Encoder::new_with_buffer(&mut vec![]).from_hex("000a01fffffffedcba9876543210")
        );
    }

    #[test]
    fn builder_from_vec() {
        let mut v = vec![1, 2, 3];
        let enc = Encoder::new_with_buffer(&mut v);
        assert_eq!(
            enc,
            Encoder::new_with_buffer(&mut vec![]).from_hex("010203")
        );
    }

    #[test]
    fn builder_inas_decoder() {
        let mut write_buffer = vec![];
        let enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("010203");
        let buf = &[1, 2, 3];
        assert_eq!(enc.as_decoder(), Decoder::new(buf));
    }

    struct UintTestCase {
        v: u64,
        b: String,
    }

    macro_rules! uint_tc {
        [$( $v:expr => $b:expr ),+ $(,)?] => {
            vec![ $( UintTestCase { v: $v, b: String::from($b) } ),+]
        };
    }

    #[test]
    fn varint_encode_decode() {
        let cases = uint_tc![
            0 => "00",
            1 => "01",
            63 => "3f",
            64 => "4040",
            16383 => "7fff",
            16384 => "80004000",
            (1 << 30) - 1 => "bfffffff",
            1 << 30 => "c000000040000000",
            (1 << 62) - 1 => "ffffffffffffffff",
        ];

        for c in cases {
            assert_eq!(Encoder::varint_len(c.v), c.b.len() / 2);

            let mut write_buffer = vec![];
            let mut enc = Encoder::new_with_buffer(&mut write_buffer);
            enc.encode_varint(c.v);
            let mut write_buffer = vec![];
            let encoded = Encoder::new_with_buffer(&mut write_buffer).from_hex(&c.b);
            assert_eq!(enc, encoded);

            let mut dec = encoded.as_decoder();
            let v = dec.decode_varint().expect("should decode");
            assert_eq!(dec.remaining(), 0);
            assert_eq!(v, c.v);
        }
    }

    #[test]
    fn varint_decode_long_zero() {
        for c in &["4000", "80000000", "c000000000000000"] {
            let mut write_buffer = vec![];
            let encoded = Encoder::new_with_buffer(&mut write_buffer).from_hex(c);
            let mut dec = encoded.as_decoder();
            let v = dec.decode_varint().expect("should decode");
            assert_eq!(dec.remaining(), 0);
            assert_eq!(v, 0);
        }
    }

    #[test]
    fn varint_decode_short() {
        for c in &["40", "800000", "c0000000000000"] {
            let mut write_buffer = vec![];
            let encoded = Encoder::new_with_buffer(&mut write_buffer).from_hex(c);
            let mut dec = encoded.as_decoder();
            assert!(dec.decode_varint().is_none());
        }
    }

    #[test]
    fn encode_vec() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer);
        enc.encode_vec(2, &[1, 2, 0x34]);
        assert_eq!(enc.to_hex(), "0003010234");
    }

    #[test]
    fn encode_vec_with() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer);
        enc.encode_vec_with(2, |enc_inner| {
            // TODO: Too complex.
            let mut write_buffer = vec![];
            enc_inner.encode(
                Encoder::new_with_buffer(&mut write_buffer)
                    .from_hex("02")
                    .as_ref(),
            );
        });
        assert_eq!(enc.to_hex(), "000102");
    }

    #[test]
    #[should_panic(expected = "assertion failed")]
    fn encode_vec_with_overflow() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer);
        enc.encode_vec_with(1, |enc_inner| {
            enc_inner.encode(&[0xb0; 256]);
        });
    }

    #[test]
    fn encode_vvec() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer);
        enc.encode_vvec(&[1, 2, 0x34]);
        assert_eq!(enc.to_hex(), "03010234");
    }

    #[test]
    fn encode_vvec_with() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer);
        enc.encode_vvec_with(|enc_inner| {
            let mut write_buffer = vec![];
            enc_inner.encode(
                Encoder::new_with_buffer(&mut write_buffer)
                    .from_hex("02")
                    .as_ref(),
            );
        });
        assert_eq!(enc.to_hex(), "0102");
    }

    #[test]
    fn encode_vvec_with_longer() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer);
        enc.encode_vvec_with(|enc_inner| {
            enc_inner.encode(&[0xa5; 65]);
        });
        let v: Vec<u8> = enc.into();
        assert_eq!(&v[..3], &[0x40, 0x41, 0xa5]);
    }

    // Test that Deref to &[u8] works for Encoder.
    #[test]
    fn encode_builder() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("ff");
        let mut write_buffer = vec![];
        let enc2 = Encoder::new_with_buffer(&mut write_buffer).from_hex("010234");
        enc.encode(enc2.as_ref());
        assert_eq!(enc.to_hex(), "ff010234");
    }

    // Test that Deref to &[u8] works for Decoder.
    #[test]
    fn encode_view() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("ff");
        let mut write_buffer = vec![];
        let enc2 = Encoder::new_with_buffer(&mut write_buffer).from_hex("010234");
        let v = enc2.as_decoder();
        enc.encode(v.as_ref());
        assert_eq!(enc.to_hex(), "ff010234");
    }

    #[test]
    fn encode_mutate() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("010234");
        enc.as_mut()[0] = 0xff;
        assert_eq!(enc.to_hex(), "ff0234");
    }

    #[test]
    fn pad() {
        let mut write_buffer = vec![];
        let mut enc = Encoder::new_with_buffer(&mut write_buffer).from_hex("010234");
        enc.pad_to(5, 0);
        assert_eq!(enc.to_hex(), "0102340000");
        enc.pad_to(4, 0);
        assert_eq!(enc.to_hex(), "0102340000");
        enc.pad_to(7, 0xc2);
        assert_eq!(
            enc,
            Encoder::new_with_buffer(&mut vec![]).from_hex("0102340000c2c2")
        );
    }
}
