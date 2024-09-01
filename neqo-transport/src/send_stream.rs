// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Buffering data to send until it is acked.

use std::{
    cell::RefCell,
    cmp::{max, min, Ordering},
    collections::{btree_map::Entry, BTreeMap, VecDeque},
    hash::{Hash, Hasher},
    mem,
    num::NonZeroUsize,
    ops::Add,
    rc::Rc,
};

use indexmap::IndexMap;
use neqo_common::{qdebug, qerror, qtrace, Encoder, Role};
use smallvec::SmallVec;

use crate::{
    events::ConnectionEvents,
    fc::SenderFlowControl,
    frame::{Frame, FRAME_TYPE_RESET_STREAM},
    packet::PacketBuilder,
    recovery::{RecoveryToken, StreamRecoveryToken},
    stats::FrameStats,
    stream_id::StreamId,
    streams::SendOrder,
    tparams::{self, TransportParameters},
    AppError, Error, Res,
};

pub const SEND_BUFFER_SIZE: usize = 0x10_0000; // 1 MiB

/// The priority that is assigned to sending data for the stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransmissionPriority {
    /// This stream is more important than the functioning of the connection.
    /// Don't use this priority unless the stream really is that important.
    /// A stream at this priority can starve out other connection functions,
    /// including flow control, which could be very bad.
    Critical,
    /// The stream is very important.  Stream data will be written ahead of
    /// some of the less critical connection functions, like path validation,
    /// connection ID management, and session tickets.
    Important,
    /// High priority streams are important, but not enough to disrupt
    /// connection operation.  They go ahead of session tickets though.
    High,
    /// The default priority.
    Normal,
    /// Low priority streams get sent last.
    Low,
}

impl Default for TransmissionPriority {
    fn default() -> Self {
        Self::Normal
    }
}

impl PartialOrd for TransmissionPriority {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TransmissionPriority {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            return Ordering::Equal;
        }
        match (self, other) {
            (Self::Critical, _) => Ordering::Greater,
            (_, Self::Critical) => Ordering::Less,
            (Self::Important, _) => Ordering::Greater,
            (_, Self::Important) => Ordering::Less,
            (Self::High, _) => Ordering::Greater,
            (_, Self::High) => Ordering::Less,
            (Self::Normal, _) => Ordering::Greater,
            (_, Self::Normal) => Ordering::Less,
            _ => unreachable!(),
        }
    }
}

impl Add<RetransmissionPriority> for TransmissionPriority {
    type Output = Self;
    fn add(self, rhs: RetransmissionPriority) -> Self::Output {
        match rhs {
            RetransmissionPriority::Fixed(fixed) => fixed,
            RetransmissionPriority::Same => self,
            RetransmissionPriority::Higher => match self {
                Self::Critical => Self::Critical,
                Self::Important | Self::High => Self::Important,
                Self::Normal => Self::High,
                Self::Low => Self::Normal,
            },
            RetransmissionPriority::MuchHigher => match self {
                Self::Critical | Self::Important => Self::Critical,
                Self::High | Self::Normal => Self::Important,
                Self::Low => Self::High,
            },
        }
    }
}

/// If data is lost, this determines the priority that applies to retransmissions
/// of that data.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum RetransmissionPriority {
    /// Prioritize retransmission at a fixed priority.
    /// With this, it is possible to prioritize retransmissions lower than transmissions.
    /// Doing that can create a deadlock with flow control which might cause the connection
    /// to stall unless new data stops arriving fast enough that retransmissions can complete.
    Fixed(TransmissionPriority),
    /// Don't increase priority for retransmission.  This is probably not a good idea
    /// as it could mean starving flow control.
    Same,
    /// Increase the priority of retransmissions (the default).
    /// Retransmissions of `Critical` or `Important` aren't elevated at all.
    #[default]
    Higher,
    /// Increase the priority of retransmissions a lot.
    /// This is useful for streams that are particularly exposed to head-of-line blocking.
    MuchHigher,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum RangeState {
    Sent,
    Acked,
}

/// Track ranges in the stream as sent or acked. Acked implies sent. Not in a
/// range implies needing-to-be-sent, either initially or as a retransmission.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct RangeTracker {
    /// The number of bytes that have been acknowledged starting from offset 0.
    acked: u64,
    /// A map that tracks the state of ranges.
    /// Keys are the offset of the start of the range.
    /// Values is a tuple of the range length and its state.
    used: BTreeMap<u64, (u64, RangeState)>,
    /// This is a cache for the output of `first_unmarked_range`, which we check a lot.
    first_unmarked: Option<(u64, Option<u64>)>,
}

impl RangeTracker {
    fn highest_offset(&self) -> u64 {
        self.used
            .last_key_value()
            .map_or(self.acked, |(&k, &(v, _))| k + v)
    }

    const fn acked_from_zero(&self) -> u64 {
        self.acked
    }

    /// Find the first unmarked range. If all are contiguous, this will return
    /// (`highest_offset()`, None).
    fn first_unmarked_range(&mut self) -> (u64, Option<u64>) {
        if let Some(first_unmarked) = self.first_unmarked {
            return first_unmarked;
        }

        let mut prev_end = self.acked;

        for (&cur_off, &(cur_len, _)) in &self.used {
            if prev_end == cur_off {
                prev_end = cur_off + cur_len;
            } else {
                let res = (prev_end, Some(cur_off - prev_end));
                self.first_unmarked = Some(res);
                return res;
            }
        }
        self.first_unmarked = Some((prev_end, None));
        (prev_end, None)
    }

    /// When the range of acknowledged bytes from zero increases, we need to drop any
    /// ranges within that span AND maybe extend it to include any adjacent acknowledged ranges.
    fn coalesce_acked(&mut self) {
        while let Some(e) = self.used.first_entry() {
            match self.acked.cmp(e.key()) {
                Ordering::Greater => {
                    let (off, (len, state)) = e.remove_entry();
                    let overflow = (off + len).saturating_sub(self.acked);
                    if overflow > 0 {
                        if state == RangeState::Acked {
                            self.acked += overflow;
                        } else {
                            self.used.insert(self.acked, (overflow, state));
                        }
                        break;
                    }
                }
                Ordering::Equal => {
                    if e.get().1 == RangeState::Acked {
                        let (len, _) = e.remove();
                        self.acked += len;
                    }
                    break;
                }
                Ordering::Less => break,
            }
        }
    }

    /// Mark a range as acknowledged.  This is simpler than marking a range as sent
    /// because an acknowledged range can never turn back into a sent range, so
    /// this function can just override the entire range.
    ///
    /// The only tricky parts are making sure that we maintain `self.acked`,
    /// which is the first acknowledged range.  And making sure that we don't create
    /// ranges of the same type that are adjacent; these need to be merged.
    #[allow(clippy::missing_panics_doc)] // with a >16 exabyte packet on a 128-bit machine, maybe
    pub fn mark_acked(&mut self, new_off: u64, new_len: usize) {
        let end = new_off + u64::try_from(new_len).unwrap();
        let new_off = max(self.acked, new_off);
        let mut new_len = end.saturating_sub(new_off);
        if new_len == 0 {
            return;
        }

        self.first_unmarked = None;
        if new_off == self.acked {
            self.acked += new_len;
            self.coalesce_acked();
            return;
        }
        let mut new_end = new_off + new_len;

        // Get all existing ranges that start within this new range.
        let mut covered = self
            .used
            .range(new_off..new_end)
            .map(|(&k, _)| k)
            .collect::<SmallVec<[_; 8]>>();

        if let Entry::Occupied(next_entry) = self.used.entry(new_end) {
            // Check if the very next entry is the same type as this.
            if next_entry.get().1 == RangeState::Acked {
                // If is is acked, drop it and extend this new range.
                let (extra_len, _) = next_entry.remove();
                new_len += extra_len;
                new_end += extra_len;
            }
        } else if let Some(last) = covered.pop() {
            // Otherwise, the last of the existing ranges might overhang this one by some.
            let (old_off, (old_len, old_state)) = self.used.remove_entry(&last).unwrap(); // can't fail
            let remainder = (old_off + old_len).saturating_sub(new_end);
            if remainder > 0 {
                if old_state == RangeState::Acked {
                    // Just extend the current range.
                    new_len += remainder;
                    new_end += remainder;
                } else {
                    self.used.insert(new_end, (remainder, RangeState::Sent));
                }
            }
        }
        // All covered ranges can just be trashed.
        for k in covered {
            self.used.remove(&k);
        }

        // Now either merge with a preceding acked range
        // or cut a preceding sent range as needed.
        let prev = self.used.range_mut(..new_off).next_back();
        if let Some((prev_off, (prev_len, prev_state))) = prev {
            let prev_end = *prev_off + *prev_len;
            if prev_end >= new_off {
                if *prev_state == RangeState::Sent {
                    *prev_len = new_off - *prev_off;
                    if prev_end > new_end {
                        // There is some extra sent range after the new acked range.
                        self.used
                            .insert(new_end, (prev_end - new_end, RangeState::Sent));
                    }
                } else {
                    *prev_len = max(prev_end, new_end) - *prev_off;
                    return;
                }
            }
        }
        self.used.insert(new_off, (new_len, RangeState::Acked));
    }

    /// Turn a single sent range into a list of subranges that align with existing
    /// acknowledged ranges.
    ///
    /// This is more complicated than adding acked ranges because any acked ranges
    /// need to be kept in place, with sent ranges filling the gaps.
    ///
    /// This means:
    /// ```ignore
    ///   AAA S AAAS AAAAA
    /// +  SSSSSSSSSSSSS
    /// = AAASSSAAASSAAAAA
    /// ```
    ///
    /// But we also have to ensure that:
    /// ```ignore
    ///     SSSS
    /// + SS
    /// = SSSSSS
    /// ```
    /// and
    /// ```ignore
    ///   SSSSS
    /// +     SS
    /// = SSSSSS
    /// ```
    #[allow(clippy::missing_panics_doc)] // not possible
    pub fn mark_sent(&mut self, mut new_off: u64, new_len: usize) {
        let new_end = new_off + u64::try_from(new_len).unwrap();
        new_off = max(self.acked, new_off);
        let mut new_len = new_end.saturating_sub(new_off);
        if new_len == 0 {
            return;
        }

        self.first_unmarked = None;

        // Get all existing ranges that start within this new range.
        let covered = self
            .used
            .range(new_off..(new_off + new_len))
            .map(|(&k, _)| k)
            .collect::<SmallVec<[u64; 8]>>();

        if let Entry::Occupied(next_entry) = self.used.entry(new_end) {
            if next_entry.get().1 == RangeState::Sent {
                // Check if the very next entry is the same type as this, so it can be merged.
                let (extra_len, _) = next_entry.remove();
                new_len += extra_len;
            }
        }

        // Merge with any preceding sent range that might overlap,
        // or cut the head of this if the preceding range is acked.
        let prev = self.used.range(..new_off).next_back();
        if let Some((&prev_off, &(prev_len, prev_state))) = prev {
            if prev_off + prev_len >= new_off {
                let overlap = prev_off + prev_len - new_off;
                new_len = new_len.saturating_sub(overlap);
                if new_len == 0 {
                    // The previous range completely covers this one (no more to do).
                    return;
                }

                if prev_state == RangeState::Acked {
                    // The previous range is acked, so it cuts this one.
                    new_off += overlap;
                } else {
                    // Extend the current range backwards.
                    new_off = prev_off;
                    new_len += prev_len;
                    // The previous range will be updated below.
                    // It might need to be cut because of a covered acked range.
                }
            }
        }

        // Now interleave new sent chunks with any existing acked chunks.
        for old_off in covered {
            let Entry::Occupied(e) = self.used.entry(old_off) else {
                unreachable!();
            };
            let &(old_len, old_state) = e.get();
            if old_state == RangeState::Acked {
                // Now we have to insert a chunk ahead of this acked chunk.
                let chunk_len = old_off - new_off;
                if chunk_len > 0 {
                    self.used.insert(new_off, (chunk_len, RangeState::Sent));
                }
                let included = chunk_len + old_len;
                new_len = new_len.saturating_sub(included);
                if new_len == 0 {
                    return;
                }
                new_off += included;
            } else {
                let overhang = (old_off + old_len).saturating_sub(new_off + new_len);
                new_len += overhang;
                if *e.key() != new_off {
                    // Retain a sent entry at `new_off`.
                    // This avoids the work of removing and re-creating an entry.
                    // The value will be overwritten when the next insert occurs,
                    // either when this loop hits an acked range (above)
                    // or for any remainder (below).
                    e.remove();
                }
            }
        }

        self.used.insert(new_off, (new_len, RangeState::Sent));
    }

    fn unmark_range(&mut self, off: u64, len: usize) {
        if len == 0 {
            qdebug!("unmark 0-length range at {}", off);
            return;
        }

        self.first_unmarked = None;
        let len = u64::try_from(len).unwrap();
        let end_off = off + len;

        let mut to_remove = SmallVec::<[_; 8]>::new();
        let mut to_add = None;

        // Walk backwards through possibly affected existing ranges
        for (cur_off, (cur_len, cur_state)) in self.used.range_mut(..off + len).rev() {
            // Maybe fixup range preceding the removed range
            if *cur_off < off {
                // Check for overlap
                if *cur_off + *cur_len > off {
                    if *cur_state == RangeState::Acked {
                        qdebug!(
                            "Attempted to unmark Acked range {}-{} with unmark_range {}-{}",
                            cur_off,
                            cur_len,
                            off,
                            off + len
                        );
                    } else {
                        *cur_len = off - cur_off;
                    }
                }
                break;
            }

            if *cur_state == RangeState::Acked {
                qdebug!(
                    "Attempted to unmark Acked range {}-{} with unmark_range {}-{}",
                    cur_off,
                    cur_len,
                    off,
                    off + len
                );
                continue;
            }

            // Add a new range for old subrange extending beyond
            // to-be-unmarked range
            let cur_end_off = cur_off + *cur_len;
            if cur_end_off > end_off {
                let new_cur_off = off + len;
                let new_cur_len = cur_end_off - end_off;
                assert_eq!(to_add, None);
                to_add = Some((new_cur_off, new_cur_len, *cur_state));
            }

            to_remove.push(*cur_off);
        }

        for remove_off in to_remove {
            self.used.remove(&remove_off);
        }

        if let Some((new_cur_off, new_cur_len, cur_state)) = to_add {
            self.used.insert(new_cur_off, (new_cur_len, cur_state));
        }
    }

    /// Unmark all sent ranges.
    /// # Panics
    /// On 32-bit machines where far too much is sent before calling this.
    /// Note that this should not be called for handshakes, which should never exceed that limit.
    pub fn unmark_sent(&mut self) {
        self.unmark_range(0, usize::try_from(self.highest_offset()).unwrap());
    }
}

/// Buffer to contain queued bytes and track their state.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct TxBuffer {
    send_buf: VecDeque<u8>, // buffer of not-acked bytes
    ranges: RangeTracker,   // ranges in buffer that have been sent or acked
}

impl TxBuffer {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Attempt to add some or all of the passed-in buffer to the `TxBuffer`.
    pub fn send(&mut self, buf: &[u8]) -> usize {
        let can_buffer = min(SEND_BUFFER_SIZE - self.buffered(), buf.len());
        if can_buffer > 0 {
            self.send_buf.extend(&buf[..can_buffer]);
            debug_assert!(self.send_buf.len() <= SEND_BUFFER_SIZE);
        }
        can_buffer
    }

    #[allow(clippy::missing_panics_doc)] // These are not possible.
    pub fn next_bytes(&mut self) -> Option<(u64, &[u8])> {
        let (start, maybe_len) = self.ranges.first_unmarked_range();

        if start == self.retired() + u64::try_from(self.buffered()).unwrap() {
            return None;
        }

        // Convert from ranges-relative-to-zero to
        // ranges-relative-to-buffer-start
        let buff_off = usize::try_from(start - self.retired()).unwrap();

        // Deque returns two slices. Create a subslice from whichever
        // one contains the first unmarked data.
        let slc = if buff_off < self.send_buf.as_slices().0.len() {
            &self.send_buf.as_slices().0[buff_off..]
        } else {
            &self.send_buf.as_slices().1[buff_off - self.send_buf.as_slices().0.len()..]
        };

        let len = maybe_len.map_or(slc.len(), |range_len| {
            min(usize::try_from(range_len).unwrap(), slc.len())
        });

        debug_assert!(len > 0);
        debug_assert!(len <= slc.len());

        Some((start, &slc[..len]))
    }

    pub fn mark_as_sent(&mut self, offset: u64, len: usize) {
        self.ranges.mark_sent(offset, len);
    }

    #[allow(clippy::missing_panics_doc)] // Not possible here.
    pub fn mark_as_acked(&mut self, offset: u64, len: usize) {
        let prev_retired = self.retired();
        self.ranges.mark_acked(offset, len);

        // Any newly-retired bytes can be dropped from the buffer.
        let new_retirable = self.retired() - prev_retired;
        debug_assert!(new_retirable <= self.buffered() as u64);
        let keep = self.buffered() - usize::try_from(new_retirable).unwrap();

        // Truncate front
        self.send_buf.rotate_left(self.buffered() - keep);
        self.send_buf.truncate(keep);
    }

    pub fn mark_as_lost(&mut self, offset: u64, len: usize) {
        self.ranges.unmark_range(offset, len);
    }

    /// Forget about anything that was marked as sent.
    pub fn unmark_sent(&mut self) {
        self.ranges.unmark_sent();
    }

    #[must_use]
    pub const fn retired(&self) -> u64 {
        self.ranges.acked_from_zero()
    }

    fn buffered(&self) -> usize {
        self.send_buf.len()
    }

    fn avail(&self) -> usize {
        SEND_BUFFER_SIZE - self.buffered()
    }

    fn used(&self) -> u64 {
        self.retired() + u64::try_from(self.buffered()).unwrap()
    }
}

/// QUIC sending stream states, based on -transport 3.1.
#[derive(Debug)]
pub enum SendStreamState {
    Ready {
        fc: SenderFlowControl<StreamId>,
        conn_fc: Rc<RefCell<SenderFlowControl<()>>>,
    },
    Send {
        fc: SenderFlowControl<StreamId>,
        conn_fc: Rc<RefCell<SenderFlowControl<()>>>,
        send_buf: TxBuffer,
    },
    // Note: `DataSent` is entered when the stream is closed, not when all data has been
    // sent for the first time.
    DataSent {
        send_buf: TxBuffer,
        fin_sent: bool,
        fin_acked: bool,
    },
    DataRecvd {
        retired: u64,
        written: u64,
    },
    ResetSent {
        err: AppError,
        final_size: u64,
        priority: Option<TransmissionPriority>,
        final_retired: u64,
        final_written: u64,
    },
    ResetRecvd {
        final_retired: u64,
        final_written: u64,
    },
}

impl SendStreamState {
    fn tx_buf_mut(&mut self) -> Option<&mut TxBuffer> {
        match self {
            Self::Send { send_buf, .. } | Self::DataSent { send_buf, .. } => Some(send_buf),
            Self::Ready { .. }
            | Self::DataRecvd { .. }
            | Self::ResetSent { .. }
            | Self::ResetRecvd { .. } => None,
        }
    }

    fn tx_avail(&self) -> usize {
        match self {
            // In Ready, TxBuffer not yet allocated but size is known
            Self::Ready { .. } => SEND_BUFFER_SIZE,
            Self::Send { send_buf, .. } | Self::DataSent { send_buf, .. } => send_buf.avail(),
            Self::DataRecvd { .. } | Self::ResetSent { .. } | Self::ResetRecvd { .. } => 0,
        }
    }

    const fn name(&self) -> &str {
        match self {
            Self::Ready { .. } => "Ready",
            Self::Send { .. } => "Send",
            Self::DataSent { .. } => "DataSent",
            Self::DataRecvd { .. } => "DataRecvd",
            Self::ResetSent { .. } => "ResetSent",
            Self::ResetRecvd { .. } => "ResetRecvd",
        }
    }

    fn transition(&mut self, new_state: Self) {
        qtrace!("SendStream state {} -> {}", self.name(), new_state.name());
        *self = new_state;
    }
}

// See https://www.w3.org/TR/webtransport/#send-stream-stats.
#[derive(Debug, Clone, Copy)]
pub struct SendStreamStats {
    // The total number of bytes the consumer has successfully written to
    // this stream. This number can only increase.
    pub bytes_written: u64,
    // An indicator of progress on how many of the consumer bytes written to
    // this stream has been sent at least once. This number can only increase,
    // and is always less than or equal to bytes_written.
    pub bytes_sent: u64,
    // An indicator of progress on how many of the consumer bytes written to
    // this stream have been sent and acknowledged as received by the server
    // using QUIC’s ACK mechanism. Only sequential bytes up to,
    // but not including, the first non-acknowledged byte, are counted.
    // This number can only increase and is always less than or equal to
    // bytes_sent.
    pub bytes_acked: u64,
}

impl SendStreamStats {
    #[must_use]
    pub const fn new(bytes_written: u64, bytes_sent: u64, bytes_acked: u64) -> Self {
        Self {
            bytes_written,
            bytes_sent,
            bytes_acked,
        }
    }

    #[must_use]
    pub const fn bytes_written(&self) -> u64 {
        self.bytes_written
    }

    #[must_use]
    pub const fn bytes_sent(&self) -> u64 {
        self.bytes_sent
    }

    #[must_use]
    pub const fn bytes_acked(&self) -> u64 {
        self.bytes_acked
    }
}

/// Implement a QUIC send stream.
#[derive(Debug)]
pub struct SendStream {
    stream_id: StreamId,
    state: SendStreamState,
    conn_events: ConnectionEvents,
    priority: TransmissionPriority,
    retransmission_priority: RetransmissionPriority,
    retransmission_offset: u64,
    sendorder: Option<SendOrder>,
    bytes_sent: u64,
    fair: bool,
    writable_event_low_watermark: NonZeroUsize,
}

impl Hash for SendStream {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.stream_id.hash(state);
    }
}

impl PartialEq for SendStream {
    fn eq(&self, other: &Self) -> bool {
        self.stream_id == other.stream_id
    }
}
impl Eq for SendStream {}

impl SendStream {
    #[allow(clippy::missing_panics_doc)] // not possible
    pub fn new(
        stream_id: StreamId,
        max_stream_data: u64,
        conn_fc: Rc<RefCell<SenderFlowControl<()>>>,
        conn_events: ConnectionEvents,
    ) -> Self {
        let ss = Self {
            stream_id,
            state: SendStreamState::Ready {
                fc: SenderFlowControl::new(stream_id, max_stream_data),
                conn_fc,
            },
            conn_events,
            priority: TransmissionPriority::default(),
            retransmission_priority: RetransmissionPriority::default(),
            retransmission_offset: 0,
            sendorder: None,
            bytes_sent: 0,
            fair: false,
            writable_event_low_watermark: 1.try_into().unwrap(),
        };
        if ss.avail() > 0 {
            ss.conn_events.send_stream_writable(stream_id);
        }
        ss
    }

    pub fn write_frames(
        &mut self,
        priority: TransmissionPriority,
        builder: &mut PacketBuilder,
        tokens: &mut Vec<RecoveryToken>,
        stats: &mut FrameStats,
    ) {
        qtrace!("write STREAM frames at priority {:?}", priority);
        if !self.write_reset_frame(priority, builder, tokens, stats) {
            self.write_blocked_frame(priority, builder, tokens, stats);
            self.write_stream_frame(priority, builder, tokens, stats);
        }
    }

    // return false if the builder is full and the caller should stop iterating
    pub fn write_frames_with_early_return(
        &mut self,
        priority: TransmissionPriority,
        builder: &mut PacketBuilder,
        tokens: &mut Vec<RecoveryToken>,
        stats: &mut FrameStats,
    ) -> bool {
        if !self.write_reset_frame(priority, builder, tokens, stats) {
            self.write_blocked_frame(priority, builder, tokens, stats);
            if builder.is_full() {
                return false;
            }
            self.write_stream_frame(priority, builder, tokens, stats);
            if builder.is_full() {
                return false;
            }
        }
        true
    }

    pub fn set_fairness(&mut self, make_fair: bool) {
        self.fair = make_fair;
    }

    #[must_use]
    pub const fn is_fair(&self) -> bool {
        self.fair
    }

    pub fn set_priority(
        &mut self,
        transmission: TransmissionPriority,
        retransmission: RetransmissionPriority,
    ) {
        self.priority = transmission;
        self.retransmission_priority = retransmission;
    }

    #[must_use]
    pub const fn sendorder(&self) -> Option<SendOrder> {
        self.sendorder
    }

    pub fn set_sendorder(&mut self, sendorder: Option<SendOrder>) {
        self.sendorder = sendorder;
    }

    /// If all data has been buffered or written, how much was sent.
    #[must_use]
    pub fn final_size(&self) -> Option<u64> {
        match &self.state {
            SendStreamState::DataSent { send_buf, .. } => Some(send_buf.used()),
            SendStreamState::ResetSent { final_size, .. } => Some(*final_size),
            _ => None,
        }
    }

    #[must_use]
    pub fn stats(&self) -> SendStreamStats {
        SendStreamStats::new(self.bytes_written(), self.bytes_sent, self.bytes_acked())
    }

    #[must_use]
    #[allow(clippy::missing_panics_doc)] // not possible
    pub fn bytes_written(&self) -> u64 {
        match &self.state {
            SendStreamState::Send { send_buf, .. } | SendStreamState::DataSent { send_buf, .. } => {
                send_buf.retired() + u64::try_from(send_buf.buffered()).unwrap()
            }
            SendStreamState::DataRecvd {
                retired, written, ..
            } => *retired + *written,
            SendStreamState::ResetSent {
                final_retired,
                final_written,
                ..
            }
            | SendStreamState::ResetRecvd {
                final_retired,
                final_written,
                ..
            } => *final_retired + *final_written,
            SendStreamState::Ready { .. } => 0,
        }
    }

    #[must_use]
    pub const fn bytes_acked(&self) -> u64 {
        match &self.state {
            SendStreamState::Send { send_buf, .. } | SendStreamState::DataSent { send_buf, .. } => {
                send_buf.retired()
            }
            SendStreamState::DataRecvd { retired, .. } => *retired,
            SendStreamState::ResetSent { final_retired, .. }
            | SendStreamState::ResetRecvd { final_retired, .. } => *final_retired,
            SendStreamState::Ready { .. } => 0,
        }
    }

    /// Return the next range to be sent, if any.
    /// If this is a retransmission, cut off what is sent at the retransmission
    /// offset.
    fn next_bytes(&mut self, retransmission_only: bool) -> Option<(u64, &[u8])> {
        match self.state {
            SendStreamState::Send {
                ref mut send_buf, ..
            } => {
                let result = send_buf.next_bytes();
                if let Some((offset, slice)) = result {
                    if retransmission_only {
                        qtrace!(
                            "next_bytes apply retransmission limit at {}",
                            self.retransmission_offset
                        );
                        if self.retransmission_offset > offset {
                            let len = min(
                                usize::try_from(self.retransmission_offset - offset).unwrap(),
                                slice.len(),
                            );
                            Some((offset, &slice[..len]))
                        } else {
                            None
                        }
                    } else {
                        Some((offset, slice))
                    }
                } else {
                    None
                }
            }
            SendStreamState::DataSent {
                ref mut send_buf,
                fin_sent,
                ..
            } => {
                let used = send_buf.used(); // immutable first
                let bytes = send_buf.next_bytes();
                if bytes.is_some() {
                    bytes
                } else if fin_sent {
                    None
                } else {
                    // Send empty stream frame with fin set
                    Some((used, &[]))
                }
            }
            SendStreamState::Ready { .. }
            | SendStreamState::DataRecvd { .. }
            | SendStreamState::ResetSent { .. }
            | SendStreamState::ResetRecvd { .. } => None,
        }
    }

    /// Calculate how many bytes (length) can fit into available space and whether
    /// the remainder of the space can be filled (or if a length field is needed).
    fn length_and_fill(data_len: usize, space: usize) -> (usize, bool) {
        if data_len >= space {
            // More data than space allows, or an exact fit => fast path.
            qtrace!("SendStream::length_and_fill fill {}", space);
            return (space, true);
        }

        // Estimate size of the length field based on the available space,
        // less 1, which is the worst case.
        let length = min(space.saturating_sub(1), data_len);
        let length_len = Encoder::varint_len(u64::try_from(length).unwrap());
        debug_assert!(length_len <= space); // We don't depend on this being true, but it is true.

        // From here we can always fit `data_len`, but we might as well fill
        // if there is no space for the length field plus another frame.
        let fill = data_len + length_len + PacketBuilder::MINIMUM_FRAME_SIZE > space;
        qtrace!("SendStream::length_and_fill {} fill {}", data_len, fill);
        (data_len, fill)
    }

    /// Maybe write a `STREAM` frame.
    #[allow(clippy::missing_panics_doc)] // not possible
    pub fn write_stream_frame(
        &mut self,
        priority: TransmissionPriority,
        builder: &mut PacketBuilder,
        tokens: &mut Vec<RecoveryToken>,
        stats: &mut FrameStats,
    ) {
        let retransmission = if priority == self.priority {
            false
        } else if priority == self.priority + self.retransmission_priority {
            true
        } else {
            return;
        };

        let id = self.stream_id;
        let final_size = self.final_size();
        if let Some((offset, data)) = self.next_bytes(retransmission) {
            let overhead = 1 // Frame type
                + Encoder::varint_len(id.as_u64())
                + if offset > 0 {
                    Encoder::varint_len(offset)
                } else {
                    0
                };
            if overhead > builder.remaining() {
                qtrace!([self], "write_frame no space for header");
                return;
            }

            let (length, fill) = Self::length_and_fill(data.len(), builder.remaining() - overhead);
            let fin = final_size.map_or(false, |fs| fs == offset + u64::try_from(length).unwrap());
            if length == 0 && !fin {
                qtrace!([self], "write_frame no data, no fin");
                return;
            }

            // Write the stream out.
            builder.encode_varint(Frame::stream_type(fin, offset > 0, fill));
            builder.encode_varint(id.as_u64());
            if offset > 0 {
                builder.encode_varint(offset);
            }
            if fill {
                builder.encode(&data[..length]);
                builder.mark_full();
            } else {
                builder.encode_vvec(&data[..length]);
            }
            debug_assert!(builder.len() <= builder.limit());

            self.mark_as_sent(offset, length, fin);
            tokens.push(RecoveryToken::Stream(StreamRecoveryToken::Stream(
                SendStreamRecoveryToken {
                    id,
                    offset,
                    length,
                    fin,
                },
            )));
            stats.stream += 1;
        }
    }

    pub fn reset_acked(&mut self) {
        match self.state {
            SendStreamState::Ready { .. }
            | SendStreamState::Send { .. }
            | SendStreamState::DataSent { .. }
            | SendStreamState::DataRecvd { .. } => {
                qtrace!([self], "Reset acked while in {} state?", self.state.name());
            }
            SendStreamState::ResetSent {
                final_retired,
                final_written,
                ..
            } => self.state.transition(SendStreamState::ResetRecvd {
                final_retired,
                final_written,
            }),
            SendStreamState::ResetRecvd { .. } => qtrace!([self], "already in ResetRecvd state"),
        };
    }

    pub fn reset_lost(&mut self) {
        match self.state {
            SendStreamState::ResetSent {
                ref mut priority, ..
            } => {
                *priority = Some(self.priority + self.retransmission_priority);
            }
            SendStreamState::ResetRecvd { .. } => (),
            _ => unreachable!(),
        }
    }

    /// Maybe write a `RESET_STREAM` frame.
    pub fn write_reset_frame(
        &mut self,
        p: TransmissionPriority,
        builder: &mut PacketBuilder,
        tokens: &mut Vec<RecoveryToken>,
        stats: &mut FrameStats,
    ) -> bool {
        if let SendStreamState::ResetSent {
            final_size,
            err,
            ref mut priority,
            ..
        } = self.state
        {
            if *priority != Some(p) {
                return false;
            }
            if builder.write_varint_frame(&[
                FRAME_TYPE_RESET_STREAM,
                self.stream_id.as_u64(),
                err,
                final_size,
            ]) {
                tokens.push(RecoveryToken::Stream(StreamRecoveryToken::ResetStream {
                    stream_id: self.stream_id,
                }));
                stats.reset_stream += 1;
                *priority = None;
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    pub fn blocked_lost(&mut self, limit: u64) {
        if let SendStreamState::Ready { fc, .. } | SendStreamState::Send { fc, .. } =
            &mut self.state
        {
            fc.frame_lost(limit);
        } else {
            qtrace!([self], "Ignoring lost STREAM_DATA_BLOCKED({})", limit);
        }
    }

    /// Maybe write a `STREAM_DATA_BLOCKED` frame.
    pub fn write_blocked_frame(
        &mut self,
        priority: TransmissionPriority,
        builder: &mut PacketBuilder,
        tokens: &mut Vec<RecoveryToken>,
        stats: &mut FrameStats,
    ) {
        // Send STREAM_DATA_BLOCKED at normal priority always.
        if priority == self.priority {
            if let SendStreamState::Ready { fc, .. } | SendStreamState::Send { fc, .. } =
                &mut self.state
            {
                fc.write_frames(builder, tokens, stats);
            }
        }
    }

    #[allow(clippy::missing_panics_doc)] // not possible
    pub fn mark_as_sent(&mut self, offset: u64, len: usize, fin: bool) {
        self.bytes_sent = max(self.bytes_sent, offset + u64::try_from(len).unwrap());

        if let Some(buf) = self.state.tx_buf_mut() {
            buf.mark_as_sent(offset, len);
            self.send_blocked_if_space_needed(0);
        };

        if fin {
            if let SendStreamState::DataSent { fin_sent, .. } = &mut self.state {
                *fin_sent = true;
            }
        }
    }

    #[allow(clippy::missing_panics_doc)] // not possible
    pub fn mark_as_acked(&mut self, offset: u64, len: usize, fin: bool) {
        match self.state {
            SendStreamState::Send {
                ref mut send_buf, ..
            } => {
                let previous_limit = send_buf.avail();
                send_buf.mark_as_acked(offset, len);
                let current_limit = send_buf.avail();
                self.maybe_emit_writable_event(previous_limit, current_limit);
            }
            SendStreamState::DataSent {
                ref mut send_buf,
                ref mut fin_acked,
                ..
            } => {
                send_buf.mark_as_acked(offset, len);
                if fin {
                    *fin_acked = true;
                }
                if *fin_acked && send_buf.buffered() == 0 {
                    self.conn_events.send_stream_complete(self.stream_id);
                    let retired = send_buf.retired();
                    let buffered = u64::try_from(send_buf.buffered()).unwrap();
                    self.state.transition(SendStreamState::DataRecvd {
                        retired,
                        written: buffered,
                    });
                }
            }
            _ => qtrace!(
                [self],
                "mark_as_acked called from state {}",
                self.state.name()
            ),
        }
    }

    #[allow(clippy::missing_panics_doc)] // not possible
    pub fn mark_as_lost(&mut self, offset: u64, len: usize, fin: bool) {
        self.retransmission_offset = max(
            self.retransmission_offset,
            offset + u64::try_from(len).unwrap(),
        );
        qtrace!(
            [self],
            "mark_as_lost retransmission offset={}",
            self.retransmission_offset
        );
        if let Some(buf) = self.state.tx_buf_mut() {
            buf.mark_as_lost(offset, len);
        }

        if fin {
            if let SendStreamState::DataSent {
                fin_sent,
                fin_acked,
                ..
            } = &mut self.state
            {
                *fin_sent = *fin_acked;
            }
        }
    }

    /// Bytes sendable on stream. Constrained by stream credit available,
    /// connection credit available, and space in the tx buffer.
    #[must_use]
    pub fn avail(&self) -> usize {
        if let SendStreamState::Ready { fc, conn_fc } | SendStreamState::Send { fc, conn_fc, .. } =
            &self.state
        {
            min(
                min(fc.available(), conn_fc.borrow().available()),
                self.state.tx_avail(),
            )
        } else {
            0
        }
    }

    /// Set low watermark for [`crate::ConnectionEvent::SendStreamWritable`]
    /// event.
    ///
    /// See [`crate::Connection::stream_set_writable_event_low_watermark`].
    pub fn set_writable_event_low_watermark(&mut self, watermark: NonZeroUsize) {
        self.writable_event_low_watermark = watermark;
    }

    pub fn set_max_stream_data(&mut self, limit: u64) {
        if let SendStreamState::Ready { fc, .. } | SendStreamState::Send { fc, .. } =
            &mut self.state
        {
            let previous_limit = fc.available();
            if let Some(current_limit) = fc.update(limit) {
                self.maybe_emit_writable_event(previous_limit, current_limit);
            }
        }
    }

    #[must_use]
    pub const fn is_terminal(&self) -> bool {
        matches!(
            self.state,
            SendStreamState::DataRecvd { .. } | SendStreamState::ResetRecvd { .. }
        )
    }

    /// # Errors
    /// When `buf` is empty or when the stream is already closed.
    pub fn send(&mut self, buf: &[u8]) -> Res<usize> {
        self.send_internal(buf, false)
    }

    /// # Errors
    /// When `buf` is empty or when the stream is already closed.
    pub fn send_atomic(&mut self, buf: &[u8]) -> Res<usize> {
        self.send_internal(buf, true)
    }

    fn send_blocked_if_space_needed(&mut self, needed_space: usize) {
        if let SendStreamState::Ready { fc, conn_fc } | SendStreamState::Send { fc, conn_fc, .. } =
            &mut self.state
        {
            if fc.available() <= needed_space {
                fc.blocked();
            }

            if conn_fc.borrow().available() <= needed_space {
                conn_fc.borrow_mut().blocked();
            }
        }
    }

    fn send_internal(&mut self, buf: &[u8], atomic: bool) -> Res<usize> {
        if buf.is_empty() {
            qerror!([self], "zero-length send on stream");
            return Err(Error::InvalidInput);
        }

        if let SendStreamState::Ready { fc, conn_fc } = &mut self.state {
            let owned_fc = mem::replace(fc, SenderFlowControl::new(self.stream_id, 0));
            let owned_conn_fc = Rc::clone(conn_fc);
            self.state.transition(SendStreamState::Send {
                fc: owned_fc,
                conn_fc: owned_conn_fc,
                send_buf: TxBuffer::new(),
            });
        }

        if !matches!(self.state, SendStreamState::Send { .. }) {
            return Err(Error::FinalSizeError);
        }

        let buf = if self.avail() == 0 {
            return Ok(0);
        } else if self.avail() < buf.len() {
            if atomic {
                self.send_blocked_if_space_needed(buf.len());
                return Ok(0);
            }

            &buf[..self.avail()]
        } else {
            buf
        };

        match &mut self.state {
            SendStreamState::Ready { .. } => unreachable!(),
            SendStreamState::Send {
                fc,
                conn_fc,
                send_buf,
            } => {
                let sent = send_buf.send(buf);
                fc.consume(sent);
                conn_fc.borrow_mut().consume(sent);
                Ok(sent)
            }
            _ => Err(Error::FinalSizeError),
        }
    }

    pub fn close(&mut self) {
        match &mut self.state {
            SendStreamState::Ready { .. } => {
                self.state.transition(SendStreamState::DataSent {
                    send_buf: TxBuffer::new(),
                    fin_sent: false,
                    fin_acked: false,
                });
            }
            SendStreamState::Send { send_buf, .. } => {
                let owned_buf = mem::replace(send_buf, TxBuffer::new());
                self.state.transition(SendStreamState::DataSent {
                    send_buf: owned_buf,
                    fin_sent: false,
                    fin_acked: false,
                });
            }
            SendStreamState::DataSent { .. } => qtrace!([self], "already in DataSent state"),
            SendStreamState::DataRecvd { .. } => qtrace!([self], "already in DataRecvd state"),
            SendStreamState::ResetSent { .. } => qtrace!([self], "already in ResetSent state"),
            SendStreamState::ResetRecvd { .. } => qtrace!([self], "already in ResetRecvd state"),
        }
    }

    #[allow(clippy::missing_panics_doc)] // not possible
    pub fn reset(&mut self, err: AppError) {
        match &self.state {
            SendStreamState::Ready { fc, .. } => {
                let final_size = fc.used();
                self.state.transition(SendStreamState::ResetSent {
                    err,
                    final_size,
                    priority: Some(self.priority),
                    final_retired: 0,
                    final_written: 0,
                });
            }
            SendStreamState::Send { fc, send_buf, .. } => {
                let final_size = fc.used();
                let final_retired = send_buf.retired();
                let buffered = u64::try_from(send_buf.buffered()).unwrap();
                self.state.transition(SendStreamState::ResetSent {
                    err,
                    final_size,
                    priority: Some(self.priority),
                    final_retired,
                    final_written: buffered,
                });
            }
            SendStreamState::DataSent { send_buf, .. } => {
                let final_size = send_buf.used();
                let final_retired = send_buf.retired();
                let buffered = u64::try_from(send_buf.buffered()).unwrap();
                self.state.transition(SendStreamState::ResetSent {
                    err,
                    final_size,
                    priority: Some(self.priority),
                    final_retired,
                    final_written: buffered,
                });
            }
            SendStreamState::DataRecvd { .. } => qtrace!([self], "already in DataRecvd state"),
            SendStreamState::ResetSent { .. } => qtrace!([self], "already in ResetSent state"),
            SendStreamState::ResetRecvd { .. } => qtrace!([self], "already in ResetRecvd state"),
        };
    }

    #[cfg(test)]
    pub(crate) fn state(&mut self) -> &mut SendStreamState {
        &mut self.state
    }

    pub(crate) fn maybe_emit_writable_event(&self, previous_limit: usize, current_limit: usize) {
        let low_watermark = self.writable_event_low_watermark.get();

        // Skip if:
        // - stream was not constrained by limit before,
        // - or stream is still constrained by limit,
        // - or stream is constrained by different limit.
        if low_watermark < previous_limit
            || current_limit < low_watermark
            || self.avail() < low_watermark
        {
            return;
        }

        self.conn_events.send_stream_writable(self.stream_id);
    }
}

impl ::std::fmt::Display for SendStream {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "SendStream {}", self.stream_id)
    }
}

#[derive(Debug, Default)]
pub struct OrderGroup {
    // This vector is sorted by StreamId
    vec: Vec<StreamId>,

    // Since we need to remember where we were, we'll store the iterator next
    // position in the object.  This means there can only be a single iterator active
    // at a time!
    next: usize,
    // This is used when an iterator is created to set the start/stop point for the
    // iteration.  The iterator must iterate from this entry to the end, and then
    // wrap and iterate from 0 until before the initial value of next.
    // This value may need to be updated after insertion and removal; in theory we should
    // track the target entry across modifications, but in practice it should be good
    // enough to simply leave it alone unless it points past the end of the
    // Vec, and re-initialize to 0 in that case.
}

pub struct OrderGroupIter<'a> {
    group: &'a mut OrderGroup,
    // We store the next position in the OrderGroup.
    // Otherwise we'd need an explicit "done iterating" call to be made, or implement Drop to
    // copy the value back.
    // This is where next was when we iterated for the first time; when we get back to that we
    // stop.
    started_at: Option<usize>,
}

impl OrderGroup {
    pub fn iter(&mut self) -> OrderGroupIter {
        // Ids may have been deleted since we last iterated
        if self.next >= self.vec.len() {
            self.next = 0;
        }
        OrderGroupIter {
            started_at: None,
            group: self,
        }
    }

    #[must_use]
    pub const fn stream_ids(&self) -> &Vec<StreamId> {
        &self.vec
    }

    pub fn clear(&mut self) {
        self.vec.clear();
    }

    pub fn push(&mut self, stream_id: StreamId) {
        self.vec.push(stream_id);
    }

    #[cfg(test)]
    pub fn truncate(&mut self, position: usize) {
        self.vec.truncate(position);
    }

    fn update_next(&mut self) -> usize {
        let next = self.next;
        self.next = (self.next + 1) % self.vec.len();
        next
    }

    /// # Panics
    /// If the stream ID is already present.
    pub fn insert(&mut self, stream_id: StreamId) {
        let Err(pos) = self.vec.binary_search(&stream_id) else {
            // element already in vector @ `pos`
            panic!("Duplicate stream_id {stream_id}");
        };
        self.vec.insert(pos, stream_id);
    }

    /// # Panics
    /// If the stream ID is not present.
    pub fn remove(&mut self, stream_id: StreamId) {
        let Ok(pos) = self.vec.binary_search(&stream_id) else {
            // element already in vector @ `pos`
            panic!("Missing stream_id {stream_id}");
        };
        self.vec.remove(pos);
    }
}

impl<'a> Iterator for OrderGroupIter<'a> {
    type Item = StreamId;
    fn next(&mut self) -> Option<Self::Item> {
        // Stop when we would return the started_at element on the next
        // call.  Note that this must take into account wrapping.
        if self.started_at == Some(self.group.next) || self.group.vec.is_empty() {
            return None;
        }
        self.started_at = self.started_at.or(Some(self.group.next));
        let orig = self.group.update_next();
        Some(self.group.vec[orig])
    }
}

#[derive(Debug, Default)]
pub struct SendStreams {
    map: IndexMap<StreamId, SendStream>,

    // What we really want is a Priority Queue that we can do arbitrary
    // removes from (so we can reprioritize). BinaryHeap doesn't work,
    // because there's no remove().  BTreeMap doesn't work, since you can't
    // duplicate keys.  PriorityQueue does have what we need, except for an
    // ordered iterator that doesn't consume the queue.  So we roll our own.

    // Added complication: We want to have Fairness for streams of the same
    // 'group' (for WebTransport), but for H3 (and other non-WT streams) we
    // tend to get better pageload performance by prioritizing by creation order.
    //
    // Two options are to walk the 'map' first, ignoring WebTransport
    // streams, then process the unordered and ordered WebTransport
    // streams.  The second is to have a sorted Vec for unfair streams (and
    // use a normal iterator for that), and then chain the iterators for
    // the unordered and ordered WebTranport streams.  The first works very
    // well for H3, and for WebTransport nodes are visited twice on every
    // processing loop.  The second adds insertion and removal costs, but
    // avoids a CPU penalty for WebTransport streams.  For now we'll do #1.
    //
    // So we use a sorted Vec<> for the regular streams (that's usually all of
    // them), and then a BTreeMap of an entry for each SendOrder value, and
    // for each of those entries a Vec of the stream_ids at that
    // sendorder.  In most cases (such as stream-per-frame), there will be
    // a single stream at a given sendorder.

    // These both store stream_ids, which need to be looked up in 'map'.
    // This avoids the complexity of trying to hold references to the
    // Streams which are owned by the IndexMap.
    sendordered: BTreeMap<SendOrder, OrderGroup>,
    regular: OrderGroup, // streams with no SendOrder set, sorted in stream_id order
}

impl SendStreams {
    #[allow(clippy::missing_errors_doc)]
    pub fn get(&self, id: StreamId) -> Res<&SendStream> {
        self.map.get(&id).ok_or(Error::InvalidStreamId)
    }

    #[allow(clippy::missing_errors_doc)]
    pub fn get_mut(&mut self, id: StreamId) -> Res<&mut SendStream> {
        self.map.get_mut(&id).ok_or(Error::InvalidStreamId)
    }

    #[must_use]
    pub fn exists(&self, id: StreamId) -> bool {
        self.map.contains_key(&id)
    }

    pub fn insert(&mut self, id: StreamId, stream: SendStream) {
        self.map.insert(id, stream);
    }

    fn group_mut(&mut self, sendorder: Option<SendOrder>) -> &mut OrderGroup {
        if let Some(order) = sendorder {
            self.sendordered.entry(order).or_default()
        } else {
            &mut self.regular
        }
    }

    #[allow(clippy::missing_panics_doc)]
    #[allow(clippy::missing_errors_doc)]
    pub fn set_sendorder(&mut self, stream_id: StreamId, sendorder: Option<SendOrder>) -> Res<()> {
        self.set_fairness(stream_id, true)?;
        if let Some(stream) = self.map.get_mut(&stream_id) {
            // don't grab stream here; causes borrow errors
            let old_sendorder = stream.sendorder();
            if old_sendorder != sendorder {
                // we have to remove it from the list it was in, and reinsert it with the new
                // sendorder key
                let mut group = self.group_mut(old_sendorder);
                group.remove(stream_id);
                self.get_mut(stream_id).unwrap().set_sendorder(sendorder);
                group = self.group_mut(sendorder);
                group.insert(stream_id);
                qtrace!(
                    "ordering of stream_ids: {:?}",
                    self.sendordered.values().collect::<Vec::<_>>()
                );
            }
            Ok(())
        } else {
            Err(Error::InvalidStreamId)
        }
    }

    #[allow(clippy::missing_panics_doc)]
    #[allow(clippy::missing_errors_doc)]
    pub fn set_fairness(&mut self, stream_id: StreamId, make_fair: bool) -> Res<()> {
        let stream: &mut SendStream = self.map.get_mut(&stream_id).ok_or(Error::InvalidStreamId)?;
        let was_fair = stream.fair;
        stream.set_fairness(make_fair);
        if !was_fair && make_fair {
            // Move to the regular OrderGroup.

            // We know sendorder can't have been set, since
            // set_sendorder() will call this routine if it's not
            // already set as fair.

            // This normally is only called when a new stream is created.  If
            // so, because of how we allocate StreamIds, it should always have
            // the largest value.  This means we can just append it to the
            // regular vector.  However, if we were ever to change this
            // invariant, things would break subtly.

            // To be safe we can try to insert at the end and if not
            // fall back to binary-search insertion
            if matches!(self.regular.stream_ids().last(), Some(last) if stream_id > *last) {
                self.regular.push(stream_id);
            } else {
                self.regular.insert(stream_id);
            }
        } else if was_fair && !make_fair {
            // remove from the OrderGroup
            let group = if let Some(sendorder) = stream.sendorder {
                self.sendordered.get_mut(&sendorder).unwrap()
            } else {
                &mut self.regular
            };
            group.remove(stream_id);
        }
        Ok(())
    }

    pub fn acked(&mut self, token: &SendStreamRecoveryToken) {
        if let Some(ss) = self.map.get_mut(&token.id) {
            ss.mark_as_acked(token.offset, token.length, token.fin);
        }
    }

    pub fn reset_acked(&mut self, id: StreamId) {
        if let Some(ss) = self.map.get_mut(&id) {
            ss.reset_acked();
        }
    }

    pub fn lost(&mut self, token: &SendStreamRecoveryToken) {
        if let Some(ss) = self.map.get_mut(&token.id) {
            ss.mark_as_lost(token.offset, token.length, token.fin);
        }
    }

    pub fn reset_lost(&mut self, stream_id: StreamId) {
        if let Some(ss) = self.map.get_mut(&stream_id) {
            ss.reset_lost();
        }
    }

    pub fn blocked_lost(&mut self, stream_id: StreamId, limit: u64) {
        if let Some(ss) = self.map.get_mut(&stream_id) {
            ss.blocked_lost(limit);
        }
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.sendordered.clear();
        self.regular.clear();
    }

    #[allow(clippy::missing_panics_doc)]
    pub fn remove_terminal(&mut self) {
        self.map.retain(|stream_id, stream| {
            if stream.is_terminal() {
                if stream.is_fair() {
                    match stream.sendorder() {
                        None => self.regular.remove(*stream_id),
                        Some(sendorder) => {
                            self.sendordered
                                .get_mut(&sendorder)
                                .unwrap()
                                .remove(*stream_id);
                        }
                    };
                }
                // if unfair, we're done
                return false;
            }
            true
        });
    }

    pub(crate) fn write_frames(
        &mut self,
        priority: TransmissionPriority,
        builder: &mut PacketBuilder,
        tokens: &mut Vec<RecoveryToken>,
        stats: &mut FrameStats,
    ) {
        qtrace!("write STREAM frames at priority {:?}", priority);
        // WebTransport data (which is Normal) may have a SendOrder
        // priority attached.  The spec states (6.3 write-chunk 6.1):

        // First, we send any streams without Fairness defined, with
        // ordering defined by StreamId.  (Http3 streams used for
        // e.g. pageload benefit from being processed in order of creation
        // so the far side can start acting on a datum/request sooner. All
        // WebTransport streams MUST have fairness set.)  Then we send
        // streams with fairness set (including all WebTransport streams)
        // as follows:

        // If stream.[[SendOrder]] is null then this sending MUST NOT
        // starve except for flow control reasons or error.  If
        // stream.[[SendOrder]] is not null then this sending MUST starve
        // until all bytes queued for sending on WebTransportSendStreams
        // with a non-null and higher [[SendOrder]], that are neither
        // errored nor blocked by flow control, have been sent.

        // So data without SendOrder goes first.   Then the highest priority
        // SendOrdered streams.
        //
        // Fairness is implemented by a round-robining or "statefully
        // iterating" within a single sendorder/unordered vector.  We do
        // this by recording where we stopped in the previous pass, and
        // starting there the next pass.  If we store an index into the
        // vec, this means we can't use a chained iterator, since we want
        // to retain our place-in-the-vector.  If we rotate the vector,
        // that would let us use the chained iterator, but would require
        // more expensive searches for insertion and removal (since the
        // sorted order would be lost).

        // Iterate the map, but only those without fairness, then iterate
        // OrderGroups, then iterate each group
        qtrace!("processing streams...  unfair:");
        for stream in self.map.values_mut() {
            if !stream.is_fair() {
                qtrace!("   {}", stream);
                if !stream.write_frames_with_early_return(priority, builder, tokens, stats) {
                    break;
                }
            }
        }
        qtrace!("fair streams:");
        let stream_ids = self.regular.iter().chain(
            self.sendordered
                .values_mut()
                .rev()
                .flat_map(|group| group.iter()),
        );
        for stream_id in stream_ids {
            let stream = self.map.get_mut(&stream_id).unwrap();
            if let Some(order) = stream.sendorder() {
                qtrace!("   {} ({})", stream_id, order);
            } else {
                qtrace!("   None");
            }
            if !stream.write_frames_with_early_return(priority, builder, tokens, stats) {
                break;
            }
        }
    }

    #[allow(clippy::missing_panics_doc)]
    pub fn update_initial_limit(&mut self, remote: &TransportParameters) {
        for (id, ss) in &mut self.map {
            let limit = if id.is_bidi() {
                assert!(!id.is_remote_initiated(Role::Client));
                remote.get_integer(tparams::INITIAL_MAX_STREAM_DATA_BIDI_REMOTE)
            } else {
                remote.get_integer(tparams::INITIAL_MAX_STREAM_DATA_UNI)
            };
            ss.set_max_stream_data(limit);
        }
    }
}

#[allow(clippy::into_iter_without_iter)]
impl<'a> IntoIterator for &'a mut SendStreams {
    type Item = (&'a StreamId, &'a mut SendStream);
    type IntoIter = indexmap::map::IterMut<'a, StreamId, SendStream>;

    fn into_iter(self) -> indexmap::map::IterMut<'a, StreamId, SendStream> {
        self.map.iter_mut()
    }
}

#[derive(Debug, Clone)]
pub struct SendStreamRecoveryToken {
    pub(crate) id: StreamId,
    offset: u64,
    length: usize,
    fin: bool,
}
