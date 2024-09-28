// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(clippy::missing_errors_doc)] // Functions simply delegate to tokio and quinn-udp.

use std::{
    io::{self, IoSliceMut},
    net::SocketAddr,
    slice,
};

use neqo_common::{qdebug, qtrace, Datagram, IpTos};
use quinn_udp::{EcnCodepoint, RecvMeta, Transmit, UdpSocketState};

/// Socket receive buffer size.
///
/// Allows reading multiple datagrams in a single [`Socket::recv`] call.
//
// TODO: Experiment with different values across platforms.
pub const RECV_BUF_SIZE: usize = u16::MAX as usize;

pub fn send_inner(
    state: &UdpSocketState,
    socket: quinn_udp::UdpSockRef<'_>,
    d: Datagram<&[u8]>,
) -> io::Result<()> {
    let transmit = Transmit {
        destination: d.destination(),
        ecn: EcnCodepoint::from_bits(Into::<u8>::into(d.tos())),
        contents: d.as_ref(),
        segment_size: Some(d.segment_size()),
        src_ip: None,
    };

    state.send(socket, &transmit)?;

    qtrace!(
        "sent {} bytes from {} to {}",
        d.len(),
        d.source(),
        d.destination()
    );

    Ok(())
}

#[cfg(unix)]
use std::os::fd::AsFd as SocketRef;
#[cfg(windows)]
use std::os::windows::io::AsSocket as SocketRef;

pub fn recv_inner<'a>(
    local_address: &SocketAddr,
    state: &UdpSocketState,
    socket: impl SocketRef,
    recv_buf: &'a mut Vec<u8>,
) -> Result<Datagram<&'a [u8]>, io::Error> {
    let mut meta;

    let data = loop {
        meta = RecvMeta::default();

        state.recv(
            (&socket).into(),
            &mut [IoSliceMut::new(recv_buf.as_mut())],
            slice::from_mut(&mut meta),
        )?;

        if meta.len == 0 || meta.stride == 0 {
            qdebug!(
                "ignoring datagram from {} to {} len {} stride {}",
                meta.addr,
                local_address,
                meta.len,
                meta.stride
            );
            continue;
        }

        break &recv_buf[..meta.len];
    };

    qtrace!(
        "received {} bytes from {} to {} with {} segments",
        data.len(),
        meta.addr,
        local_address,
        meta.len.div_ceil(meta.stride),
    );

    Ok(Datagram::new(
        meta.addr,
        *local_address,
        meta.ecn.map(|n| IpTos::from(n as u8)).unwrap_or_default(),
        data,
        Some(meta.stride),
    ))
}

/// A wrapper around a UDP socket, sending and receiving [`Datagram`]s.
pub struct Socket<S> {
    state: UdpSocketState,
    inner: S,
}

impl<S: SocketRef> Socket<S> {
    /// Create a new [`Socket`] given a raw file descriptor managed externally.
    pub fn new(socket: S) -> Result<Self, io::Error> {
        Ok(Self {
            state: quinn_udp::UdpSocketState::new((&socket).into())?,
            inner: socket,
        })
    }

    /// Send a [`Datagram`] on the given [`Socket`].
    pub fn send(&self, d: Datagram<&[u8]>) -> io::Result<()> {
        send_inner(&self.state, (&self.inner).into(), d)
    }

    /// Receive a batch of [`Datagram`]s on the given [`Socket`], each
    /// set with the provided local address.
    pub fn recv<'a>(
        &self,
        local_address: &SocketAddr,
        recv_buf: &'a mut Vec<u8>,
    ) -> Result<Datagram<&'a [u8]>, io::Error> {
        recv_inner(local_address, &self.state, &self.inner, recv_buf)
    }
}

#[cfg(test)]
mod tests {
    use neqo_common::{IpTosDscp, IpTosEcn};

    use super::*;

    fn socket() -> Result<Socket<std::net::UdpSocket>, io::Error> {
        let socket = Socket::new(std::net::UdpSocket::bind("127.0.0.1:0")?)?;
        // Reverse non-blocking flag set by `UdpSocketState` to make the test non-racy.
        socket.inner.set_nonblocking(false)?;
        Ok(socket)
    }

    #[test]
    fn ignore_empty_datagram() -> Result<(), io::Error> {
        let sender = socket()?;
        let receiver = Socket::new(std::net::UdpSocket::bind("127.0.0.1:0")?)?;
        let receiver_addr: SocketAddr = "127.0.0.1:0".parse().unwrap();

        let payload = vec![];
        let datagram = Datagram::new(
            sender.inner.local_addr()?,
            receiver.inner.local_addr()?,
            IpTos::default(),
            payload.as_slice(),
            None,
        );

        sender.send(datagram)?;
        let mut recv_buf = vec![0; RECV_BUF_SIZE];
        let res = receiver.recv(&receiver_addr, &mut recv_buf);
        assert_eq!(res.unwrap_err().kind(), std::io::ErrorKind::WouldBlock);

        Ok(())
    }

    #[test]
    fn datagram_tos() -> Result<(), io::Error> {
        let sender = socket()?;
        let receiver = socket()?;
        let receiver_addr: SocketAddr = "127.0.0.1:0".parse().unwrap();

        let payload = b"Hello, world!".to_vec();
        let datagram = Datagram::new(
            sender.inner.local_addr()?,
            receiver.inner.local_addr()?,
            IpTos::from((IpTosDscp::Le, IpTosEcn::Ect1)),
            payload.as_slice(),
            None,
        );

        sender.send(datagram)?;

        let mut recv_buf = vec![0; RECV_BUF_SIZE];
        let received_datagram = receiver
            .recv(&receiver_addr, &mut recv_buf)
            .expect("receive to succeed");

        // Assert that the ECN is correct.
        assert_eq!(
            IpTosEcn::from(datagram.tos()),
            IpTosEcn::from(received_datagram.tos())
        );

        Ok(())
    }

    // TODO: Cleanup test
    #[test]
    fn gso() -> Result<(), io::Error> {
        let sender = socket()?;
        let receiver = socket()?;
        let receiver_addr: SocketAddr = "127.0.0.1:0".parse().unwrap();

        let payload = vec![0; 2 * 1500];

        let datagram = Datagram::new(
            sender.inner.local_addr()?,
            receiver.inner.local_addr()?,
            IpTos::from((IpTosDscp::Le, IpTosEcn::Ect1)),
            payload.as_slice(),
            Some(1500),
        );

        sender.send(datagram)?;

        let mut recv_buf = vec![0; RECV_BUF_SIZE * 2];
        let received_datagram = receiver
            .recv(&receiver_addr, &mut recv_buf)
            .expect("receive to succeed");

        // Assert that the ECN is correct.
        assert_eq!(received_datagram.num_segments(), 2);

        Ok(())
    }

    /// Expect [`Socket::recv`] to handle multiple [`Datagram`]s on GRO read.
    #[test]
    #[cfg_attr(not(any(target_os = "linux", target_os = "windows")), ignore)]
    fn many_datagrams_through_gro() -> Result<(), io::Error> {
        const SEGMENT_SIZE: usize = 128;

        let sender = socket()?;
        let receiver = socket()?;
        let receiver_addr: SocketAddr = "127.0.0.1:0".parse().unwrap();

        // TODO: It does now.
        // `neqo_udp::Socket::send` does not yet
        // (https://github.com/mozilla/neqo/issues/1693) support GSO. Use
        // `quinn_udp` directly.
        let max_gso_segments = sender.state.max_gso_segments();
        let msg = vec![0xAB; SEGMENT_SIZE * max_gso_segments];
        let transmit = Transmit {
            destination: receiver.inner.local_addr()?,
            ecn: EcnCodepoint::from_bits(Into::<u8>::into(IpTos::from((
                IpTosDscp::Le,
                IpTosEcn::Ect1,
            )))),
            contents: &msg,
            segment_size: Some(SEGMENT_SIZE),
            src_ip: None,
        };
        sender.state.send((&sender.inner).into(), &transmit)?;

        // Allow for one GSO sendmmsg to result in multiple GRO recvmmsg.
        let mut num_received = 0;
        let mut recv_buf = vec![0; RECV_BUF_SIZE];
        while num_received < max_gso_segments {
            recv_buf.clear();
            let dgram = receiver
                .recv(&receiver_addr, &mut recv_buf)
                .expect("receive to succeed");
            assert_eq!(
                SEGMENT_SIZE,
                dgram.segment_size(),
                "Expect received datagrams to have same length as sent datagrams."
            );
            num_received += dgram.num_segments();
        }

        Ok(())
    }
}
