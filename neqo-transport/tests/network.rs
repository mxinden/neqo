// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::{ops::Range, time::Duration};

use neqo_transport::{CloseReason, ConnectionParameters, Error, State};
use test_fixture::{
    boxed,
    sim::{
        connection::{ConnectionNode, ReachState, ReceiveData, SendData},
        network::{Delay, Drop, NonRandomDelay, TailDrop},
        Simulator,
    },
    simulate,
};

/// The amount of transfer.  Much more than this takes a surprising amount of time.
const TRANSFER_AMOUNT: usize = 1 << 20; // 1M
const ZERO: Duration = Duration::from_millis(0);
const DELAY: Duration = Duration::from_millis(50);
const DELAY_RANGE: Range<Duration> = DELAY..Duration::from_millis(55);
const JITTER: Duration = Duration::from_millis(10);

const fn weeks(m: u32) -> Duration {
    Duration::from_secs((m as u64) * 60 * 60 * 24 * 7)
}

simulate!(
    connect_direct,
    [
        ConnectionNode::new_client(
            ConnectionParameters::default(),
            [],
            boxed![ReachState::new(State::Confirmed)]
        ),
        ConnectionNode::new_server(
            ConnectionParameters::default(),
            [],
            boxed![ReachState::new(State::Confirmed)]
        ),
    ]
);

simulate!(
    idle_timeout,
    [
        ConnectionNode::default_client(boxed![ReachState::new(State::Closed(
            CloseReason::Transport(Error::IdleTimeout)
        ))]),
        ConnectionNode::default_server(boxed![ReachState::new(State::Closed(
            CloseReason::Transport(Error::IdleTimeout)
        ))]),
    ]
);

simulate!(
    idle_timeout_crazy_rtt,
    [
        ConnectionNode::new_client(
            ConnectionParameters::default().idle_timeout(weeks(1000)),
            boxed![ReachState::new(State::Confirmed),],
            boxed![ReachState::new(State::Closed(CloseReason::Transport(
                Error::IdleTimeout
            )))]
        ),
        Delay::new(weeks(6)..weeks(6)),
        Drop::percentage(10),
        ConnectionNode::new_server(
            ConnectionParameters::default().idle_timeout(weeks(1000)),
            boxed![ReachState::new(State::Confirmed),],
            boxed![ReachState::new(State::Closed(CloseReason::Transport(
                Error::IdleTimeout
            )))]
        ),
        Delay::new(weeks(8)..weeks(8)),
        Drop::percentage(10),
    ],
);

simulate!(
    transfer,
    [
        ConnectionNode::default_client(boxed![SendData::new(TRANSFER_AMOUNT)]),
        ConnectionNode::default_server(boxed![ReceiveData::new(TRANSFER_AMOUNT)]),
    ]
);

simulate!(
    connect_fixed_rtt,
    [
        ConnectionNode::new_client(
            ConnectionParameters::default(),
            [],
            boxed![ReachState::new(State::Confirmed)]
        ),
        Delay::new(DELAY..DELAY),
        ConnectionNode::new_server(
            ConnectionParameters::default(),
            [],
            boxed![ReachState::new(State::Confirmed)]
        ),
        Delay::new(DELAY..DELAY),
    ],
);

simulate!(
    connect_taildrop_jitter,
    [
        ConnectionNode::new_client(
            ConnectionParameters::default(),
            [],
            boxed![ReachState::new(State::Confirmed)]
        ),
        TailDrop::dsl_downlink(),
        Delay::new(ZERO..JITTER),
        ConnectionNode::new_server(
            ConnectionParameters::default(),
            [],
            boxed![ReachState::new(State::Confirmed)]
        ),
        TailDrop::dsl_uplink(),
        Delay::new(ZERO..JITTER),
    ],
);

simulate!(
    connect_taildrop,
    [
        ConnectionNode::new_client(
            ConnectionParameters::default(),
            [],
            boxed![ReachState::new(State::Confirmed)]
        ),
        TailDrop::dsl_downlink(),
        ConnectionNode::new_server(
            ConnectionParameters::default(),
            [],
            boxed![ReachState::new(State::Confirmed)]
        ),
        TailDrop::dsl_uplink(),
    ],
);

simulate!(
    transfer_delay_drop,
    [
        ConnectionNode::default_client(boxed![SendData::new(TRANSFER_AMOUNT)]),
        Delay::new(DELAY_RANGE),
        Drop::percentage(1),
        ConnectionNode::default_server(boxed![ReceiveData::new(TRANSFER_AMOUNT)]),
        Delay::new(DELAY_RANGE),
        Drop::percentage(1),
    ],
);

simulate!(
    transfer_taildrop,
    [
        ConnectionNode::default_client(boxed![SendData::new(TRANSFER_AMOUNT)]),
        TailDrop::dsl_downlink(),
        ConnectionNode::default_server(boxed![ReceiveData::new(TRANSFER_AMOUNT)]),
        TailDrop::dsl_uplink(),
    ],
);

simulate!(
    transfer_taildrop_jitter,
    [
        ConnectionNode::default_client(boxed![SendData::new(TRANSFER_AMOUNT)]),
        TailDrop::dsl_downlink(),
        Delay::new(ZERO..JITTER),
        ConnectionNode::default_server(boxed![ReceiveData::new(TRANSFER_AMOUNT)]),
        TailDrop::dsl_uplink(),
        Delay::new(ZERO..JITTER),
    ],
);

/// This test is a nasty piece of work.  Delays are anything from 0 to 50ms and 1% of
/// packets get dropped.
#[test]
fn transfer_fixed_seed() {
    let mut sim = Simulator::new(
        "transfer_fixed_seed",
        boxed![
            ConnectionNode::default_client(boxed![SendData::new(TRANSFER_AMOUNT)]),
            Delay::new(ZERO..DELAY),
            Drop::percentage(1),
            ConnectionNode::default_server(boxed![ReceiveData::new(TRANSFER_AMOUNT)]),
            Delay::new(ZERO..DELAY),
            Drop::percentage(1),
        ],
    );
    sim.seed_str("117f65d90ee5c1a7fb685f3af502c7730ba5d31866b758d98f5e3c2117cf9b86");
    sim.run();
}

#[test]
fn unlimited_bandwidth_50ms_delay_connection() {
    // TODO: Not tenable as a unit test today, given that this will take roughly 300s
    // of wallclock time to execute on the simulator. Large for now to make sure
    // congestion control isn't the limiting factor.
    const TRANSFER_AMOUNT: usize = 50 * 1024 * 1024;
    // One way delay of 25ms, thus RTT of 50ms.
    const DELAY: Duration = Duration::from_millis(25);

    let mut sim = Simulator::new(
        "unlimited_bandwidth_50ms_delay_connection",
        boxed![
            ConnectionNode::default_client(boxed![SendData::new(TRANSFER_AMOUNT)]),
            NonRandomDelay::new(DELAY),
            ConnectionNode::default_server(boxed![ReceiveData::new(TRANSFER_AMOUNT)]),
            NonRandomDelay::new(DELAY),
        ],
    );
    // TODO: Shouldn't matter. No packet loss. Ideally no randomness in delay.
    sim.seed_str("117f65d90ee5c1a7fb685f3af502c7730ba5d31866b758d98f5e3c2117cf9b86");

    let simulated_time = sim.setup().run();
    let bandwidth = TRANSFER_AMOUNT as f64 * 8.0 / simulated_time.as_secs_f64();

    // TODO: Document 160.0
    assert!(
        160.0 * 1024.0 * 1024.0 < bandwidth,
        "expect transfer on 50ms connection with unlimited bandwidth to eventually surpass 160 Mbit/s but got {} Mbit/s.",
        bandwidth / 1024.0 / 1024.0,

    );
}
