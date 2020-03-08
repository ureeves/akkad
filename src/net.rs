//! Implementation of an asynchronous RPC gateway over UDP. Allows for
//! receiving and responding to incoming requests, as well as sending requests
//! and awaiting a response.
//!
//! # Example
//!
//! ```
//! use akkad::net::RpcGateway;
//! use std::net::{UdpSocket, SocketAddr};
//! use futures::executor::block_on;
//!
//! let req_bytes: [u8; 8] = [0, 0, 0, 104, 101, 108, 108, 111];
//! let res_bytes: [u8; 8] = [1, 0, 0, 104, 101, 108, 108, 111];
//!
//! // startup two gateways
//! let origin_addr = "127.0.0.1:25555".parse().unwrap();
//! let socket = UdpSocket::bind(origin_addr).unwrap();
//!
//! let dest_addr: SocketAddr = "127.0.0.1:25556".parse().unwrap();
//! let gateway = block_on(RpcGateway::bind(dest_addr)).unwrap();
//!
//! // send and receive a message
//! let request_fut = gateway.recv();
//! socket.send_to(&req_bytes[..], dest_addr).unwrap();
//!
//! // block on receiving a request
//! let (msg, resp, addr) = block_on(request_fut).unwrap();
//!
//! assert_eq!(msg.as_ref(), &res_bytes[3..]);
//! assert_eq!(addr, origin_addr);
//!
//! // respond and block on being responded to
//! let mut buf = [0u8; 8];
//! block_on(resp.respond(b"hello")).unwrap();
//! let (_, addr) = socket.recv_from(&mut buf).unwrap();
//!
//! assert_eq!(addr, dest_addr);
//! assert_eq!(&buf[..], &res_bytes[..]);
//!
//! block_on(gateway.shutdown()).unwrap();
//! ```
//!
//! # Design
//! To distinguish requests and responses, and specific request-response
//! cycles, a protocol is implemented that adds a header on top of a UDP
//! datagram. The header looks like this:
//!
//! ```Text
//!  0                   1                   2
//!  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |      Flags      |           Cycle Id            |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! ```
//!
//! `Flags` is used to distinguish requests from responses, and the remaining
//! bits are reserved for future use.
//!
//! `Cycle Id` is used to give a unique identifier to a request-response cycle.
//! This allows us to await a response and issue multiple requests to the same
//! host and awaiting on all the respective responses.
//!
//! This header is completely opaque to a user.
//!
//! The gateway will - internally - continuously processes arriving messages,
//! and forwards them sequencially to the returned [`Future`]s.
use async_std::{
    io,
    net::{SocketAddr, ToSocketAddrs, UdpSocket},
    prelude::*,
    sync::{Arc, Mutex},
    task,
};
use futures::{
    channel::{mpsc, oneshot},
    select,
    sink::SinkExt,
    FutureExt,
};
use std::{cmp, collections::HashMap};

/// RPC gateway allowing for asynchronous request-response cycles over UDP.
pub struct RpcGateway {
    state: Arc<Mutex<SharedState>>,
}

struct SharedState {
    loop_handle: task::JoinHandle<Result<()>>,
    send_sender: Option<Sender<SendArgs>>,
    recv_sender: Option<Sender<RecvArgs>>,
    shutdown_sender: Option<Sender<()>>,
}

impl SharedState {
    fn new(
        loop_handle: task::JoinHandle<Result<()>>,
        send_sender: Sender<SendArgs>,
        recv_sender: Sender<RecvArgs>,
        shutdown_sender: Sender<()>,
    ) -> Self {
        Self {
            loop_handle,
            send_sender: Some(send_sender),
            recv_sender: Some(recv_sender),
            shutdown_sender: Some(shutdown_sender),
        }
    }
}

type SendArgs = (Message, SocketAddr, OneshotSender<Result<(usize, Message)>>);
type RecvArgs = OneshotSender<Result<(Message, Responder, SocketAddr)>>;

impl RpcGateway {
    /// Creates a [`UdpSocket`] from the given address and starts listening
    /// for messages.
    ///
    /// The address type can be any implementor of the [`ToSocketAddrs`] trait.
    /// See its documentation and [`UdpSocket::bind`] for more info.
    pub async fn bind<A: ToSocketAddrs>(addr: A) -> Result<RpcGateway> {
        let socket = Arc::new(UdpSocket::bind(addr).await?);

        let (send_sender, send_receiver) = mpsc::unbounded();
        let (recv_sender, recv_receiver) = mpsc::unbounded();
        let (shutdown_sender, shutdown_receiver) = mpsc::unbounded();

        let loop_handle = task::spawn(gateway_loop(
            socket,
            send_receiver,
            recv_receiver,
            shutdown_receiver,
        ));

        Ok(RpcGateway {
            state: Arc::new(Mutex::new(SharedState::new(
                loop_handle,
                send_sender,
                recv_sender,
                shutdown_sender,
            ))),
        })
    }

    /// Returns a future that on which to `await` yielding a request message,
    /// a [`Responder`], and the source address
    ///
    /// These futures are processed in sequence - the first call will be the
    /// first to resolve. See [`Responder`] documentation for details on how to
    /// respond to the request.
    pub async fn recv(&self) -> Result<(Message, Responder, SocketAddr)> {
        let (sender, receiver) = oneshot::channel();
        match &mut self.state.lock().await.recv_sender {
            Some(recv_sender) => recv_sender.send(sender).await?,
            None => return Err(Error::Shutdown),
        }

        receiver.await?
    }

    /// Sends a request to the given address. Returns a future yielding the
    /// number of bytes written on the socket and a response.
    pub async fn send<A: ToSocketAddrs>(&self, buf: &[u8], addr: A) -> Result<(usize, Message)> {
        // get socket address from addr
        let mut addrs = addr.to_socket_addrs().await?;
        let addr = addrs.next();

        if addr.is_none() {
            let err = io::Error::from(io::ErrorKind::InvalidInput);
            return Err(err.into());
        }

        let addr = addr.unwrap();
        let msg = Message::req(0, buf);

        let (sender, receiver) = oneshot::channel();
        match &mut self.state.lock().await.send_sender {
            Some(send_sender) => send_sender.send((msg, addr, sender)).await?,
            None => return Err(Error::Shutdown),
        }

        receiver.await?
    }

    // TODO Reintroduce timeouts on requests, or should the user just drop?
    //      How about sweeping kept memory?

    /// Shuts down the gateway and consumes it.
    ///
    /// Pending futures will fail with `Error::Shutdown` and passes an error if
    /// the inner thread paniced.
    pub async fn shutdown(&self) -> Result<()> {
        let mut state = self.state.lock().await;

        if let Some(shutdown_sender) = state.shutdown_sender.take() {
            drop(shutdown_sender);
        }
        if let Some(send_sender) = state.send_sender.take() {
            drop(send_sender);
        }
        if let Some(recv_sender) = state.recv_sender.take() {
            drop(recv_sender);
        }

        (&mut state.loop_handle).await
    }
}

async fn gateway_loop(
    socket: Arc<UdpSocket>,
    send_call_receiver: Receiver<SendArgs>,
    recv_call_receiver: Receiver<RecvArgs>,
    shutdown: Receiver<()>,
) -> Result<()> {
    let (send_sender, send_receiver) = mpsc::unbounded();
    let (recv_sender, recv_receiver) = mpsc::unbounded();
    let (mut broker_sender, broker_receiver) = mpsc::unbounded();

    let send_handle = task::spawn(send_loop(socket.clone(), send_call_receiver, send_receiver));
    let recv_handle = task::spawn(recv_loop(recv_call_receiver, recv_receiver));
    let broker_handle = task::spawn(message_broker_loop(
        socket.clone(),
        broker_receiver,
        send_sender,
        recv_sender,
    ));

    let mut response = Ok(());

    // select loop through shutdown and socket
    let mut shutdown = shutdown.fuse();
    loop {
        let mut msg = Message::zeroed();

        select! {
            res = socket.recv_from(&mut msg.vec).fuse() => match res {
                Ok((len, addr)) => {
                    msg.len = len;
                    broker_sender.send((msg, addr)).await.unwrap();
                },
                Err(err) => match err.kind() {
                    io::ErrorKind::WouldBlock => {}
                    io::ErrorKind::TimedOut => {}
                    _ => {
                        response = Err(err.into());
                        break;
                    }
                },
            },
            void = shutdown.next().fuse() => match void {
                Some(_) => {},
                None => break,
            }
        }
    }

    drop(broker_sender);

    broker_handle.await?;
    send_handle.await?;
    recv_handle.await?;

    response
}

async fn message_broker_loop(
    socket: Arc<UdpSocket>,
    broker_receiver: Receiver<(Message, SocketAddr)>,
    mut send_sender: Sender<(Message, SocketAddr)>,
    mut recv_sender: Sender<(Message, Responder, SocketAddr)>,
) -> Result<()> {
    let mut broker_receiver = broker_receiver.fuse();
    loop {
        select! {
            received = broker_receiver.next().fuse() => match received {
                Some(received) => {
                    // drop malformed packet
                    if received.0.len < 4 {
                        continue;
                    }

                    // send to the appropriate receiver
                    match received.0.msb() {
                        true => {
                            send_sender.send(received).await.unwrap()
                        },
                        false => {
                            let cycle_id = received.0.cycle_id();
                            let resp = Responder::new(socket.clone(), received.1, cycle_id);
                            let received = (received.0, resp, received.1);
                            recv_sender.send(received).await.unwrap()
                        },
                    }
                },
                None => break,
            }
        }
    }

    Ok(())
}

async fn recv_loop(
    call_receiver: Receiver<RecvArgs>,
    recv_receiver: Receiver<(Message, Responder, SocketAddr)>,
) -> Result<()> {
    let mut call_receiver = call_receiver.fuse();
    let mut recv_receiver = recv_receiver.fuse();

    let mut pending_messages = Vec::new();
    let mut pending_receivers = Vec::new();

    loop {
        select! {
            call = call_receiver.next().fuse() => match call {
                Some(call) => {
                    if !pending_messages.is_empty() {
                        call.send(Ok(pending_messages.remove(0))).ok();
                        continue;
                    }
                    pending_receivers.push(call);
                },
                None => break,
            },
            recv = recv_receiver.next().fuse() => match recv {
                Some(recv) => {
                    if !pending_receivers.is_empty() {
                        pending_receivers.remove(0).send(Ok(recv)).ok();
                        continue;
                    }
                    pending_messages.push(recv);
                },
                None => break,
            },
        }
    }

    for receiver in pending_receivers.drain(..) {
        receiver.send(Err(Error::Shutdown)).ok();
    }

    Ok(())
}

async fn send_loop(
    socket: Arc<UdpSocket>,
    call_receiver: Receiver<SendArgs>,
    send_receiver: Receiver<(Message, SocketAddr)>,
) -> Result<()> {
    let mut call_receiver = call_receiver.fuse();
    let mut send_receiver = send_receiver.fuse();

    let mut sender_map = HashMap::new();
    let mut cycle_id = 0u16;

    loop {
        select! {
            call = call_receiver.next().fuse() => match call {
                Some(call) => {
                    let (mut msg, addr, sender) = call;

                    if sender_map.contains_key(&(addr, cycle_id)) {
                        cycle_id += 1;
                    }
                    msg.vec[0] = 0; // set as a message
                    let cycle_id_bytes = u16::to_be_bytes(cycle_id);
                    msg.vec[1] = cycle_id_bytes[0]; // set cycle id bytes
                    msg.vec[2] = cycle_id_bytes[1];
                    let written = match socket.send_to(&msg.vec[0..msg.len], addr).await {
                        Ok(written) => written,
                        Err(err) => {
                            sender.send(Err(err.into())).ok();
                            continue;
                        }
                    };
                    sender_map.insert((addr, cycle_id), (written, sender));
                },
                None => break,
            },
            send = send_receiver.next().fuse() => match send {
                Some(send) => {
                    let (msg, addr) = send;
                    let cycle_id = u16::from_be_bytes([msg.vec[1], msg.vec[2]]);
                    if let Some((written, sender)) = sender_map.remove(&(addr, cycle_id)) {
                        sender.send(Ok((written - 3, msg))).ok();
                    }
                },
                None => break,
            },
        }
    }

    for (_, (_, sender)) in sender_map.drain() {
        sender.send(Err(Error::Shutdown)).ok();
    }

    Ok(())
}

type Result<T> = std::result::Result<T, Error>;

type Sender<T> = mpsc::UnboundedSender<T>;
type Receiver<T> = mpsc::UnboundedReceiver<T>;

type OneshotSender<T> = oneshot::Sender<T>;

/// Allows responding to incoming requests.
pub struct Responder {
    socket: Arc<UdpSocket>,
    addr: SocketAddr,
    cycle_id: u16,
}

impl Responder {
    fn new(socket: Arc<UdpSocket>, addr: SocketAddr, cycle_id: u16) -> Self {
        Self {
            socket,
            addr,
            cycle_id,
        }
    }

    /// Responds to a received request returning the amount of written from the
    /// buffer to the underlying socket.
    pub async fn respond(self, buf: &[u8]) -> Result<usize> {
        let msg = Message::res(self.cycle_id, buf);
        match self.socket.send_to(&msg.vec[0..msg.len], self.addr).await {
            Ok(written) => Ok(written - 3),
            Err(err) => Err(err.into()),
        }
    }
}

const MAX_DATAGRAM_LEN: usize = 65536;

/// Network message to be processed by a [`RpcGateway`].
///
/// These messages have a maximum size of 65533 bytes due to protocol overhead.
pub struct Message {
    vec: Vec<u8>,
    len: usize,
}

impl Message {
    const MSB: u8 = 0x80;

    /// True if the most significant bit is set.
    fn msb(&self) -> bool {
        self.vec[0] & Self::MSB != 0
    }

    fn cycle_id(&self) -> u16 {
        u16::from_be_bytes([self.vec[1], self.vec[2]])
    }

    fn zeroed() -> Self {
        Self {
            vec: vec![0; MAX_DATAGRAM_LEN],
            len: 0,
        }
    }

    /// Returns a request with a cycle id and a buffer.
    fn req(cycle_id: u16, buf: &[u8]) -> Self {
        let mut msg = Self::zeroed();

        msg.vec[0] = 0x00;
        msg.vec[1..3].copy_from_slice(&u16::to_be_bytes(cycle_id));

        let to_copy = cmp::min(MAX_DATAGRAM_LEN - 3, buf.len());
        msg.vec[3..to_copy + 3].copy_from_slice(&buf[0..to_copy]);
        msg.len = to_copy + 3;

        msg
    }

    /// Returns a response with a cycle id and a buffer.
    fn res(cycle_id: u16, buf: &[u8]) -> Self {
        let mut msg = Self::zeroed();

        msg.vec[0] = 0x01;
        msg.vec[1..3].copy_from_slice(&u16::to_be_bytes(cycle_id));

        let to_copy = cmp::min(MAX_DATAGRAM_LEN - 3, buf.len());
        msg.vec[3..to_copy + 3].copy_from_slice(&buf[0..to_copy]);
        msg.len = to_copy + 3;

        msg
    }
}

impl AsRef<[u8]> for Message {
    /// Returns a slice through the contents of a message.
    fn as_ref(&self) -> &[u8] {
        &self.vec[3..self.len]
    }
}

/// Error type returned by the [`RpcGateway`] and associated types.
#[derive(Debug)]
pub enum Error {
    /// Errors related to UDP
    Io(io::Error),

    /// When something could be completed due to shutdown.
    Shutdown,

    /// Timed out waiting for a response to a request.
    Timeout,
}

impl From<io::Error> for Error {
    fn from(io_err: io::Error) -> Self {
        Error::Io(io_err)
    }
}

impl From<mpsc::SendError> for Error {
    fn from(_mpsc_err: mpsc::SendError) -> Self {
        Self::Shutdown
    }
}

impl From<oneshot::Canceled> for Error {
    fn from(_cancelled: oneshot::Canceled) -> Self {
        Self::Shutdown
    }
}

#[test]
fn clean_shutdown() {
    use futures::executor::block_on;

    let gateway = block_on(RpcGateway::bind("127.0.0.1:25557")).expect("couldn't bind to address");

    let res_fut = gateway.send(b"hello", "127.0.0.1:25557");
    let req_fut = gateway.recv();

    block_on(gateway.shutdown()).expect("not a clean shutdown");

    match block_on(res_fut) {
        Ok(_) => panic!("not an error"),
        Err(res_err) => match res_err {
            Error::Shutdown => {}
            _ => panic!("not Error::Shutdown"),
        },
    }
    match block_on(req_fut) {
        Ok(_) => panic!("not an error"),
        Err(req_err) => match req_err {
            Error::Shutdown => {}
            _ => panic!("not Error::Shutdown"),
        },
    }
}

#[test]
fn multiple_receptions() {
    use futures::executor::block_on;
    use std::net::UdpSocket;

    let hello = [
        0,
        0,
        0,
        0b0110_1000,
        0b0110_0101,
        0b0110_1100,
        0b0110_1100,
        0b0110_1111,
    ];

    let dest_addr: SocketAddr = "127.0.0.1:25558".parse().unwrap();
    let gateway = block_on(RpcGateway::bind(dest_addr)).expect("couldn't bind to address");

    let origin_addr: SocketAddr = "127.0.0.1:25559".parse().unwrap();
    let udp_socket = UdpSocket::bind(origin_addr).expect("couldn't bind to address");

    udp_socket
        .send_to(&hello[..], dest_addr)
        .expect("couldn't send message");
    udp_socket
        .send_to(&hello[..], dest_addr)
        .expect("couldn't send message");
    udp_socket
        .send_to(&hello[..], dest_addr)
        .expect("couldn't send message");

    let req1_fut = gateway.recv();
    let req2_fut = gateway.recv();
    let req3_fut = gateway.recv();

    let (msg1, resp1, addr1) = block_on(req1_fut).unwrap();
    let (msg2, resp2, addr2) = block_on(req2_fut).unwrap();
    let (msg3, resp3, addr3) = block_on(req3_fut).unwrap();

    assert_eq!(addr1, origin_addr);
    assert_eq!(addr2, origin_addr);
    assert_eq!(addr3, origin_addr);

    match block_on(resp1.respond(msg1.as_ref())) {
        Ok(_) => {}
        _ => panic!("couldn't echo"),
    }
    match block_on(resp2.respond(msg2.as_ref())) {
        Ok(_) => {}
        _ => panic!("couldn't echo"),
    }
    match block_on(resp3.respond(msg3.as_ref())) {
        Ok(_) => {}
        _ => panic!("couldn't echo"),
    }

    let mut buf1 = [0u8; 8];
    let (bytes_read1, addr1) = udp_socket.recv_from(&mut buf1).expect("failed receiving");
    let mut buf2 = [0u8; 8];
    let (bytes_read2, addr2) = udp_socket.recv_from(&mut buf2).expect("failed receiving");
    let mut buf3 = [0u8; 8];
    let (bytes_read3, addr3) = udp_socket.recv_from(&mut buf3).expect("failed receiving");

    assert_eq!(addr1, dest_addr);
    assert_eq!(addr2, dest_addr);
    assert_eq!(addr3, dest_addr);

    assert_eq!(msg1.as_ref(), b"hello");
    assert_eq!(msg2.as_ref(), b"hello");
    assert_eq!(msg3.as_ref(), b"hello");

    assert_eq!(bytes_read1, hello.len());
    assert_eq!(bytes_read2, hello.len());
    assert_eq!(bytes_read3, hello.len());

    block_on(gateway.shutdown()).expect("error on shutdown");
}

#[test]
fn multiple_sends() {
    use futures::executor::block_on;
    use std::net::UdpSocket;
    use std::thread;

    let origin_addr: SocketAddr = "127.0.0.1:25560".parse().unwrap();
    let gateway = block_on(RpcGateway::bind(origin_addr)).expect("couldn't bind to address");

    let dest_addr: SocketAddr = "127.0.0.1:25561".parse().unwrap();
    let udp_socket = Arc::new(UdpSocket::bind(dest_addr).expect("couldn't bind to address"));

    let clone_udpsocket = udp_socket.clone();
    let thread1 = thread::spawn(move || {
        let mut buf = [0u8; 8];
        let (bytes_read, addr) = clone_udpsocket
            .recv_from(&mut buf)
            .expect("failed receiving");

        assert_eq!(bytes_read, buf.len());
        assert_eq!(addr, origin_addr);

        buf[0] = 0x80;
        clone_udpsocket
            .send_to(&buf, origin_addr)
            .expect("failed sending response");
    });

    let clone_udpsocket = udp_socket.clone();
    let thread2 = thread::spawn(move || {
        let mut buf = [0u8; 8];
        let (bytes_read, addr) = clone_udpsocket
            .recv_from(&mut buf)
            .expect("failed receiving");

        assert_eq!(bytes_read, buf.len());
        assert_eq!(addr, origin_addr);

        buf[0] = 0x80;
        clone_udpsocket
            .send_to(&buf, origin_addr)
            .expect("failed sending response");
    });

    let clone_udpsocket = udp_socket;
    let thread3 = thread::spawn(move || {
        let mut buf = [0u8; 8];
        let (bytes_read, addr) = clone_udpsocket
            .recv_from(&mut buf)
            .expect("failed receiving");

        assert_eq!(bytes_read, buf.len());
        assert_eq!(addr, origin_addr);

        buf[0] = 0x80;
        clone_udpsocket
            .send_to(&buf, origin_addr)
            .expect("failed sending response");
    });

    let (bytes_written1, msg1) =
        block_on(gateway.send(b"hello", dest_addr)).expect("failed send()");
    let (bytes_written2, msg2) =
        block_on(gateway.send(b"hello", dest_addr)).expect("failed send()");
    let (bytes_written3, msg3) =
        block_on(gateway.send(b"hello", dest_addr)).expect("failed send()");

    assert_eq!(bytes_written1, b"hello".len());
    assert_eq!(bytes_written2, b"hello".len());
    assert_eq!(bytes_written3, b"hello".len());

    assert_eq!(msg1.as_ref(), b"hello");
    assert_eq!(msg2.as_ref(), b"hello");
    assert_eq!(msg3.as_ref(), b"hello");

    thread1.join().expect("thread panic");
    thread2.join().expect("thread panic");
    thread3.join().expect("thread panic");
    block_on(gateway.shutdown()).expect("error on shutdown");
}
