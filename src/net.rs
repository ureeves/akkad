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
//! let origin_addr = "127.0.0.1:13562".parse().unwrap();
//! let socket = UdpSocket::bind(origin_addr).unwrap();
//!
//! let dest_addr: SocketAddr = "127.0.0.2:26531".parse().unwrap();
//! let gateway = RpcGateway::bind(dest_addr).unwrap();
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
//! resp.respond(b"hello").unwrap();
//! let (_, addr) = socket.recv_from(&mut buf).unwrap();
//!
//! assert_eq!(addr, dest_addr);
//! assert_eq!(&buf[..], &res_bytes[..]);
//!
//! gateway.shutdown().unwrap();
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
use std::{
    any::Any,
    cmp,
    collections::HashMap,
    fmt,
    future::Future,
    io,
    net::{SocketAddr, ToSocketAddrs, UdpSocket},
    pin::Pin,
    sync::{
        mpsc::{self, Receiver, Sender},
        Arc, Mutex, RwLock,
    },
    task::{Context, Poll, Waker},
    thread,
    time::{Duration, Instant},
};

/// RPC gateway allowing for asynchronous request-response cycles over UDP.
pub struct RpcGateway {
    handle: thread::JoinHandle<()>,
    shared_state: Arc<ThreadSharedState>,
}

// TODO Investigate the use of lifetimes to limit memory use - e.g. don't
//      return a Message -> return a slice over some memory owned by a
//      UdpGateway - or by the shared state.

impl RpcGateway {
    /// Creates a [`UdpSocket`] from the given address and starts listening
    /// for messages.
    ///
    /// The address type can be any implementor of the [`ToSocketAddrs`] trait.
    /// See its documentation and [`UdpSocket::bind`] for more info.
    pub fn bind<A: ToSocketAddrs>(addr: A) -> Result<Self> {
        let udp = UdpSocket::bind(addr)?;
        // TODO Investigate consequences of second-long timeout
        udp.set_read_timeout(Some(Duration::from_secs(1)))?;

        let (sender, recv) = mpsc::channel();

        let shared_state = Arc::new(ThreadSharedState::new(udp, recv));
        let shared_state_clone = shared_state.clone();

        let handle = thread::spawn(move || {
            let shared_state = shared_state_clone;
            let sender = sender;
            loop_until_shutdown(shared_state, sender);
        });

        Ok(Self {
            handle,
            shared_state,
        })
    }

    /// Sets the timeout for a response to a request.
    ///
    /// A response timeout isn't exact, and one should consider a maximum of
    /// approximately twice the inserted value. As an example, if the timeout
    /// is set to be 5 secs, then a response will timeout before 10 secs.
    pub fn set_response_timeout(&self, timeout: Duration) {
        *self.shared_state.response_timeout.write().unwrap() = timeout;
    }

    /// Returns a future that on which to `await` yielding a request message,
    /// a [`Responder`], and the source address
    ///
    /// These futures are processed in sequence - the first call will be the
    /// first to resolve. See [`Responder`] documentation for details on how to
    /// respond to the request.
    pub fn recv(&self) -> impl Future<Output = Result<(Message, Responder, SocketAddr)>> {
        match &*self.shared_state.error.read().unwrap() {
            Some(err) => {
                return RequestFuture::erroring(err.clone());
            }
            None => {}
        };

        // If there is already a queued message handle it immediately
        if let Ok((msg, resp, addr)) = self.shared_state.receiver.lock().unwrap().try_recv() {
            return RequestFuture::already_concluded(msg, resp, addr);
        }

        // Otherwise push it to the queue
        let rss = RequestSharedState::new();
        self.shared_state
            .awaiting_requests
            .lock()
            .unwrap()
            .push(rss.clone());

        RequestFuture::new(rss)
    }

    /// Sends a request to the given address. Returns a future yielding the
    /// number of bytes written on the socket and a response.
    pub fn send<A: ToSocketAddrs>(
        &self,
        buf: &[u8],
        addr: A,
    ) -> impl Future<Output = Result<(usize, Message)>> {
        match &*self.shared_state.error.read().unwrap() {
            Some(err) => {
                return ResponseFuture::erroring(err.clone());
            }
            None => {}
        };

        // Get socket address from addr
        let mut addrs = match addr.to_socket_addrs() {
            Ok(addrs) => addrs,
            Err(err) => return ResponseFuture::erroring(err.into()),
        };
        let addr = addrs.next();
        if addr.is_none() {
            let err = io::Error::from(io::ErrorKind::InvalidInput);
            return ResponseFuture::erroring(err.into());
        }
        let addr = addr.unwrap();

        let mut awaiting_responses = self.shared_state.awaiting_responses.lock().unwrap();
        let mut cycle_id = self.shared_state.cycle_id.lock().unwrap();

        // make sure the same cycle_id is not already in use
        while awaiting_responses.contains(&(addr, *cycle_id)) {
            cycle_id.increment();
        }

        // new buffer for the request.
        // TODO Combat DoS attacks. Memory grows a lot. Rate limiting? How about DDoS?
        let msg = Message::req(*cycle_id, buf);

        let written = match self.shared_state.socket.send_to(&msg.vec[0..msg.len], addr) {
            Ok(written) => written,
            Err(err) => return ResponseFuture::erroring(err.into()),
        };
        let rss = ResponseSharedState::new(written - 3);

        awaiting_responses.insert((addr, *cycle_id), rss.clone());
        ResponseFuture::new(rss)
    }

    /// Shuts down the gateway and consumes it.
    ///
    /// Pending futures will fail with `Error::Shutdown` and passes an error if
    /// the inner thread paniced.
    ///
    /// See [`thread::JoinHandle::join()`].
    pub fn shutdown(self) -> std::result::Result<(), Box<dyn Any + Send + 'static>> {
        *self.shared_state.shutdown.write().unwrap() = true;
        let res = self.handle.join();

        let mut awaiting_responses = self.shared_state.awaiting_responses.lock().unwrap();
        let mut awaiting_requests = self.shared_state.awaiting_requests.lock().unwrap();

        // end all pending response futures with Error::Shutdown
        for ((_, _), shared_state) in awaiting_responses.drain() {
            let mut state = shared_state.lock().unwrap();
            state.result = Some(Err(Error::Shutdown));

            if let Some(waker) = state.waker.take() {
                waker.wake()
            }
        }

        // end all pending request futures with Error::Shutdown
        for shared_state in awaiting_requests.drain() {
            let mut state = shared_state.lock().unwrap();
            state.result = Some(Err(Error::Shutdown));

            if let Some(waker) = state.waker.take() {
                waker.wake()
            }
        }

        res
    }
}

#[derive(Debug)]
struct ThreadSharedState {
    // Make these all Arc?
    shutdown: RwLock<bool>,
    error: RwLock<Option<Error>>,
    awaiting_responses: Mutex<AwaitingResponseMap>,
    cycle_id: Mutex<CycleId>,
    socket: UdpSocket,
    awaiting_requests: Mutex<AwaitingRequestQueue>,
    receiver: Mutex<Receiver<(Message, Responder, SocketAddr)>>,
    response_timeout: RwLock<Duration>,
}

impl ThreadSharedState {
    fn new(socket: UdpSocket, recv: Receiver<(Message, Responder, SocketAddr)>) -> Self {
        Self {
            shutdown: RwLock::new(false),
            error: RwLock::new(None),
            socket,
            receiver: Mutex::new(recv),
            cycle_id: Mutex::new(CycleId::new()),
            awaiting_responses: Mutex::new(AwaitingResponseMap::new()),
            awaiting_requests: Mutex::new(AwaitingRequestQueue::new()),
            response_timeout: RwLock::new(Duration::from_secs(30)),
        }
    }
}

/// Processes datagrams until the shutdown flag is set to true.
fn loop_until_shutdown(
    state: Arc<ThreadSharedState>,
    sender: Sender<(Message, Responder, SocketAddr)>,
) {
    let mut past = Instant::now();

    loop {
        if *state.shutdown.read().unwrap() {
            *state.error.write().unwrap() = Some(Error::Shutdown);
            break;
        }

        // Every `response_timeout` see if some responses are taking more
        // than `response_timeout` secs, and eject them from the map, setting Error::Timeout.
        let response_timeout = *state.response_timeout.read().unwrap();
        if past.elapsed() > response_timeout {
            let mut rss_vec = Vec::new();
            let mut awaiting_responses = state.awaiting_responses.lock().unwrap();

            for (key, rss) in awaiting_responses.iter() {
                let rss_guard = rss.lock().unwrap();
                if rss_guard.created.elapsed() > response_timeout {
                    rss_vec.push((*key, rss.clone()))
                }
            }

            for (key, rss) in rss_vec {
                awaiting_responses.pop(&key);

                let mut rss = rss.lock().unwrap();
                rss.result = Some(Err(Error::Timeout));
                if let Some(waker) = rss.waker.take() {
                    waker.wake();
                }
            }

            past = Instant::now();
        }

        let mut msg = Message::empty();
        match state.socket.recv_from(&mut msg.vec[..]) {
            Ok((len, addr)) => {
                // Process the message elsewhere
                msg.len = len;
                process_buffer(state.clone(), sender.clone(), msg, addr);
            }
            Err(err) => {
                // Timeouts are a good thing, since they allow stopping
                // without first receiving a datagram.
                let err_kind = err.kind();
                match err_kind {
                    io::ErrorKind::WouldBlock => {}
                    io::ErrorKind::TimedOut => {}
                    _ => {
                        *state.error.write().unwrap() = Some(err.into());
                        break;
                    }
                }
            }
        }
    }
}

/// Processes the incoming message.
fn process_buffer(
    state: Arc<ThreadSharedState>,
    sender: Sender<(Message, Responder, SocketAddr)>,
    msg: Message,
    addr: SocketAddr,
) {
    // drop malformed datagram
    if msg.len < 4 {
        return;
    }
    match msg.vec[0] {
        0x00 => {
            let mut awaiting_requests = state.awaiting_requests.lock().unwrap();
            let resp = Responder::new(
                addr,
                CycleId::from_bytes([msg.vec[1], msg.vec[2]]),
                state.clone(),
            );
            // if there is a waiting request just set and wake (if has been polled)
            // else just pump it through to the sender.
            if let Some(rss) = awaiting_requests.pop() {
                let mut rss = rss.lock().unwrap();
                rss.result = Some(Ok((msg, resp, addr)));
                if let Some(waker) = rss.waker.take() {
                    waker.wake();
                }
            } else {
                let _ = sender.send((msg, resp, addr));
            }
        }
        0x01 => {
            let mut awaiting_responses = state.awaiting_responses.lock().unwrap();
            let cycle_id = CycleId::from_bytes([msg.vec[1], msg.vec[2]]);

            // If there is a pending request set the response and wake,
            // otherwise drop message.
            if let Some(rss) = awaiting_responses.pop(&(addr, cycle_id)) {
                let mut rss = rss.lock().unwrap();

                rss.result = Some(Ok(msg));
                if let Some(waker) = rss.waker.take() {
                    waker.wake();
                }
            }
        }
        _ => {
            // drop malformed datagram
        }
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

impl PartialEq for Error {
    /// Is true if they're both shutdown or timeout errors, or if the
    /// [`io::Error`] has the same [`io::ErrorKind`].
    fn eq(&self, rhs: &Self) -> bool {
        match self {
            Error::Io(err) => {
                if let Error::Io(rhs_err) = rhs {
                    return err.kind() == rhs_err.kind();
                }
                false
            }
            Error::Shutdown => {
                if let Error::Shutdown = rhs {
                    return true;
                }
                false
            }
            Error::Timeout => {
                if let Error::Timeout = rhs {
                    return true;
                }
                false
            }
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Error::Io(err) => write!(f, "RpcGateway: {}", err),
            Error::Shutdown => write!(f, "RpcGateway: Shutdown"),
            Error::Timeout => write!(f, "RpcGateway: Timeout"),
        }
    }
}

impl std::error::Error for Error {}

impl Clone for Error {
    fn clone(&self) -> Self {
        match self {
            Self::Io(err) => Self::Io(io::Error::from(err.kind())),
            Self::Shutdown => Self::Shutdown,
            Self::Timeout => Self::Timeout,
        }
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
    }
}

/// DRY keeping
type Result<T> = std::result::Result<T, Error>;

/// Future yielding a message and a responder when
struct RequestFuture {
    shared_state: Arc<Mutex<RequestSharedState>>,
}

impl Future for RequestFuture {
    type Output = Result<(Message, Responder, SocketAddr)>;
    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut state = self.shared_state.lock().unwrap();

        match state.result.take() {
            Some(res) => Poll::Ready(res),
            None => {
                state.waker = Some(ctx.waker().clone());
                Poll::Pending
            }
        }
    }
}

impl RequestFuture {
    fn new(rss: Arc<Mutex<RequestSharedState>>) -> Self {
        Self { shared_state: rss }
    }

    fn already_concluded(msg: Message, resp: Responder, addr: SocketAddr) -> Self {
        Self {
            shared_state: RequestSharedState::already_concluded(msg, resp, addr),
        }
    }

    fn erroring(err: Error) -> Self {
        Self {
            shared_state: RequestSharedState::erroring(err),
        }
    }
}

#[derive(Debug)]
struct RequestSharedState {
    result: Option<Result<(Message, Responder, SocketAddr)>>,
    waker: Option<Waker>,
}

impl RequestSharedState {
    /// New empty shared state.
    fn new() -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self {
            result: None,
            waker: None,
        }))
    }

    /// New shared state that will immediately resolve when polled
    fn already_concluded(msg: Message, resp: Responder, addr: SocketAddr) -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self {
            result: Some(Ok((msg, resp, addr))),
            waker: None,
        }))
    }

    /// New erroring shared state
    fn erroring(err: Error) -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self {
            result: Some(Err(err)),
            waker: None,
        }))
    }
}

/// Allows responding to incoming requests.
#[derive(Debug)]
pub struct Responder {
    addr: SocketAddr,
    cycle_id: CycleId,
    shared_state: Arc<ThreadSharedState>,
}

impl Responder {
    fn new(addr: SocketAddr, cycle_id: CycleId, shared_state: Arc<ThreadSharedState>) -> Self {
        Self {
            addr,
            cycle_id,
            shared_state,
        }
    }

    /// Responds to a received request returning the amount of written from the
    /// buffer to the underlying socket.
    pub fn respond(self, buf: &[u8]) -> Result<usize> {
        let state = self.shared_state.clone();

        let msg = Message::res(self.cycle_id, buf);
        match state.socket.send_to(&msg.vec[0..msg.len], self.addr) {
            Ok(written) => Ok(written - 3),
            Err(err) => Err(err.into()),
        }
    }
}

/// Future yielding with bytes written to the socket and a Message.
struct ResponseFuture {
    shared_state: Arc<Mutex<ResponseSharedState>>,
}

impl ResponseFuture {
    fn new(rss: Arc<Mutex<ResponseSharedState>>) -> Self {
        Self { shared_state: rss }
    }

    fn erroring(err: Error) -> Self {
        Self {
            shared_state: ResponseSharedState::erroring(err),
        }
    }
}

impl Future for ResponseFuture {
    type Output = Result<(usize, Message)>;

    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut state = self.shared_state.lock().unwrap();

        match state.result.take() {
            Some(res) => Poll::Ready(res.map(|msg| (state.bytes_consumed, msg))),
            None => {
                state.waker = Some(ctx.waker().clone());
                Poll::Pending
            }
        }
    }
}

/// The state shared between the running thread and a single request-response
/// cycle.
#[derive(Debug)]
struct ResponseSharedState {
    bytes_consumed: usize,
    result: Option<Result<Message>>,
    waker: Option<Waker>,
    created: Instant,
}

impl ResponseSharedState {
    /// New response state with `bytes_consumed` from the buffer.
    fn new(bytes_consumed: usize) -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self {
            bytes_consumed,
            result: None,
            waker: None,
            created: Instant::now(),
        }))
    }

    /// An erroring state. The future will return an error on poll().
    fn erroring(err: Error) -> Arc<Mutex<Self>> {
        Arc::new(Mutex::new(Self {
            bytes_consumed: 0,
            result: Some(Err(err)),
            waker: None,
            created: Instant::now(),
        }))
    }
}

const MAX_DATAGRAM_LEN: usize = 65536;

/// Network message to be processed by a [`RpcGateway`].
///
/// These messages have a maximum size of 65533 bytes due to protocol overhead.
#[derive(Debug)]
pub struct Message {
    vec: Vec<u8>,
    len: usize,
}

impl Message {
    fn empty() -> Self {
        Self {
            vec: vec![0; MAX_DATAGRAM_LEN],
            len: 0,
        }
    }

    /// Returns a request with a cycle id and a buffer.
    fn req(cycle_id: CycleId, buf: &[u8]) -> Self {
        let mut this = Self::empty();

        this.vec[0] = 0x00;
        this.vec[1..3].copy_from_slice(&cycle_id.into_bytes());

        let to_copy = cmp::min(MAX_DATAGRAM_LEN - 3, buf.len());
        this.vec[3..to_copy + 3].copy_from_slice(&buf[0..to_copy]);
        this.len = to_copy + 3;

        this
    }

    /// Returns a response with a cycle id and a buffer.
    fn res(cycle_id: CycleId, buf: &[u8]) -> Self {
        let mut this = Self::empty();

        this.vec[0] = 0x01;
        this.vec[1..3].copy_from_slice(&cycle_id.into_bytes());

        let to_copy = cmp::min(MAX_DATAGRAM_LEN - 3, buf.len());
        this.vec[3..to_copy + 3].copy_from_slice(&buf[0..to_copy]);
        this.len = to_copy + 3;

        this
    }
}

impl AsRef<[u8]> for Message {
    /// Returns a slice through the contents of a message.
    fn as_ref(&self) -> &[u8] {
        &self.vec[3..self.len]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CycleId(u16);

impl CycleId {
    fn new() -> Self {
        Self(0)
    }

    fn increment(&mut self) {
        self.0 += self.0.wrapping_add(1);
    }

    fn from_bytes(bytes: [u8; 2]) -> Self {
        Self(u16::from_be_bytes(bytes))
    }

    fn into_bytes(self) -> [u8; 2] {
        u16::to_be_bytes(self.0)
    }
}

/// Maps incoming SocketAddr and cycle Ids to some shared state with the
/// ResponseFuture.
///
/// This allows us to map pending request-response cycles to a way to notify
/// the executor that a response is ready for consumption.
#[derive(Debug)]
struct AwaitingResponseMap(HashMap<(SocketAddr, CycleId), Arc<Mutex<ResponseSharedState>>>);

impl AwaitingResponseMap {
    /// Returns a new empty map.
    fn new() -> Self {
        Self(HashMap::new())
    }

    /// Inserts the state into the map using the (addr, cycle_id) tuple as a
    /// key. Should never be called when there is already an item in the same
    /// key. Make sure to check with [`contains`].
    fn insert(&mut self, key: (SocketAddr, CycleId), state: Arc<Mutex<ResponseSharedState>>) {
        self.0.insert(key, state);
    }

    /// Returns true if the (addr, cycle_id) tuple is a key in the map.
    fn contains(&self, key: &(SocketAddr, CycleId)) -> bool {
        self.0.contains_key(key)
    }

    /// Pops a value from the map if it exists.
    fn pop(&mut self, key: &(SocketAddr, CycleId)) -> Option<Arc<Mutex<ResponseSharedState>>> {
        self.0.remove(key)
    }

    /// Iterates through all values of the map
    fn iter(
        &self,
    ) -> impl Iterator<Item = (&(SocketAddr, CycleId), &Arc<Mutex<ResponseSharedState>>)> + '_ {
        self.0.iter()
    }

    /// Empties the map and returns all the values as an iterator.
    fn drain(
        &mut self,
    ) -> impl Iterator<Item = ((SocketAddr, CycleId), Arc<Mutex<ResponseSharedState>>)> + '_ {
        self.0.drain()
    }
}

/// FIFO queue allowing us to enqueue waiting request futures.
#[derive(Debug)]
struct AwaitingRequestQueue(Vec<Arc<Mutex<RequestSharedState>>>);

impl AwaitingRequestQueue {
    /// New empty queue
    fn new() -> Self {
        Self(Vec::new())
    }

    /// Pushes an element to the beginning of the queue.
    fn push(&mut self, elem: Arc<Mutex<RequestSharedState>>) {
        self.0.insert(0, elem)
    }

    /// Pops an element from the end of the queue.
    fn pop(&mut self) -> Option<Arc<Mutex<RequestSharedState>>> {
        self.0.pop()
    }

    /// Empties the queue returning an iterator over the element
    fn drain(&mut self) -> impl Iterator<Item = Arc<Mutex<RequestSharedState>>> + '_ {
        self.0.drain(..).rev()
    }
}

#[test]
fn clean_shutdown() {
    use futures::executor::block_on;

    let gateway = RpcGateway::bind("127.0.0.1:12345").expect("couldn't bind to address");

    let res_fut = gateway.send(b"hello", "127.0.0.2:12345");
    let req_fut = gateway.recv();

    gateway.shutdown().expect("not a clean shutdown");

    let res_err = block_on(res_fut).expect_err("not an error");
    let req_err = block_on(req_fut).expect_err("not an error");

    assert_eq!(res_err, Error::Shutdown);
    assert_eq!(req_err, Error::Shutdown);
}

#[test]
fn response_timeout() {
    use futures::executor::block_on;

    let gateway = RpcGateway::bind("127.0.0.1:12346").expect("couldn't bind to address");
    gateway.set_response_timeout(Duration::from_secs(1));

    // send back to ourselves
    let res_fut = gateway.send(b"lost to the ether", "127.0.0.1:12346");
    let err = block_on(res_fut).expect_err("not an error");

    assert_eq!(err, Error::Timeout);
    gateway.shutdown().unwrap();
}

#[test]
fn multiple_echoes() {
    use futures::executor::block_on;

    // startup two gateways
    let origin_addr = "127.0.0.1:13562".parse().unwrap();
    let gateway_origin = RpcGateway::bind(origin_addr).expect("couldn't bind to address");

    let dest_addr: SocketAddr = "127.0.0.2:26531".parse().unwrap();
    let gateway_dest = RpcGateway::bind(dest_addr).expect("couldn't bind to address");

    let res1_fut = gateway_origin.send(b"hello1", dest_addr);
    let res2_fut = gateway_origin.send(b"hello2", dest_addr);
    let res3_fut = gateway_origin.send(b"hello3", dest_addr);

    let req1_fut = gateway_dest.recv();
    let req2_fut = gateway_dest.recv();
    let req3_fut = gateway_dest.recv();

    let (msg1, resp1, addr1) = block_on(req1_fut).unwrap();
    let (msg2, resp2, addr2) = block_on(req2_fut).unwrap();
    let (msg3, resp3, addr3) = block_on(req3_fut).unwrap();

    assert_eq!(addr1, origin_addr);
    assert_eq!(addr2, origin_addr);
    assert_eq!(addr3, origin_addr);

    resp1.respond(msg1.as_ref()).expect("couldn't echo");
    resp2.respond(msg2.as_ref()).expect("couldn't echo");
    resp3.respond(msg3.as_ref()).expect("couldn't echo");

    let (written1, msg1) = block_on(res1_fut).unwrap();
    let (written2, msg2) = block_on(res2_fut).unwrap();
    let (written3, msg3) = block_on(res3_fut).unwrap();

    assert_eq!(msg1.as_ref(), b"hello1");
    assert_eq!(msg2.as_ref(), b"hello2");
    assert_eq!(msg3.as_ref(), b"hello3");

    assert_eq!(written1, b"hello1".len());
    assert_eq!(written2, b"hello2".len());
    assert_eq!(written3, b"hello3".len());

    gateway_origin.shutdown().expect("error on shutdown");
    gateway_dest.shutdown().expect("error on shutdown");
}
