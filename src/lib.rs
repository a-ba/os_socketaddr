//! This crate provides a type that can act as a platform-native socket address
//! (i.e. [libc::sockaddr])
//!
//! # Motivation
//!
//! The std crate provides [SocketAddr] for managing socket addresses. However there is no easy way
//! to convert `SocketAddr` from/into a `libc::sockaddr` because `SocketAddr` has a different
//! internal layout.

//!
//! This crate provides [OsSocketAddr] which holds a `libc::sockaddr` (containing an IPv4 or IPv6
//! address) and the conversion functions from/into `SocketAddr`.
//!
//!
//! # Example
//!
//! ```
//! # mod foo {
//! extern crate libc;
//! extern crate os_socketaddr;
//!
//! use std::net::SocketAddr;
//! use self::libc::{c_int, c_void, size_t, ssize_t};
//! use self::os_socketaddr::OsSocketAddr;
//!
//! ////////// unix examples //////////
//!
//! #[cfg(target_family = "unix")]
//! fn sendto(socket: c_int, payload: &[u8], dst: SocketAddr) -> ssize_t
//! {
//!     let addr : OsSocketAddr = dst.into();
//!     unsafe {
//!         libc::sendto(socket, payload.as_ptr() as *const c_void, payload.len() as size_t, 0,
//!                      addr.as_ptr(), addr.len())
//!     }
//! }
//!
//! #[cfg(target_family = "unix")]
//! fn recvfrom(socket: c_int, payload: &mut[u8]) -> (ssize_t, Option<SocketAddr>)
//! {
//!     let mut addr = OsSocketAddr::new();
//!     let mut addrlen = addr.capacity();
//!     let nb = unsafe {
//!         libc::recvfrom(socket, payload.as_mut_ptr() as *mut c_void, payload.len(), 0,
//!                        addr.as_mut_ptr(), &mut addrlen as *mut _)
//!     };
//!     (nb, addr.into())
//! }
//!
//! ////////// windows examples //////////
//!
//! #[cfg(target_family = "windows")]
//! fn sendto(socket: winapi::um::winsock2::SOCKET,
//!           payload: &mut winapi::shared::ws2def::WSABUF,
//!           dst: SocketAddr) -> ssize_t
//! {
//!     let addr : OsSocketAddr = dst.into();
//!     let mut nb : u32 = 0;
//!     match unsafe {
//!         winapi::um::winsock2::WSASendTo(socket, payload, 1u32, &mut nb, 0u32,
//!                                         addr.as_ptr(), addr.len() as i32,
//!                                         std::ptr::null_mut::<winapi::um::minwinbase::OVERLAPPED>(), None)
//!     } {
//!         0 => nb as ssize_t,
//!         _ => -1,
//!     }
//! }
//!
//! #[cfg(target_family = "windows")]
//! fn recvfrom(socket: winapi::um::winsock2::SOCKET,
//!             payload: &mut winapi::shared::ws2def::WSABUF) -> (ssize_t, Option<SocketAddr>)
//! {
//!     let mut addr = OsSocketAddr::new();
//!     let mut addrlen = addr.capacity();
//!     let mut nb : u32 = 0;
//!     let mut flags : u32 = 0;
//!     match unsafe {
//!         winapi::um::winsock2::WSARecvFrom(socket, payload, 1u32, &mut nb, &mut flags,
//!                                           addr.as_mut_ptr(), &mut addrlen as *mut _,
//!                                           std::ptr::null_mut::<winapi::um::minwinbase::OVERLAPPED>(), None)
//!     } {
//!         0 => (nb as ssize_t, addr.into()),
//!         _ => (-1, None),
//!     }
//! }
//! # }
//! ```
//!

extern crate libc;

use std::convert::TryInto;
use std::net::{Ipv4Addr,Ipv6Addr,SocketAddr,SocketAddrV4,SocketAddrV6};

#[cfg(not(target_os = "windows"))]
use libc::{sockaddr, sockaddr_in, sockaddr_in6, socklen_t, AF_INET, AF_INET6, in_addr, in6_addr};

#[cfg(target_os = "windows")]
use winapi::{
    shared::{
        ws2def::{AF_INET, AF_INET6, SOCKADDR as sockaddr, SOCKADDR_IN as sockaddr_in},
        ws2ipdef::SOCKADDR_IN6_LH as sockaddr_in6,
    },
    um::ws2tcpip::socklen_t,
};

/// A type for handling platform-native socket addresses (`struct sockaddr`)
///
/// This type has a buffer big enough to hold a [libc::sockaddr_in] or [libc::sockaddr_in6]
/// struct. Its content can be arbitrary written using [.as_mut()](Self::as_mut) or
/// [.as_mut_ptr()](Self::as_mut_ptr).
///
/// It also provides the conversion functions from/into [SocketAddr].
///
/// See [crate] level documentation.
///
#[derive(Copy, Clone)]
#[repr(C)]
pub union OsSocketAddr {
    sa4: sockaddr_in,
    sa6: sockaddr_in6,
}

#[allow(dead_code)]
impl OsSocketAddr {
    /// Create a new empty socket address
    pub fn new() -> Self {
        OsSocketAddr {
            sa6: unsafe { std::mem::zeroed() },
        }
    }

    /// Create a new socket address from a raw slice
    ///
    /// # Panics
    ///
    /// Panics if `len` is bigger that the size of [sockaddr_in6]
    ///
    pub unsafe fn from_raw_parts(ptr: *const u8, len: usize) -> Self {
        let mut raw = OsSocketAddr::new();
        assert!(len <= std::mem::size_of_val(&raw.sa6));
        raw.as_mut()[..len].copy_from_slice(std::slice::from_raw_parts(ptr, len));
        raw
    }

    /// Create a new socket address from a [SocketAddr] object
    pub fn from(addr: SocketAddr) -> Self {
        addr.into()
    }

    /// Attempt to convert the internal buffer into a [SocketAddr] object
    ///
    /// The internal buffer is assumed to be a [sockaddr].
    ///
    /// If the value of `.sa_family` resolves to `AF_INET` or `AF_INET6` then the buffer is
    /// converted into `SocketAddr`, otherwise the function returns None.
    ///
    pub fn into_addr(self) -> Option<SocketAddr> {
        self.into()
    }

    /// Return the length of the address
    ///
    /// The result depends on the value of `.sa_family` in the internal buffer:
    /// * `AF_INET`  -> the size of [sockaddr_in]
    /// * `AF_INET6` -> the size of [sockaddr_in6]
    /// * *other* -> 0
    pub fn len(&self) -> socklen_t {
        (match unsafe { self.sa6.sin6_family } as i32 {
            AF_INET => std::mem::size_of::<sockaddr_in>(),
            AF_INET6 => std::mem::size_of::<sockaddr_in6>(),
            _ => 0,
        }) as socklen_t
    }

    /// Return the size of the internal buffer
    pub fn capacity(&self) -> socklen_t {
        std::mem::size_of::<sockaddr_in6>() as socklen_t
    }

    /// Get a pointer to the internal buffer
    pub fn as_ptr(&self) -> *const sockaddr {
        unsafe { &self.sa6 as *const _ as *const _ }
    }

    /// Get a mutable pointer to the internal buffer
    pub fn as_mut_ptr(&mut self) -> *mut sockaddr {
        unsafe { &mut self.sa6 as *mut _ as *mut _ }
    }
}

impl AsRef<[u8]> for OsSocketAddr {
    /// Get the internal buffer as a byte slice
    ///
    /// Note: the actual length of slice depends on the value of `.sa_family`
    /// (see [.len()](Self::len))
    ///
    fn as_ref(&self) -> &[u8] {
        unsafe {
            std::slice::from_raw_parts(&self.sa6 as *const _ as *const u8, self.len() as usize)
        }
    }
}

impl AsMut<[u8]> for OsSocketAddr {
    /// Get the internal buffer as a mutable slice
    fn as_mut(&mut self) -> &mut [u8] {
        unsafe {
            std::slice::from_raw_parts_mut(
                &mut self.sa6 as *mut _ as *mut u8,
                self.capacity() as usize,
            )
        }
    }
}

impl Into<Option<SocketAddr>> for OsSocketAddr {
    /// Attempt to convert the internal buffer into a [SocketAddr] object
    ///
    /// The internal buffer is assumed to be a [sockaddr].
    ///
    /// If the value of `.sa_family` resolves to `AF_INET` or `AF_INET6` then the buffer is
    /// converted into `SocketAddr`, otherwise the function returns None.
    ///
    fn into(self) -> Option<SocketAddr> {
        self.try_into().ok()
    }
}

impl TryInto<SocketAddr> for OsSocketAddr {
    type Error = BadFamilyError;

    /// Attempt to convert the internal buffer into a [SocketAddr] object
    ///
    /// The internal buffer is assumed to be a [sockaddr].
    ///
    /// If the value of `.sa_family` resolves to `AF_INET` or `AF_INET6` then the buffer is
    /// converted into `SocketAddr`, otherwise the function returns an error.
    ///
    fn try_into(self) -> Result<SocketAddr, BadFamilyError> {
        unsafe {
            match self.sa6.sin6_family as i32 {
                AF_INET => {
                    #[cfg(not(target_os = "windows"))]
                    let ip = self.sa4.sin_addr.s_addr;
                    #[cfg(target_os = "windows")]
                    let ip = *self.sa4.sin_addr.S_un.S_addr();

                    Ok(SocketAddr::V4(SocketAddrV4::new(
                            Ipv4Addr::from(u32::from_be(ip)),
                            u16::from_be(self.sa4.sin_port),
                        )))
                },
                AF_INET6 => {
                    #[cfg(not(target_os = "windows"))]
                    let (ip, scope_id) = (self.sa6.sin6_addr.s6_addr, self.sa6.sin6_scope_id);
                    #[cfg(target_os = "windows")]
                    let (ip, scope_id) = (*self.sa6.sin6_addr.u.Byte(), *self.sa6.u.sin6_scope_id());

                    Ok(SocketAddr::V6(SocketAddrV6::new(
                            Ipv6Addr::from(u128::from_be_bytes(ip)),
                            u16::from_be(self.sa6.sin6_port),
                            self.sa6.sin6_flowinfo,
                            scope_id)))
                },
                f => Err(BadFamilyError(f)),
            }
        }
    }
}

/// Error type returned by [OsSocketAddr::try_into()]
#[derive(Debug,Eq,PartialEq)]
pub struct BadFamilyError(i32);
impl std::error::Error for BadFamilyError {}
impl std::fmt::Display for BadFamilyError {
   fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
   {
       "not an ip address (family=".fmt(f)?;
       self.0.fmt(f)?;
       ')'.fmt(f)
   }
}

impl From<SocketAddr> for OsSocketAddr {
    fn from(addr: SocketAddr) -> Self {
        match addr {
            SocketAddr::V4(addr) => {
                let raw_ip = u32::to_be((*addr.ip()).into());

                #[cfg(any(
                        target_os = "android",
                        target_os = "emscripten",
                        target_os = "fuchsia",
                        target_os = "illumos",
                        target_os = "l4re",
                        target_os = "linux",
                        target_os = "redox",
                        target_os = "solaris",
                        ))]
                return Self{ sa4: sockaddr_in{
                    sin_family: AF_INET as u16,
                    sin_port: u16::to_be(addr.port()),
                    sin_addr: in_addr{ s_addr: raw_ip },
                    sin_zero: Default::default(),
                }};

                #[cfg(any(
                        target_os = "dragonfly",
                        target_os = "freebsd",
                        target_os = "haiku",
                        target_os = "hermit",
                        target_os = "ios",
                        target_os = "macos",
                        target_os = "netbsd",
                        target_os = "openbsd",
                        target_os = "vxworks",
                        target_os = "watchos",
                        ))]
                return Self{ sa4: sockaddr_in {
                    sin_len: std::mem::size_of::<sockaddr_in>() as u8,
                    sin_family: AF_INET as u8,
                    sin_port: u16::to_be(addr.port()),
                    sin_addr: in_addr{ s_addr: raw_ip },
                    sin_zero: Default::default(),
                }};

                #[cfg(target_os = "windows")]
                return {
                    let mut osa = Self{ sa4: sockaddr_in{
                        sin_family: AF_INET as u16,
                        sin_port: u16::to_be(addr.port()),
                        sin_addr: unsafe { std::mem::zeroed() },
                        sin_zero: Default::default(),
                    }};
                    unsafe { *osa.sa4.sin_addr.S_un.S_addr_mut() = raw_ip; }
                    osa
                };
            },
            SocketAddr::V6(addr) => {
                let raw_ip = u128::to_be_bytes((*addr.ip()).into());

                #[cfg(any(
                        target_os = "android",
                        target_os = "emscripten",
                        target_os = "fuchsia",
                        target_os = "illumos",
                        target_os = "l4re",
                        target_os = "linux",
                        target_os = "redox",
                        target_os = "solaris",
                        ))]
                return Self{ sa6: sockaddr_in6{
                    sin6_family: AF_INET6 as u16,
                    sin6_port: u16::to_be(addr.port()),
                    sin6_flowinfo: addr.flowinfo(),
                    sin6_addr: in6_addr{ s6_addr: raw_ip },
                    sin6_scope_id: addr.scope_id(),
                    #[cfg(any(target_os = "solaris", target_os = "illumos"))]
                    __sin6_src_id: 0,
                }};

                #[cfg(any(
                        target_os = "dragonfly",
                        target_os = "freebsd",
                        target_os = "haiku",
                        target_os = "hermit",
                        target_os = "ios",
                        target_os = "macos",
                        target_os = "netbsd",
                        target_os = "openbsd",
                        target_os = "vxworks",
                        target_os = "watchos",
                        ))]
                return Self{ sa6: sockaddr_in6{
                    sin6_len: std::mem::size_of::<sockaddr_in6>() as u8,
                    sin6_family: AF_INET6 as u8,
                    sin6_port: u16::to_be(addr.port()),
                    sin6_flowinfo: addr.flowinfo(),
                    sin6_addr: in6_addr{ s6_addr: raw_ip },
                    sin6_scope_id: addr.scope_id(),
                }};

                #[cfg(target_os = "windows")]
                return {
                    let mut osa = Self{ sa6: sockaddr_in6{
                        sin6_family: AF_INET6 as u16,
                        sin6_port: u16::to_be(addr.port()),
                        sin6_flowinfo: addr.flowinfo(),
                        sin6_addr: unsafe { std::mem::zeroed() },
                        u:         unsafe { std::mem::zeroed() },
                    }};
                    unsafe {
                        *osa.sa6.sin6_addr.u.Byte_mut() = raw_ip;
                        *osa.sa6.u.sin6_scope_id_mut() = addr.scope_id();
                    }
                    osa
                };
            }
        }
    }
}

impl From<Option<SocketAddr>> for OsSocketAddr {
    fn from(addr: Option<SocketAddr>) -> Self {
        match addr {
            None => Self::new(),
            Some(addr) => addr.into(),
        }
    }
}

impl std::fmt::Debug for OsSocketAddr {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.into_addr().fmt(fmt)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::SocketAddrV6;

    #[cfg(not(target_os = "windows"))]
    use libc::{in6_addr, in_addr};

    #[cfg(target_os = "windows")]
    use winapi::shared::{in6addr::in6_addr, inaddr::in_addr};

    fn check_as_mut(osa: &mut OsSocketAddr) {
        let ptr = osa as *mut _ as usize;
        let buf = osa.as_mut();
        assert_eq!(buf.as_mut_ptr(), ptr as *mut _);
        assert_eq!(buf.len(), std::mem::size_of::<sockaddr_in6>());
    }

    #[test]
    fn ptr_and_capacity() {
        let mut osa = OsSocketAddr::new();
        assert_eq!(osa.as_ptr(), &osa as *const _ as *const _);
        assert_eq!(osa.as_mut_ptr(), &mut osa as *mut _ as *mut _);
        assert_eq!(osa.capacity() as usize, std::mem::size_of::<sockaddr_in6>());
    }

    #[test]
    fn as_slice() {
        let mut osa = OsSocketAddr::new();
        {
            let sl = osa.as_ref();
            assert_eq!(sl.as_ptr(), &osa as *const _ as *const _);
            assert_eq!(sl.len(), 0);
        }
        {
            let ptr = &mut osa as *mut _ as *mut _;
            let sl = osa.as_mut();
            assert_eq!(sl.as_mut_ptr(), ptr);
            assert_eq!(sl.len(), std::mem::size_of::<sockaddr_in6>());
        }
    }

    #[test]
    fn os_socketaddr_ipv4() {
        let addr: SocketAddr = "12.34.56.78:4242".parse().unwrap();
        unsafe {
            #[cfg(any(
                    target_os = "android",
                    target_os = "emscripten",
                    target_os = "fuchsia",
                    target_os = "illumos",
                    target_os = "l4re",
                    target_os = "linux",
                    target_os = "redox",
                    target_os = "solaris",

                    target_os = "windows",
                    ))]
            let sa = sockaddr_in {
                sin_family: AF_INET as u16,
                sin_addr: *(&[12u8, 34, 56, 78] as *const _ as *const in_addr),
                sin_port: 4242u16.to_be(),
                sin_zero: std::mem::zeroed(),
            };
            #[cfg(any(
                    target_os = "dragonfly",
                    target_os = "freebsd",
                    target_os = "haiku",
                    target_os = "hermit",
                    target_os = "ios",
                    target_os = "macos",
                    target_os = "netbsd",
                    target_os = "openbsd",
                    target_os = "vxworks",
                    target_os = "watchos",
                    ))]
            let sa = sockaddr_in {
                sin_len: std::mem::size_of::<sockaddr_in>() as u8,
                sin_family: AF_INET as u8,
                sin_addr: *(&[12u8, 34, 56, 78] as *const _ as *const in_addr),
                sin_port: 4242u16.to_be(),
                sin_zero: std::mem::zeroed(),
            };
            let mut osa = OsSocketAddr::from_raw_parts(
                &sa as *const _ as *const u8,
                std::mem::size_of_val(&sa),
            );
            assert_eq!(osa.len() as usize, std::mem::size_of::<sockaddr_in>());
            assert_eq!(osa.capacity() as usize, std::mem::size_of::<sockaddr_in6>());
            assert_eq!(osa.into_addr(), Some(addr));
            assert_eq!(osa.try_into(), Ok(addr));
            assert_eq!(OsSocketAddr::from(addr).into_addr(), Some(addr));
            {
                let buf = osa.as_ref();
                assert_eq!(buf.as_ptr(), &osa as *const _ as *const _);
                assert_eq!(buf.len(), std::mem::size_of_val(&sa));
            }
            check_as_mut(&mut osa);
        }
    }

    #[test]
    fn os_socketaddr_ipv6() {
        let ip = [
            7u8, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
        ];
        let addr = SocketAddr::V6(SocketAddrV6::new(ip.into(), 4242, 0x11223344, 0x55667788));
        unsafe {
            #[cfg(any(
                    target_os = "android",
                    target_os = "emscripten",
                    target_os = "fuchsia",
                    target_os = "illumos",
                    target_os = "l4re",
                    target_os = "linux",
                    target_os = "redox",
                    target_os = "solaris",
                    ))]
            let sa = sockaddr_in6 {
                sin6_family: AF_INET6 as u16,
                sin6_addr: *(&ip as *const _ as *const in6_addr),
                sin6_port: 4242u16.to_be(),
                sin6_flowinfo: 0x11223344,
                sin6_scope_id: 0x55667788,
            };
            #[cfg(any(
                    target_os = "dragonfly",
                    target_os = "freebsd",
                    target_os = "haiku",
                    target_os = "hermit",
                    target_os = "ios",
                    target_os = "macos",
                    target_os = "netbsd",
                    target_os = "openbsd",
                    target_os = "vxworks",
                    target_os = "watchos",
                    ))]
            let sa = sockaddr_in6 {
                sin6_len: std::mem::size_of::<sockaddr_in6>() as u8,
                sin6_family: AF_INET6 as u8,
                sin6_addr: *(&ip as *const _ as *const in6_addr),
                sin6_port: 4242u16.to_be(),
                sin6_flowinfo: 0x11223344,
                sin6_scope_id: 0x55667788,
            };
            #[cfg(target_os = "windows")]
            let mut sa = sockaddr_in6 {
                sin6_family: AF_INET6 as u16,
                sin6_addr: *(&ip as *const _ as *const in6_addr),
                sin6_port: 4242u16.to_be(),
                sin6_flowinfo: 0x11223344,
                u: std::mem::zeroed(),
            };
            #[cfg(target_os = "windows")]
            let sa = {
                let scope_id = sa.u.sin6_scope_id_mut();
                *scope_id = 0x55667788;
                sa
            };

            let mut osa = OsSocketAddr::from_raw_parts(
                &sa as *const _ as *const u8,
                std::mem::size_of_val(&sa),
            );
            assert_eq!(osa.len() as usize, std::mem::size_of::<sockaddr_in6>());
            assert_eq!(osa.capacity() as usize, std::mem::size_of::<sockaddr_in6>());
            assert_eq!(osa.into_addr(), Some(addr));
            assert_eq!(osa.try_into(), Ok(addr));
            assert_eq!(OsSocketAddr::from(addr).into_addr(), Some(addr));
            {
                let buf = osa.as_ref();
                assert_eq!(buf.as_ptr(), &osa as *const _ as *const _);
                assert_eq!(buf.len(), std::mem::size_of_val(&sa));
            }
            check_as_mut(&mut osa);
        }
    }

    #[test]
    fn os_socketaddr_other() {
        fn check(mut osa: OsSocketAddr) {
            assert_eq!(osa.into_addr(), None);

            let r : Result<SocketAddr, _> = osa.try_into();
            assert!(r.is_err());
            {
                let buf = osa.as_ref();
                assert_eq!(buf.len(), 0);
                assert_eq!(osa.len(), 0);
                assert_eq!(osa.capacity() as usize, std::mem::size_of::<sockaddr_in6>());
            }
            check_as_mut(&mut osa);
        }

        check(OsSocketAddr::new());
        check(None.into());
        unsafe {
            check(OsSocketAddr::from_raw_parts(
                [0xde, 0xad, 0xbe, 0xef].as_ptr(),
                4,
            ));
        }

        let r : Result<SocketAddr, BadFamilyError> = OsSocketAddr::new().try_into();
        assert!(r.is_err());
        let e = r.unwrap_err();
        assert_eq!(e, BadFamilyError(0));
        assert_eq!(e.to_string(), "not an ip address (family=0)");
    }
}
