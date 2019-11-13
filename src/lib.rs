//! This crate provides a type that can act as a platform-native socket address
//! (i.e. `libc::sockaddr`)
//!
//! #Motivation
//!
//! The std crate provides `std::net::SocketAddr` for managing socket addresses. Its `V4` variant
//! encapsulates a `libc::sockaddr_in` and its `V6` variant encapsulates a `libc::sockaddr_in6`.
//! However there is no easy way to convert `SocketAddr` from/into a `libc::sockaddr`, because
//! `SocketAddr` is a rust enum.
//!
//! This crate provides `OsSocketAddr` which holds a `libc::sockaddr` (containing an IPv4 or IPv6
//! address) and the conversion functions from/into `std::net::SocketAddr`.
//!
//!
//! #Example
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
//! #[cfg(target_family = "unix")]
//! fn send(socket: c_int, buf: &[u8], dst: SocketAddr) -> ssize_t {
//!     let addr : OsSocketAddr = dst.into();
//!     unsafe {
//!         libc::sendto(socket, buf.as_ptr() as *const c_void, buf.len() as size_t, 0,
//!                      addr.as_ptr(), addr.len())
//!     }
//! }
//!
//! #[cfg(target_family = "windows")]
//! fn send(socket: winapi::um::winsock2::SOCKET, buf: &mut [u8], dst: SocketAddr) -> ssize_t {
//!     let addr : OsSocketAddr = dst.into();
//!     let mut wsabuf = winapi::shared::ws2def::WSABUF {
//!         len: buf.len() as u32,
//!         buf: buf.as_ptr() as *mut i8,
//!     };
//!     let mut numberOfBytesSent: u32 = 0;
//!     let nb = unsafe {
//!         winapi::um::winsock2::WSASendTo(socket, &mut wsabuf, 1u32, &mut numberOfBytesSent, 0u32,
//!                                         addr.as_ptr(), addr.len() as i32,
//!                                         std::ptr::null_mut::<winapi::um::minwinbase::OVERLAPPED>(), None)
//!     };
//!     if nb == 0 {
//!         numberOfBytesSent as isize
//!     } else {
//!         -1
//!     }
//! }
//!
//! #[cfg(target_family = "unix")]
//! fn receive(socket: c_int, buf: &mut[u8]) -> (ssize_t, Option<SocketAddr>)
//! {
//!     let mut addr = OsSocketAddr::new();
//!     let mut addrlen = addr.capacity();
//!     let nb = unsafe {
//!         libc::recvfrom(socket, buf.as_mut_ptr() as *mut c_void, buf.len(), 0,
//!                        addr.as_mut_ptr(), &mut addrlen as *mut _)
//!     };
//!     (nb, addr.into())
//! }
//!
//! #[cfg(target_family = "windows")]
//! fn receive(socket: winapi::um::winsock2::SOCKET, buf: &mut[u8]) -> (ssize_t, Option<SocketAddr>)
//! {
//!     let mut addr = OsSocketAddr::new();
//!     let mut addrlen = addr.capacity();
//!     let mut wsabuf = winapi::shared::ws2def::WSABUF {
//!         len: buf.len() as u32,
//!         buf: buf.as_ptr() as *mut i8,
//!     };
//!     let mut numberOfBytesRecvd: u32 = 0;
//!     let mut flags: u32 = 0;
//!     let nb = unsafe {
//!         winapi::um::winsock2::WSARecvFrom(socket, &mut wsabuf, 1u32, &mut numberOfBytesRecvd, &mut flags,
//!                                           addr.as_mut_ptr(), &mut addrlen as *mut _,
//!                                           std::ptr::null_mut::<winapi::um::minwinbase::OVERLAPPED>(), None)
//!     };
//!     if nb == 0 {
//!         (numberOfBytesRecvd as isize, addr.into())
//!     } else {
//!         (-1, None)
//!     }
//! }
//! # }
//! ```
//!

extern crate libc;

use std::net::SocketAddr;

/// A type for handling platform-native socket addresses (`struct sockaddr`)
///
/// This type holds a buffer enough big to have a `libc::sockaddr_in` or `libc::sockaddr_in6`
/// struct. Its content can be arbitrary written using `.as_mut()` or `.as_mut_ptr()`.
///
/// It also provides the conversion functions from/into `std::net::SocketAddr`.
///
/// See [module level][mod] documentation for more details.
///
/// [mod]: index.html
///
#[cfg(target_family = "unix")]
use libc::AF_INET;

#[cfg(target_family = "unix")]
use libc::AF_INET6;

#[cfg(target_family = "unix")]
use libc::socklen_t;

#[cfg(target_family = "unix")]
use libc::sockaddr;

#[cfg(target_family = "unix")]
use libc::sockaddr_in;

#[cfg(target_family = "unix")]
use libc::sockaddr_in6;

#[cfg(target_family = "unix")]
use libc::in_addr;

#[cfg(target_family = "unix")]
use libc::in6_addr;

#[cfg(target_family = "windows")]
use winapi::shared::ws2def::AF_INET;

#[cfg(target_family = "windows")]
use winapi::shared::ws2def::AF_INET6;

#[cfg(target_family = "windows")]
use winapi::um::ws2tcpip::socklen_t;

#[cfg(target_family = "windows")]
use winapi::shared::ws2def::SOCKADDR as sockaddr;

#[cfg(target_family = "windows")]
use winapi::shared::ws2def::SOCKADDR_IN as sockaddr_in;

#[cfg(target_family = "windows")]
use winapi::shared::ws2ipdef::SOCKADDR_IN6_LH as sockaddr_in6;

#[cfg(target_family = "windows")]
use winapi::shared::inaddr::in_addr;

#[cfg(target_family = "windows")]
use winapi::shared::in6addr::in6_addr;

#[derive(Copy, Clone)]
pub struct OsSocketAddr {
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
    /// Panics if `len` is bigger that the size of `libc::sockaddr_in6`
    ///
    pub unsafe fn from_raw_parts(ptr: *const u8, len: usize) -> Self {
        let mut raw = OsSocketAddr::new();
        assert!(len <= std::mem::size_of_val(&raw.sa6));
        raw.as_mut()[..len].copy_from_slice(std::slice::from_raw_parts(ptr, len));
        raw
    }

    /// Create a new socket address from a `std::net::SocketAddr` object
    pub fn from(addr: SocketAddr) -> Self {
        addr.into()
    }

    /// Attempt to convert the internal buffer into a `std::net::SocketAddr` object
    ///
    /// The internal buffer is assumed to be a `libc::sockaddr`.
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
    /// * `AF_INET`  -> the size of `sockaddr_in`
    /// * `AF_INET6` -> the size of `sockaddr_in6`
    /// * *other* -> 0
    pub fn len(&self) -> socklen_t {
        (match self.sa6.sin6_family as i32 {
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
        &self.sa6 as *const _ as *const _
    }

    /// Get a mutable pointer to the internal buffer
    pub fn as_mut_ptr(&mut self) -> *mut sockaddr {
        &mut self.sa6 as *mut _ as *mut _
    }
}

impl AsRef<[u8]> for OsSocketAddr {
    /// Get the internal buffer as a byte slice
    ///
    /// Note: the actual length of slice depends on the value of `.sa_family` (see `.len()`)
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
    /// Attempt to convert the internal buffer into a `std::net::SocketAddr` object
    ///
    /// The internal buffer is assumed to be a `libc::sockaddr`.
    ///
    /// If the value of `.sa_family` resolves to `AF_INET` or `AF_INET6` then the buffer is
    /// converted into `SocketAddr`, otherwise the function returns None.
    ///
    fn into(self) -> Option<SocketAddr> {
        unsafe {
            match self.sa6.sin6_family as i32 {
                AF_INET => Some(SocketAddr::V4(*(self.as_ptr() as *const _))),
                AF_INET6 => Some(SocketAddr::V6(*(self.as_ptr() as *const _))),
                _ => None,
            }
        }
    }
}

impl From<SocketAddr> for OsSocketAddr {
    fn from(addr: SocketAddr) -> Self {
        OsSocketAddr {
            sa6: unsafe {
                match addr {
                    SocketAddr::V4(addr) => {
                        let mut sa6 = std::mem::uninitialized();
                        *(&mut sa6 as *mut _ as *mut _) = addr;
                        sa6
                    }
                    SocketAddr::V6(addr) => *(&addr as *const _ as *const _),
                }
            },
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
            let sa = sockaddr_in {
                sin_family: AF_INET as u16,
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
            #[cfg(target_family = "unix")]
            let sa = sockaddr_in6 {
                sin6_family: AF_INET6 as u16,
                sin6_addr: *(&ip as *const _ as *const in6_addr),
                sin6_port: 4242u16.to_be(),
                sin6_flowinfo: 0x11223344,
                sin6_scope_id: 0x55667788,
            };
            #[cfg(target_family = "windows")]
            let mut sa = sockaddr_in6 {
                sin6_family: AF_INET6 as u16,
                sin6_addr: *(&ip as *const _ as *const in6_addr),
                sin6_port: 4242u16.to_be(),
                sin6_flowinfo: 0x11223344,
                u: unsafe { std::mem::zeroed() },
            };
            #[cfg(target_family = "windows")]
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
        fn check(osa: &mut OsSocketAddr) {
            assert_eq!(osa.into_addr(), None);
            {
                let buf = osa.as_ref();
                assert_eq!(buf.len(), 0);
                assert_eq!(osa.len(), 0);
                assert_eq!(osa.capacity() as usize, std::mem::size_of::<sockaddr_in6>());
            }
            check_as_mut(osa);
        };

        check(&mut OsSocketAddr::new());
        check(&mut None.into());

        unsafe {
            check(&mut OsSocketAddr::from_raw_parts(
                [0xde, 0xad, 0xbe, 0xef].as_ptr(),
                4,
            ));
        }
    }
}
