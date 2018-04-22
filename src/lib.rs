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
//! fn send(socket: c_int, buf: &[u8], dst: SocketAddr) -> ssize_t {
//!     let addr : OsSocketAddr = dst.into();
//!     unsafe {
//!         libc::sendto(socket, buf.as_ptr() as *const c_void, buf.len() as size_t, 0,
//!                      addr.as_ptr(), addr.len())
//!     }
//! }
//! 
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
#[derive(Copy,Clone)]
pub struct OsSocketAddr
{
    sa6: libc::sockaddr_in6
}

#[allow(dead_code)]
impl OsSocketAddr {

    /// Create a new empty socket address
    pub fn new() -> Self
    {
        OsSocketAddr{sa6: unsafe { std::mem::zeroed() }}
    }

    /// Create a new socket address from a raw slice
    /// 
    /// # Panics
    /// 
    /// Panics if `len` is bigger that the size of `libc::sockaddr_in6`
    /// 
    pub unsafe fn from_raw_parts(ptr: *const u8, len: usize) -> Self
    {
        let mut raw = OsSocketAddr::new();
        assert!(len <= std::mem::size_of_val(&raw.sa6));
        raw.as_mut()[..len].copy_from_slice(std::slice::from_raw_parts(ptr, len));
        raw
    }

    /// Create a new socket address from a `std::net::SocketAddr` object
    pub fn from(addr: SocketAddr) -> Self
    {
        addr.into()
    }

    /// Attempt to convert the internal buffer into a `std::net::SocketAddr` object
    /// 
    /// The internal buffer is assumed to be a `libc::sockaddr`.
    /// 
    /// If the value of `.sa_family` resolves to `AF_INET` or `AF_INET6` then the buffer is
    /// converted into `SocketAddr`, otherwise the function returns None.
    /// 
    pub fn into_addr(self) -> Option<SocketAddr>
    {
        self.into()
    }

    /// Return the length of the address
    /// 
    /// The result depends on the value of `.sa_family` in the internal buffer:
    /// * `AF_INET`  -> the size of `sockaddr_in`
    /// * `AF_INET6` -> the size of `sockaddr_in6`
    /// * *other* -> 0
    pub fn len(&self) -> libc::socklen_t
    {
        (match self.sa6.sin6_family as i32 {
            libc::AF_INET  => std::mem::size_of::<libc::sockaddr_in >(),
            libc::AF_INET6 => std::mem::size_of::<libc::sockaddr_in6>(),
            _ => 0
        }) as libc::socklen_t
    }

    /// Return the size of the internal buffer
    pub fn capacity(&self) -> libc::socklen_t
    {
        std::mem::size_of::<libc::sockaddr_in6>() as libc::socklen_t
    }

    /// Get a pointer to the internal buffer
    pub fn as_ptr(&self) -> *const libc::sockaddr {
        &self.sa6 as *const _ as *const _
    }

    /// Get a mutable pointer to the internal buffer
    pub fn as_mut_ptr(&mut self) -> *mut libc::sockaddr {
        &mut self.sa6 as *mut _ as *mut _
    }

}

impl AsRef<[u8]> for OsSocketAddr
{
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

impl AsMut<[u8]> for OsSocketAddr
{
    /// Get the internal buffer as a mutable slice
    fn as_mut(&mut self) -> &mut[u8] {
        unsafe {
            std::slice::from_raw_parts_mut(&mut self.sa6 as *mut _ as *mut u8,
                                           self.capacity() as usize)
        }
    }
}

impl Into<Option<SocketAddr>> for OsSocketAddr
{
    /// Attempt to convert the internal buffer into a `std::net::SocketAddr` object
    /// 
    /// The internal buffer is assumed to be a `libc::sockaddr`.
    /// 
    /// If the value of `.sa_family` resolves to `AF_INET` or `AF_INET6` then the buffer is
    /// converted into `SocketAddr`, otherwise the function returns None.
    /// 
    fn into(self) -> Option<SocketAddr>
    {
        unsafe { match self.sa6.sin6_family as i32 {
                libc::AF_INET   => Some(SocketAddr::V4(*(self.as_ptr() as *const _))),
                libc::AF_INET6  => Some(SocketAddr::V6(*(self.as_ptr() as *const _))),
                _ => None
        }}
    }
}

impl From<SocketAddr> for OsSocketAddr
{
    fn from(addr: SocketAddr) -> Self
    {
        OsSocketAddr{sa6: unsafe {
            match addr {
                SocketAddr::V4(addr) => {
                    let mut sa6 = std::mem::uninitialized();
                    *(&mut sa6 as *mut _ as *mut _) = addr;
                    sa6
                },
                SocketAddr::V6(addr) =>
                    *(&addr as *const _ as *const _),
            }
        }}
    }
}

impl From<Option<SocketAddr>> for OsSocketAddr
{
    fn from(addr: Option<SocketAddr>) -> Self
    {
        match addr {
            None => Self::new(),
            Some(addr) => addr.into(),
        }
    }
}

impl std::fmt::Debug for OsSocketAddr
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result
    {
        self.into_addr().fmt(fmt)
    }
}

#[cfg(test)]
mod tests {
    use std::net::SocketAddrV6;
    use super::*;

    fn check_as_mut(osa: &mut OsSocketAddr)
    {
        let ptr = osa as *mut _ as usize;
        let buf = osa.as_mut();
        assert_eq!(buf.as_mut_ptr(), ptr as *mut _);
        assert_eq!(buf.len(), std::mem::size_of::<libc::sockaddr_in6>());
    }

    #[test]
    fn ptr_and_capacity() {
        let mut osa = OsSocketAddr::new();
        assert_eq!(osa.as_ptr(), &osa as *const _ as *const _);
        assert_eq!(osa.as_mut_ptr(), &mut osa as *mut _ as *mut _);
        assert_eq!(osa.capacity() as usize, std::mem::size_of::<libc::sockaddr_in6>());
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
            assert_eq!(sl.len(), std::mem::size_of::<libc::sockaddr_in6>());
        }
    }

    #[test]
    fn os_socketaddr_ipv4()
    {
        let addr : SocketAddr = "12.34.56.78:4242".parse().unwrap();
        unsafe {
            let sa = libc::sockaddr_in {
                sin_family: libc::AF_INET as u16,
                sin_addr: *(&[12u8,34,56,78] as *const _ as *const libc::in_addr),
                sin_port: 4242u16.to_be(),
                sin_zero: std::mem::zeroed(),
            };
            let mut osa = OsSocketAddr::from_raw_parts(&sa as *const _ as *const u8,
                                                    std::mem::size_of_val(&sa));
            assert_eq!(osa.len()      as usize, std::mem::size_of::<libc::sockaddr_in>());
            assert_eq!(osa.capacity() as usize, std::mem::size_of::<libc::sockaddr_in6>());
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
    fn os_socketaddr_ipv6()
    {
        let ip = [7u8,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22];
        let addr = SocketAddr::V6(SocketAddrV6::new(ip.into(), 4242,
                        0x11223344, 0x55667788));
        unsafe {
            let sa = libc::sockaddr_in6 {
                sin6_family: libc::AF_INET6 as u16,
                sin6_addr: *(&ip as *const _ as *const libc::in6_addr),
                sin6_port: 4242u16.to_be(),
                sin6_flowinfo: 0x11223344,
                sin6_scope_id: 0x55667788,
            };
            let mut osa = OsSocketAddr::from_raw_parts(&sa as *const _ as *const u8,
                                                    std::mem::size_of_val(&sa));
            assert_eq!(osa.len()      as usize, std::mem::size_of::<libc::sockaddr_in6>());
            assert_eq!(osa.capacity() as usize, std::mem::size_of::<libc::sockaddr_in6>());
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
    fn os_socketaddr_other()
    {
        fn check(osa: &mut OsSocketAddr) {
            assert_eq!(osa.into_addr(), None);
            {
                let buf = osa.as_ref();
                assert_eq!(buf.len(), 0);
                assert_eq!(osa.len(), 0);
                assert_eq!(osa.capacity() as usize, std::mem::size_of::<libc::sockaddr_in6>());
            }
            check_as_mut(osa);
        };

        check(&mut OsSocketAddr::new());
        check(&mut None.into());

        unsafe {
            check(&mut OsSocketAddr::from_raw_parts([0xde,0xad,0xbe,0xef].as_ptr(), 4));
        }
    }
}

