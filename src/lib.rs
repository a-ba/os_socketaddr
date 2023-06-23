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
//! address) and the conversion functions:
//!
//!   - from/into `SocketAddr`
//!   - from `(*const sockaddr, SockLen)`
//!   - into `(*mut sockaddr, *mut SockLen)`
//!
//! where [SockLen] may be any of [i32], [u32], [i64], [u64], [isize] or [usize].
//!
//!
//! # Example
//!
//! ```
//! # mod foo {
//! extern crate libc;
//! extern crate os_socketaddr;
//!
//! use std::net::{SocketAddr,UdpSocket};
//! use self::libc::{c_int, c_void, size_t, ssize_t, sockaddr};
//!
//! use self::os_socketaddr::OsSocketAddr;
//!
//! ////////// unix examples //////////
//!
//! //
//! // calling C functions from Rust
//! //
//!
//! #[cfg(target_family = "unix")]
//! fn sendto(socket: c_int, payload: &[u8], dst: SocketAddr) -> ssize_t
//! {
//!     let addr : OsSocketAddr = dst.into();
//!     unsafe {
//!         libc::sendto(socket, payload.as_ptr() as *const c_void, payload.len(), 0,
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
//! //
//! // calling Rust functions from C
//! //
//!
//! #[cfg(target_family = "unix")]
//! #[no_mangle]
//! pub unsafe extern "C" fn send_to(
//!         sock: *const UdpSocket, buf: *const u8, buflen: size_t,
//!         addr: *const sockaddr, addrlen: size_t) -> ssize_t
//! {
//! 
//!     let Some(dst) = OsSocketAddr::copy_from_raw(addr, addrlen).into_addr() else {
//!         // not an IPv4/IPv6 address
//!         return -1;
//!     };
//!     let slice = std::slice::from_raw_parts(buf, buflen);
//!     match (*sock).send_to(&slice, dst) {
//!         Ok(nb) => nb as ssize_t,
//!         Err(_) => -1,
//!     }
//! }
//!
//! #[cfg(target_family = "unix")]
//! #[no_mangle]
//! pub unsafe extern "C" fn recv_from(
//!         sock: *const UdpSocket, buf: *mut u8, buflen: size_t,
//!         addr: *mut sockaddr, addrlen: *mut size_t) -> ssize_t
//! {
//!     let slice = std::slice::from_raw_parts_mut(buf, buflen);
//!     match (*sock).recv_from(slice) {
//!         Ok((nb, src)) => {
//!             OsSocketAddr::from(src).copy_to_raw(addr, addrlen);
//!             nb as ssize_t
//!         },
//!         Err(_) => -1,
//!     }
//! }
//!
//! ////////// windows examples //////////
//!
//! //
//! // calling C functions from Rust
//! //
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
//!                                         addr.as_ptr(), addr.len(),
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

use std::convert::{TryFrom,TryInto};
use std::net::{Ipv4Addr,Ipv6Addr,SocketAddr,SocketAddrV4,SocketAddrV6};
use std::str::FromStr;

#[cfg(not(target_os = "windows"))]
use libc::{sockaddr, sockaddr_in, sockaddr_in6, AF_INET, AF_INET6};

#[cfg(target_os = "windows")]
use winapi::shared::{
    ws2def::{AF_INET, AF_INET6, SOCKADDR as sockaddr, SOCKADDR_IN as sockaddr_in},
    ws2ipdef::SOCKADDR_IN6_LH as sockaddr_in6,
};

/// A type for handling platform-native socket addresses (`struct sockaddr`)
///
/// This type has a buffer big enough to hold a [libc::sockaddr_in] or [libc::sockaddr_in6]
/// struct. Its content can be arbitrary written using [.as_mut()](Self::as_mut) or
/// [.as_mut_ptr()](Self::as_mut_ptr).
///
/// It also provides the conversion functions:
///
///   - from/into `SocketAddr`
///   - from `(*const sockaddr, SockLen)`
///   - into `(*mut sockaddr, *mut SockLen)`
///
/// where [SockLen] may be any of [i32], [u32], [i64], [u64], [isize] or [usize].
///
/// See [crate] level documentation.
///
#[derive(Copy, Clone)]
#[repr(C)]
pub union OsSocketAddr {
    sa4: sockaddr_in,
    sa6: sockaddr_in6,
}

/// Portable re-export of `socklen_t`
///
/// Uses `winapi::um::ws2tcpip::socklen_t` on windows and `libc::socklen_t` on other systems.
#[cfg(not(target_os = "windows"))]
pub use libc::socklen_t;
///
/// Portable re-export of `socklen_t`
///
/// Uses `winapi::um::ws2tcpip::socklen_t` on windows and `libc::socklen_t` on other systems.
#[cfg(target_os = "windows")]
pub use winapi::um::ws2tcpip::socklen_t;


/// Trait used for representing the socket address length in any 32 or 64 bit format.
pub trait SockLen : TryFrom<usize> + TryInto<usize> + Copy + Default {}
impl SockLen for i32 {}
impl SockLen for u32 {}
impl SockLen for i64 {}
impl SockLen for u64 {}
impl SockLen for isize {}
impl SockLen for usize {}


#[allow(dead_code)]
impl OsSocketAddr {
    /// Create a new empty socket address (all bytes initialised to 0)
    pub fn new() -> Self {
        OsSocketAddr {
            sa6: unsafe { std::mem::zeroed() },
        }
    }

    /// Create a new socket address from a raw byte slice
    ///
    /// The location pointed by `ptr` is assumed to hold a `struct sockaddr` whose length in bytes
    /// is given by `len`.
    ///
    /// Its content is copied into a new [OsSocketAddr] object. If `len` is greater than the size
    /// of [sockaddr_in6] then the resulting address is truncated. If less, then the extra bytes
    /// are zeroed.
    ///
    /// If the conversion from [SockLen] into [usize] fails, then `len` is assumed to be 0.
    ///
    /// If `ptr` is NULL, then the resulting address is zeroed.
    ///
    /// See also [OsSocketAddr::copy_to_raw]
    pub unsafe fn copy_from_raw<L: SockLen>(ptr: *const sockaddr, len: L) -> Self {
        let mut addr = OsSocketAddr::new();
        if !ptr.is_null() {
            len.try_into().map(|ulen| {
                let src = std::slice::from_raw_parts(ptr as *const u8, ulen);
                let dst = addr.as_mut();
                let nb = src.len().min(dst.len());
                dst[..nb].copy_from_slice(&src[..nb]);
            }).ok();
        }
        addr
    }

    /// Create a new socket address from a raw slice
    #[deprecated(since="0.2.4", note="use copy_from_raw()")]
    pub unsafe fn from_raw_parts(ptr: *const u8, len: usize) -> Self {
        Self::copy_from_raw(ptr as *const sockaddr, len)
    }


    /// Copy the socket address into a raw byte slice
    ///
    /// The value pointed by `len` must be initialised with the length in bytes of the buffer
    /// pointed by `ptr`. On return it contains the actual size of the returned address.
    ///
    /// If the provided buffer is too small, then the returned address is truncated (and `len` will
    /// have a greater value than before the call).
    ///
    /// If the conversion of from [SockLen] into [usize] fails, then `*len` is assumed to be 0.
    ///
    /// If `ptr` is NULL then the function does nothing.
    ///
    /// If the value of .sa_family does not resolve to AF_INET or AF_INET6 then the function
    /// sets `*len` to 0 and returns an error.
    /// 
    /// See also [OsSocketAddr::copy_from_raw]
    pub unsafe fn copy_to_raw<L>(&self, ptr: *mut sockaddr, len: *mut L) -> Result<(), BadFamilyError>
        where L: SockLen
    {
        if !ptr.is_null() {
            let src = self.as_ref();
            let dst = std::slice::from_raw_parts_mut(ptr as *mut u8,
                                                     (*len).try_into().unwrap_or_default());
            if src.len() == 0 {
                *len = L::default();
                return Err(BadFamilyError(self.sa4.sin_family as i32))
            }
            let nb = src.len().min(dst.len());
            dst[..nb].copy_from_slice(&src[..nb]);
            *len = src.len().try_into().unwrap_or_default();
        }
        Ok(())
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
    pub fn len<L: SockLen>(&self) -> L {
        (match unsafe { self.sa6.sin6_family } as i32 {
            AF_INET => std::mem::size_of::<sockaddr_in>(),
            AF_INET6 => std::mem::size_of::<sockaddr_in6>(),
            _ => 0,
        }).try_into().unwrap_or_default()
    }

    /// Return the size of the internal buffer
    pub fn capacity<L: SockLen>(&self) -> L {
        std::mem::size_of::<sockaddr_in6>().try_into().unwrap_or_default()
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
            std::slice::from_raw_parts(&self.sa6 as *const _ as *const u8, self.len())
        }
    }
}

impl AsMut<[u8]> for OsSocketAddr {
    /// Get the internal buffer as a mutable slice
    fn as_mut(&mut self) -> &mut [u8] {
        unsafe {
            std::slice::from_raw_parts_mut(
                &mut self.sa6 as *mut _ as *mut u8,
                self.capacity(),
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
        let mut result : Self = unsafe { std::mem::zeroed() };
        match addr {
            SocketAddr::V4(addr) => {
                let sa4 = unsafe { &mut result.sa4 };

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
                {
                    sa4.sin_len = std::mem::size_of::<sockaddr_in>() as u8;
                }

                sa4.sin_family = AF_INET.try_into().unwrap();
                sa4.sin_port = u16::to_be(addr.port());

                let raw_ip = u32::to_be((*addr.ip()).into());
                #[cfg(not(target_os = "windows"))]
                {
                    sa4.sin_addr.s_addr = raw_ip;
                }
                #[cfg(target_os = "windows")]
                unsafe {
                    *sa4.sin_addr.S_un.S_addr_mut() = raw_ip;
                }
            },
            SocketAddr::V6(addr) => {
                let sa6 = unsafe { &mut result.sa6 };

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
                {
                    sa6.sin6_len = std::mem::size_of::<sockaddr_in6>() as u8;
                }

                sa6.sin6_family = AF_INET6.try_into().unwrap();
                sa6.sin6_port = u16::to_be(addr.port());
                sa6.sin6_flowinfo = addr.flowinfo();

                let raw_ip = u128::to_be_bytes((*addr.ip()).into());
                #[cfg(not(target_os = "windows"))]
                {
                    sa6.sin6_addr.s6_addr = raw_ip;
                    sa6.sin6_scope_id = addr.scope_id();
                }
                #[cfg(target_os = "windows")]
                unsafe {
                    *sa6.sin6_addr.u.Byte_mut() = raw_ip;
                    *sa6.u.sin6_scope_id_mut() = addr.scope_id();
                }
            }
        }
        result
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

impl FromStr for OsSocketAddr {
    type Err = std::net::AddrParseError;
    fn from_str(val: &str) -> Result<Self,Self::Err> {
        let addr : SocketAddr = val.parse()?;
        Ok(addr.into())
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
    use libc::{in6_addr, in_addr, socklen_t};

    #[cfg(target_os = "windows")]
    use winapi::{
        shared::{in6addr::in6_addr, inaddr::in_addr},
        um::ws2tcpip::socklen_t,
    };

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
        assert_eq!(std::mem::size_of::<sockaddr_in6>(), osa.capacity());
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
    fn convert_from_and_to_raw() {
        let osa4 : OsSocketAddr = "12.34.56.78:12345".parse().unwrap();
        let osa6 : OsSocketAddr = "[0123:4567:89ab:cdef:fedc:ba98:7654:3210]:12345"
            .parse().unwrap();
        const LEN4 : usize = std::mem::size_of::<sockaddr_in>();
        const LEN6 : usize = std::mem::size_of::<sockaddr_in6>();

        fn with_buf<F>(len: usize, f: F)
            where F: Fn(&mut [u8], *mut sockaddr, *mut socklen_t)
        {
            let mut buf = Vec::new();
            buf.resize(len, 0xff);
            let sa = buf.as_mut_ptr() as *mut sockaddr;
            let mut sa_len = len as socklen_t;
            f(&mut buf, sa , &mut sa_len as *mut socklen_t);
        }
        // ipv4
        with_buf(128, |buf, sa, sa_len| unsafe {
            osa4.copy_to_raw(sa, sa_len).unwrap();

            assert_eq!(*sa_len as usize, LEN4);
            assert_eq!(&buf[..LEN4], osa4.as_ref());
            assert!(buf[LEN4..].iter().all(|v| *v==0xff));

            let mut osa4_bis = OsSocketAddr::copy_from_raw(sa, *sa_len);
            assert_eq!(osa4.into_addr(), osa4_bis.into_addr());
            assert_eq!(&osa4_bis.as_ref()[..LEN4], &buf[..LEN4]);
            assert!(osa4_bis.as_mut()[LEN4..].iter().all(|v| *v==0x0));

            let mut osa4_ter = OsSocketAddr::copy_from_raw(sa, 128);
            assert_eq!(osa4.into_addr(), osa4_ter.into_addr());
            assert_eq!(&osa4_ter.as_ref()[..LEN4], &buf[..LEN4]);
            assert!(osa4_ter.as_mut()[LEN4..].iter().all(|v| *v==0xff));
        });
        // ipv6
        with_buf(128, |buf, sa, sa_len| unsafe {
            osa6.copy_to_raw(sa, sa_len).unwrap();

            assert_eq!(*sa_len as usize, LEN6);
            assert_eq!(&buf[..LEN6], osa6.as_ref());
            assert!(buf[LEN6..].iter().all(|v| *v==0xff));

            let mut osa6_bis = OsSocketAddr::copy_from_raw(sa, *sa_len);
            assert_eq!(osa6.into_addr(), osa6_bis.into_addr());
            assert_eq!(osa6_bis.as_ref(), &buf[..LEN6]);
            assert_eq!(osa6_bis.as_mut(), &buf[..LEN6]);
        });
        // copy to smaller buffer (must truncate)
        with_buf(128, |buf, sa, sa_len| unsafe {
            let limit = 6;

            *sa_len = limit as socklen_t;
            osa4.copy_to_raw(sa, sa_len).unwrap();
            assert_eq!(*sa_len as usize, LEN4);
            assert_eq!(&buf[..limit], &osa4.as_ref()[..limit]);
            assert!(buf[limit..].iter().all(|v| *v==0xff));

            buf.fill(0xff);
            *sa_len = limit as socklen_t;
            osa6.copy_to_raw(sa, sa_len).unwrap();
            assert_eq!(*sa_len as usize, LEN6);
            assert_eq!(&buf[..limit], &osa6.as_ref()[..limit]);
            assert!(buf[limit..].iter().all(|v| *v==0xff));
        });
        // copy unknown sin_addr
        with_buf(128, |_, sa, sa_len| unsafe {
            assert_eq!(OsSocketAddr::new().copy_to_raw(sa, sa_len), Err(BadFamilyError(0)));
            assert_eq!(*sa_len, 0);
        });
        // null pointers
        unsafe { osa4.copy_to_raw(std::ptr::null_mut(), std::ptr::null_mut::<socklen_t>()).unwrap(); }

        let mut null = unsafe { OsSocketAddr::copy_from_raw(std::ptr::null(), 456) };
        assert_eq!(null.as_mut(), OsSocketAddr::new().as_mut());
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
            let mut osa = OsSocketAddr::copy_from_raw(
                &sa as *const _ as *const sockaddr,
                std::mem::size_of_val(&sa) as socklen_t,
            );
            assert_eq!(std::mem::size_of::<sockaddr_in>(),  osa.len());
            assert_eq!(std::mem::size_of::<sockaddr_in6>(), osa.capacity());
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

            let mut osa = OsSocketAddr::copy_from_raw(
                &sa as *const _ as *const sockaddr,
                std::mem::size_of_val(&sa) as socklen_t,
            );
            assert_eq!(std::mem::size_of::<sockaddr_in6>(), osa.len());
            assert_eq!(std::mem::size_of::<sockaddr_in6>(), osa.capacity());
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
                assert_eq!(0_isize, osa.len());
                assert_eq!(std::mem::size_of::<sockaddr_in6>(), osa.capacity());
            }
            check_as_mut(&mut osa);
        }

        check(OsSocketAddr::new());
        check(None.into());
        unsafe {
            check(OsSocketAddr::copy_from_raw(
                [0xde, 0xad, 0xbe, 0xef].as_ptr() as *const sockaddr,
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
