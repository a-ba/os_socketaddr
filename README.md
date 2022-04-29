# os_socketaddr

[![Crates.io][crates-badge]][crates-url]
[![Build Status][actions-badge]][actions-url]

[crates-badge]:  https://img.shields.io/crates/v/os_socketaddr.svg
[crates-url]:    https://crates.io/crates/os_socketaddr
[actions-badge]: https://github.com/a-ba/os_socketaddr/workflows/CI/badge.svg?branch=master
[actions-url]:   https://github.com/a-ba/os_socketaddr/actions?query=workflow%3ACI+branch%3Amaster


This crate provides a type that can act as a platform-native socket address
(i.e. `libc::sockaddr`)

## Motivation

The std crate provides `SocketAddr` for managing socket addresses. Its `V4` variant
encapsulates `libc::sockaddr_in` and its `V6` variant encapsulates `libc::sockaddr_in6`.
However there is no easy way to convert `SocketAddr` from/into a `libc::sockaddr` because
`SocketAddr` is a rust enum.

This crate provides `OsSocketAddr` which holds a `libc::sockaddr` (containing an IPv4 or IPv6
address) and the conversion functions from/into `SocketAddr`.

## Example

```rust
extern crate libc;
extern crate os_socketaddr;

use std::net::SocketAddr;
use libc::{c_int, c_void, size_t, ssize_t};
use os_socketaddr::OsSocketAddr;

fn sendto(socket: c_int, buf: &[u8], dst: SocketAddr) -> ssize_t
{
    let addr : OsSocketAddr = dst.into();
    unsafe {
        libc::sendto(socket, buf.as_ptr() as *const c_void, buf.len() as size_t, 0,
                     addr.as_ptr(), addr.len())
    }
}

fn recvfrom(socket: c_int, buf: &mut[u8]) -> (ssize_t, Option<SocketAddr>)
{
    let mut addr = OsSocketAddr::new();
    let mut addrlen = addr.capacity();
    let nb = unsafe {
        libc::recvfrom(socket, buf.as_mut_ptr() as *mut c_void, buf.len(), 0,
                       addr.as_mut_ptr(), &mut addrlen as *mut _)
    };
    (nb, addr.into())
}
```
