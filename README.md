# os_socketaddr

[![Crates.io][crates-badge]][crates-url]
![License: Mit or Apache 2.0](https://img.shields.io/badge/license-MIT_or_Apache_2.0-blue.svg)
[![Build Status][actions-badge]][actions-url]

[crates-badge]:  https://img.shields.io/crates/v/os_socketaddr.svg
[crates-url]:    https://crates.io/crates/os_socketaddr
[actions-badge]: https://github.com/a-ba/os_socketaddr/workflows/CI/badge.svg?branch=master
[actions-url]:   https://github.com/a-ba/os_socketaddr/actions?query=workflow%3ACI+branch%3Amaster


This crate provides a type that can act as a platform-native socket address
(i.e. `libc::sockaddr`)

## Motivation

The std crate provides `SocketAddr` for managing socket addresses. However there is no easy way to
convert `SocketAddr` from/into a `libc::sockaddr` because `SocketAddr` has a different internal
layout.

This crate provides `OsSocketAddr` which holds a `libc::sockaddr` (containing an IPv4 or IPv6
address) and the conversion functions:

  - from/into `SocketAddr`
  - from `(*const sockaddr, SockLen)`
  - into `(*mut sockaddr, *mut Socklen)`

where `SockLen` may be any of `i32`, `u32`, `i64`, `u64`, `isize` or `usize`.

## Supported targets   `#[cfg(target_os="xxxxxx")]`

`linux`, `macos` and `windows` are officially supported and
[actively tested](https://github.com/a-ba/os_socketaddr/actions).

`android`, `dragonfly`, `emscripten`, `freebsd`, `fuchsia`, `haiku`, `hermit`, `illumos`, `ios`,
`l4re`, `netbsd`, `openbsd`, `redox`, `solaris`, `vxworks` and `watchos` should work but are not
tested.

## Example

```rust
extern crate libc;
extern crate os_socketaddr;

use std::net::SocketAddr;
use libc::{c_int, c_void, size_t, ssize_t};
use os_socketaddr::OsSocketAddr;

fn sendto(socket: c_int, payload: &[u8], dst: SocketAddr) -> ssize_t
{
    let addr : OsSocketAddr = dst.into();
    unsafe {
        libc::sendto(socket, payload.as_ptr() as *const c_void, payload.len() as size_t, 0,
                     addr.as_ptr(), addr.len())
    }
}

fn recvfrom(socket: c_int, payload: &mut[u8]) -> (ssize_t, Option<SocketAddr>)
{
    let mut addr = OsSocketAddr::new();
    let mut addrlen = addr.capacity();
    let nb = unsafe {
        libc::recvfrom(socket, payload.as_mut_ptr() as *mut c_void, payload.len(), 0,
                       addr.as_mut_ptr(), &mut addrlen as *mut _)
    };
    (nb, addr.into())
}
```
