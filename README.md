# os_socketaddr

[![Build Status](https://travis-ci.org/a-ba/os_socketaddr.svg?branch=master)](https://travis-ci.org/a-ba/os_socketaddr)
[![Crates.io](https://img.shields.io/crates/v/os_socketaddr.svg)](https://crates.io/crates/os_socketaddr)

This crate provides a type that can act as a platform-native socket address
(i.e. `libc::sockaddr`)

## Motivation

The std crate provides `std::net::SocketAddr` for managing socket addresses. Its `V4` variant
encapsulates a `libc::sockaddr_in` and its `V6` variant encapsulates a `libc::sockaddr_in6`.
However there is no easy way to convert `SocketAddr` from/into a `libc::sockaddr`, because
`SocketAddr` is a rust enum.

This crate provides `OsSocketAddr` which holds a `libc::sockaddr` (containing an IPv4 or IPv6
address) and the conversion functions from/into `std::net::SocketAddr`.
