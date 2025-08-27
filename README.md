# sans-io-time

Represent time as an abstract absolute value based on an arbitrary start point
in a user-provided timeline.

## Why?

1. `no_std` environments may require an implementation of `Instant`.
2. Network protocols may require that time continues during suspend of the OS
   which is not something that is guaranteed by `std::time::Instant`.
3. Other uses of `std::time::Instant` should not count time during suspend e.g.
   CPU process time.

The `Instant`  type provided by this crate satisfies all of these constraints by
only specifying the carriage of data. It does not specify how the current time
is acquired or whether time continues during suspend. Both of these questions
are required to be answered (or left unspecified) by the caller by either using
`std::time::Instant` or `std::time::SystemTime` (with the "std" feature that is
enabled by default), or converting from another source of time like
[boot-time](https://crates.io/crates/boot-time).
