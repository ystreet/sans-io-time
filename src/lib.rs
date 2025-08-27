// Copyright (C) 2025 Matthew Waters <matthew@centricular.com>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![no_std]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

//! # sans-io-time
//!
//! Represent time as an abstract absolute value based on an arbitrary start point in a
//! (user-provided) timeline.
//!
//! ## Why?
//!
//! 1. `no_std` environments may require an implementation of `Instant` and may require
//!    leaving the implementation details to the implementor.
//! 2. Network protocols may require that time continues during suspend of the OS
//!    which is not something that is guaranteed by `std::time::Instant`.
//! 3. Other uses of `std::time::Instant` should not count time during suspend e.g.
//!    CPU process time, or process uptime.
//!
//! The `Instant`  type provided by this crate satisfies all of these constraints by
//! only specifying the carriage of data. It does not specify how the current time
//! is acquired or whether time continues during suspend. Both of these questions
//! are required to be answered (or left unspecified) by the caller by either using
//! `std::time::Instant` or `std::time::SystemTime` (with the "std" feature), or
//! converting from another source of time like
//! [boot-time](https://crates.io/crates/boot-time).
//!
//! In a sans-IO library, the decision on the exact clock source can be decided by the
//! user of the library rather than specifying a particular `Instant` implementation.
//!
//! ## Features
//! - "std" (enabled by default) enables conversion from `std::time::Instant` and
//!   `std::time::SystemTime` into an [`Instant`].

#[cfg(feature = "std")]
extern crate std;

use core::time::Duration;

/// An absolute point in time.
///
/// An [`Instant`] is a wrapper around a signed integer that holds the number of nanoseconds since
/// an arbitrary point in time, e.g. system startup.
///
/// - A value of `0` is arbitrary.
/// - Values < 0 indicate a time before the start point.
#[derive(Debug, Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct Instant {
    nanos: i64,
}

impl Instant {
    /// The zero [`Instant`].
    ///
    /// An arbitrary point on the absolute timescale.
    pub const ZERO: Instant = Instant { nanos: 0 };

    /// Construct an [`Instant`] from a number of nanoseconds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use sans_io_time::Instant;
    /// let instant = Instant::from_nanos(1_234_567_890);
    /// assert_eq!(instant.as_nanos(), 1_234_567_890);
    /// ```
    pub fn from_nanos(nanos: i64) -> Self {
        Self { nanos }
    }

    /// The number of nanoseconds that have passed since the `ZERO` point.
    pub const fn as_nanos(&self) -> i64 {
        self.nanos
    }

    /// The number of whole seconds since the `ZERO` point.
    pub const fn secs(&self) -> i64 {
        self.nanos / 1_000_000_000
    }

    /// The number of fractional nanoseconds since the `ZERO` point.
    pub const fn subsec_nanos(&self) -> i64 {
        self.nanos % 1_000_000_000
    }

    /// The amount of time elapsed since an earlier [`Instant`], or `0`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use sans_io_time::Instant;
    /// # use core::time::Duration;
    /// let earlier = Instant::from_nanos(1_234_567_890);
    /// let later = Instant::from_nanos(2_234_567_890);
    /// assert_eq!(later.duration_since(earlier), Duration::from_nanos(1_000_000_000));
    /// assert_eq!(earlier.duration_since(later), Duration::ZERO);
    /// assert_eq!(earlier.duration_since(earlier), Duration::ZERO);
    /// ```
    pub fn duration_since(&self, earlier: Instant) -> Duration {
        self.saturating_duration_since(earlier)
    }

    /// The amount of time elapsed since an earlier [`Instant`], or `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use sans_io_time::Instant;
    /// # use core::time::Duration;
    /// let earlier = Instant::from_nanos(1_234_567_890);
    /// let later = Instant::from_nanos(2_234_567_890);
    /// assert_eq!(later.checked_duration_since(earlier), Some(Duration::from_nanos(1_000_000_000)));
    /// assert_eq!(earlier.checked_duration_since(later), None);
    /// assert_eq!(earlier.checked_duration_since(earlier), Some(Duration::ZERO));
    /// ```
    pub fn checked_duration_since(&self, earlier: Instant) -> Option<Duration> {
        self.nanos.checked_sub(earlier.nanos).and_then(|nanos| {
            if nanos < 0 {
                None
            } else {
                Some(Duration::from_nanos(nanos as u64))
            }
        })
    }

    /// The amount of time elapsed since an earlier [`Instant`], or `0`.
    pub fn saturating_duration_since(&self, earlier: Instant) -> Duration {
        self.checked_duration_since(earlier)
            .unwrap_or(Duration::ZERO)
    }

    /// Returns the result of `self + duration` if the result can be represented by the underlying
    /// data structure, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use sans_io_time::Instant;
    /// # use core::time::Duration;
    /// let instant = Instant::from_nanos(1_234_567_890);
    /// assert_eq!(instant.checked_add(Duration::from_secs(1)), Some(Instant::from_nanos(2_234_567_890)));
    /// assert_eq!(instant.checked_add(Duration::ZERO), Some(instant));
    /// ```
    pub fn checked_add(&self, duration: Duration) -> Option<Instant> {
        let dur_nanos: i64 = duration.as_nanos().try_into().ok()?;
        let nanos = self.nanos.checked_add(dur_nanos)?;
        Some(Self { nanos })
    }

    /// Returns the result of `self - duration` if the result can be represented by the underlying
    /// data structure, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use sans_io_time::Instant;
    /// # use core::time::Duration;
    /// let instant = Instant::from_nanos(1_234_567_890);
    /// assert_eq!(instant.checked_sub(Duration::from_secs(1)), Some(Instant::from_nanos(234_567_890)));
    /// assert_eq!(instant.checked_sub(Duration::from_secs(2)), Some(Instant::from_nanos(-765_432_110)));
    /// assert_eq!(instant.checked_sub(Duration::ZERO), Some(instant));
    /// ```
    pub fn checked_sub(&self, duration: Duration) -> Option<Instant> {
        let dur_nanos: i64 = duration.as_nanos().try_into().ok()?;
        let nanos = self.nanos.checked_sub(dur_nanos)?;
        Some(Self { nanos })
    }

    /// Construct an [`Instant`] from a `std::time::Instant` based its the elapsed time.
    ///
    /// Can be used if you have a base `std::time::Instant` where you can create [`Instant`]s as
    /// needed.
    ///
    /// # Example
    ///
    /// ```
    /// # use sans_io_time::Instant;
    /// # use core::time::Duration;
    /// let std_instant = std::time::Instant::now();
    /// std::thread::sleep(Duration::from_secs(1));
    /// assert!(Instant::from_std(std_instant) >= Instant::from_nanos(1_000_000_000));
    /// ```
    #[cfg(feature = "std")]
    pub fn from_std(instant: ::std::time::Instant) -> Self {
        let elapsed = instant.elapsed();
        Self {
            nanos: elapsed
                .as_nanos()
                .try_into()
                .expect("Elapsed time too large to fit into Instant"),
        }
    }

    /// Construct an [`Instant`] from a `std::time::System` based on the distance from the unix
    /// epoch.
    ///
    /// # Example
    ///
    /// ```
    /// # use sans_io_time::Instant;
    /// # use core::time::Duration;
    /// let std_instant = std::time::Instant::now();
    /// std::thread::sleep(Duration::from_secs(1));
    /// assert!(Instant::from_std(std_instant) >= Instant::from_nanos(1_000_000_000));
    /// ```
    #[cfg(feature = "std")]
    pub fn from_system(sys_time: ::std::time::SystemTime) -> Self {
        let dur = sys_time
            .duration_since(::std::time::UNIX_EPOCH)
            .expect("start time must not be before the unix epoch");
        Self {
            nanos: dur
                .as_nanos()
                .try_into()
                .expect("Elapsed time too large to fit into Instant"),
        }
    }
}

impl core::fmt::Display for Instant {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let secs = self.secs();
        let nanos = self.subsec_nanos();
        if secs != 0 {
            write!(f, "{}", secs)?;
            if nanos != 0 {
                write!(f, ".{:0>9}", nanos.abs())?;
            }
            write!(f, "s")
        } else if nanos != 0 {
            if nanos < 0 {
                write!(f, "-")?;
            }
            let millis = nanos.abs() / 1_000_000;
            let millis_rem = nanos.abs() % 1_000_000;
            write!(f, "{}.{:0>6}ms", millis, millis_rem)
        } else {
            write!(f, "0s")
        }
    }
}

impl core::ops::Add<Duration> for Instant {
    type Output = Instant;
    fn add(self, rhs: Duration) -> Self::Output {
        self.checked_add(rhs)
            .expect("Duration too large to fit into Instant")
    }
}

impl core::ops::AddAssign<Duration> for Instant {
    fn add_assign(&mut self, rhs: Duration) {
        *self = self
            .checked_add(rhs)
            .expect("Duration too large to fit into Instant");
    }
}

impl core::ops::Sub<Duration> for Instant {
    type Output = Instant;
    fn sub(self, rhs: Duration) -> Self::Output {
        self.checked_sub(rhs)
            .expect("Duration too large to fit into Instant")
    }
}

impl core::ops::SubAssign<Duration> for Instant {
    fn sub_assign(&mut self, rhs: Duration) {
        *self = self
            .checked_sub(rhs)
            .expect("Duration too large to fit into Instant")
    }
}

impl core::ops::Sub<Instant> for Instant {
    type Output = Duration;
    fn sub(self, rhs: Instant) -> Self::Output {
        self.saturating_duration_since(rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    extern crate alloc;

    #[test]
    fn add() {
        let base = Instant::from_nanos(1_222_333_444);
        assert_eq!(
            base + Duration::from_secs(1),
            Instant::from_nanos(2_222_333_444)
        );
        let mut new = base;
        new += Duration::from_secs(1);
        assert_eq!(new, Instant::from_nanos(2_222_333_444));
    }

    #[test]
    fn sub_duration() {
        let base = Instant::from_nanos(1_222_333_444);
        assert_eq!(
            base - Duration::from_secs(1),
            Instant::from_nanos(222_333_444)
        );
        let mut new = base;
        new -= Duration::from_secs(1);
        assert_eq!(new, Instant::from_nanos(222_333_444));
    }

    #[test]
    fn sub_instant() {
        let earlier = Instant::from_nanos(1_222_333_444);
        let later = Instant::from_nanos(2_333_444_555);
        assert_eq!(later - earlier, Duration::from_nanos(1_111_111_111));
        assert_eq!(earlier - later, Duration::ZERO);
        assert_eq!(earlier - earlier, Duration::ZERO);
    }

    #[test]
    fn display() {
        assert_eq!(&alloc::format!("{}", Instant::ZERO), "0s");
        assert_eq!(&alloc::format!("{}", Instant::from_nanos(1)), "0.000001ms");
        assert_eq!(
            &alloc::format!("{}", Instant::from_nanos(-1)),
            "-0.000001ms"
        );
        assert_eq!(
            &alloc::format!("{}", Instant::from_nanos(1_000_000_000)),
            "1s"
        );
        assert_eq!(
            &alloc::format!("{}", Instant::from_nanos(1_000_000_001)),
            "1.000000001s"
        );
        assert_eq!(
            &alloc::format!("{}", Instant::from_nanos(1_100_000_000)),
            "1.100000000s"
        );
        assert_eq!(
            &alloc::format!("{}", Instant::from_nanos(-1_000_000_000)),
            "-1s"
        );
        assert_eq!(
            &alloc::format!("{}", Instant::from_nanos(-1_000_000_001)),
            "-1.000000001s"
        );
        assert_eq!(
            &alloc::format!("{}", Instant::from_nanos(-1_100_000_000)),
            "-1.100000000s"
        );
    }
}
