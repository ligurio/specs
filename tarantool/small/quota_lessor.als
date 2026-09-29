// quota_lessor.als -- model of the per-thread quota lessor
// (include/small/quota_lessor.h).
//
// A lessor takes memory from a shared `quota` source and leases it to users in
// chunks of at least `QUOTA_USE_MIN`, tracking `used` (taken from the source)
// and `leased` (handed out). The core invariant is `used >= leased`; when the
// slack exceeds two minimum chunks, `quota_end_lease` returns some of it to the
// source to avoid oscillation.
//
// LIMITATIONS:
//  - The source `quota` is abstracted to "a lease always succeeds"; the shared
//    quota's own limit and atomicity (see quota.als) are not modeled.
//  - Units are abstract small integers; `QUOTA_USE_MIN = 2` and the hysteresis
//    threshold of two minimum chunks are scaled down. The exact 1 KiB / 1 MiB
//    sizes and the `use /= 2` retry loop are not modeled.
//  - Bounded: Time=5, Int width 5. See ../README.md#model-limitations.
//
// C asserts covered: quota_lessor.h:93,105,150.

module quota_lessor

open util/ordering[Time]
open util/integer

sig Time {}

one sig Lessor {
	used: Time -> one Int,
	leased: Time -> one Int
}

fun minUse: Int { 2 }

pred init[t: Time] {
	Lessor.used[t] = 0
	Lessor.leased[t] = 0
}

/** quota_lease(): hand out `size`, taking a chunk from the source if needed. */
pred lease[t, t1: Time, size: Int, ret: Int] {
	size > 0 and size <= 3
	(
		// Enough slack already: take nothing new.
		(plus[Lessor.leased[t], size] <= Lessor.used[t] and
		 Lessor.used[t1] = Lessor.used[t] and ret = size)
		or
		// Take a chunk of at least `minUse` (which must cover the shortfall).
		(plus[Lessor.leased[t], size] > Lessor.used[t] and
		 Lessor.used[t1] >= plus[Lessor.leased[t], size] and
		 Lessor.used[t1] >= plus[Lessor.used[t], minUse] and
		 ret = size)
	)
	Lessor.leased[t1] = plus[Lessor.leased[t], size]
}

/** quota_end_lease(): return `size` to the lessor, maybe release slack. */
pred endLease[t, t1: Time, size: Int] {
	size > 0 and size <= 3 and size <= Lessor.leased[t]
	Lessor.leased[t1] = minus[Lessor.leased[t], size]
	// Release slack only above two minimum chunks (hysteresis); `used`
	// never drops below `leased`.
	(
		(minus[Lessor.used[t], Lessor.leased[t1]] >
			mul[2, minUse] and
		 Lessor.used[t1] = Lessor.leased[t1] and
		 Lessor.used[t1] <= Lessor.used[t])
		or
		(Lessor.used[t1] = Lessor.used[t])
	)
}

pred stutter[t, t1: Time] {
	Lessor.used[t1] = Lessor.used[t]
	Lessor.leased[t1] = Lessor.leased[t]
}

pred step[t, t1: Time] {
	(some s, r: Int | lease[t, t1, s, r]) or
	(some s: Int | endLease[t, t1, s]) or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

pred inv[t: Time] {
	Lessor.used[t] >= Lessor.leased[t]
	Lessor.leased[t] >= 0
}

check safety { all t: Time | inv[t] } for 4 but 5 int

/** The lessor never hands out more than it has taken from the source. */
check used_covers_leased {
	all t: Time | Lessor.used[t] >= Lessor.leased[t]
} for 4 but 5 int

/** Every lease is at least the minimum chunk when the slack is insufficient. */
check lease_takes_min {
	all t: Time - last, s, r: Int |
		lease[t, next[t], s, r] and plus[Lessor.leased[t], s] > Lessor.used[t]
			implies Lessor.used[next[t]] >= plus[Lessor.used[t], minUse]
} for 4 but 5 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Lease, then end the lease. */
run lease_then_end {
	some t: Time, s: Int |
		lease[t, next[t], s, s] and endLease[next[t], next[next[t]], s]
} for 4 but 5 int

/** The slack built up by an over-lease is returned to the source once. */
run release_slack {
	some t: Time, s: Int |
		lease[t, next[t], s, s] and
		endLease[next[t], next[next[t]], s] and
		Lessor.used[next[next[t]]] < Lessor.used[next[t]]
} for 4 but 5 int

/** Full lessor trace: lease, end the lease, then lease again from the slack. */
run lease_end_release {
	lease[first, next[first], 3, 3] and
	endLease[next[first], next[next[first]], 3] and
	lease[next[next[first]], last, 2, 2]
} for 4 but 5 int

/** Ending a lease that left little slack does not return memory. */
run end_lease_keeps_used {
	lease[first, next[first], 3, 3] and
	endLease[next[first], last, 3] and
	Lessor.used[last] = Lessor.used[next[first]]
} for 3 but 5 int
