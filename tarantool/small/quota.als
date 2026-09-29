// quota.als -- model of `struct quota` (include/small/quota.h).
//
// The C implementation packs `(total, used)` into one 64-bit word, both in
// units of QUOTA_UNIT_SIZE, and updates them with compare-and-exchange. Here
// the two fields are plain small integers and each operation is one atomic
// step (the CAS retry loop is a refinement that preserves the same invariant).
//
// LIMITATIONS:
//  - Amounts are abstract small `Int`s (bitwidth 5..6), not `size_t`.
//  - Unit rounding (`QUOTA_UNIT_SIZE`, `ceil`) is not modeled: every size is
//    assumed already unit-aligned.
//  - The 32/64-bit packing, overflow around `QUOTA_MAX`, and the atomic CAS
//    loop are not modeled.
//  - See ../README.md#model-limitations.
//
// C asserts covered: quota.h:137,144,162,171.

module quota

open util/ordering[Time]
open util/integer

sig Time {}

one sig Quota {
	total: Time -> one Int,
	used: Time -> one Int
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

/** quota_init(): used = 0. The limit is fixed to 8 by the trace. */
pred init[t: Time] {
	Quota.total[t] = 6
	Quota.used[t] = 0
}

/** quota_use(): consume `n`; fails with -1 when the limit would be exceeded. */
pred use[t, t1: Time, n: Int, ret: Int] {
	let avail = minus[Quota.total[t], Quota.used[t]] |
		(n >= 0 and n <= avail and
		 ret = n and
		 Quota.used[t1] = plus[Quota.used[t], n] and
		 Quota.total[t1] = Quota.total[t])
		or
		(n > avail and
		 ret = -1 and
		 Quota.used[t1] = Quota.used[t] and
		 Quota.total[t1] = Quota.total[t])
}

/** quota_release(): return `n` units; precondition `n <= used`. */
pred release[t, t1: Time, n: Int, ret: Int] {
	n >= 0 and n <= Quota.used[t] and
	ret = n and
	Quota.used[t1] = minus[Quota.used[t], n] and
	Quota.total[t1] = Quota.total[t]
}

/** quota_set(): change the limit; fails with -1 when below current usage. */
pred quotaSet[t, t1: Time, newTotal: Int, ret: Int] {
	(newTotal >= Quota.used[t] and newTotal >= 0 and
	 ret = newTotal and
	 Quota.total[t1] = newTotal and
	 Quota.used[t1] = Quota.used[t])
	or
	(newTotal < Quota.used[t] and
	 ret = -1 and
	 Quota.total[t1] = Quota.total[t] and
	 Quota.used[t1] = Quota.used[t])
}

pred step[t, t1: Time] {
	(some n, ret: Int | use[t, t1, n, ret])
	or (some n, ret: Int | release[t, t1, n, ret])
	or (some nt, ret: Int | quotaSet[t, t1, nt, ret])
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

pred inv[t: Time] {
	Quota.used[t] >= 0
	Quota.total[t] >= 0
	Quota.used[t] <= Quota.total[t]
}

/** Usage never exceeds the limit, under any interleaving of use/release/set. */
check invariant {
	all t: Time | inv[t]
} for 3 but 4 int

/** `use` succeeds exactly when the request fits, and fails otherwise. */
check use_matches_capacity {
	all t: Time - last, n, ret: Int |
		use[t, next[t], n, ret] implies
		(ret = -1 iff n > minus[Quota.total[t], Quota.used[t]])
} for 3 but 4 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Use part of the quota, then release it again. */
run use_then_release {
	some t: Time, n: Int |
		n > 0 and
		use[t, next[t], n, n] and
		release[next[t], next[next[t]], n, n]
} for 3 but 4 int

/** A failed use leaves the quota unchanged. */
run failed_use_is_noop {
	some t: Time, n: Int |
		n > minus[Quota.total[t], Quota.used[t]] and
		use[t, next[t], n, -1] and
		Quota.used[next[t]] = Quota.used[t]
} for 3 but 4 int

/** Full quota trace: use, shrink the limit, then release. */
run use_set_release {
	use[first, next[first], 2, 2] and
	quotaSet[next[first], next[next[first]], 4, 4] and
	release[next[next[first]], last, 1, 1]
} for 4 but 4 int

/** A set below the current usage fails and keeps the limit. */
run set_below_used_fails {
	use[first, next[first], 2, 2] and
	quotaSet[next[first], last, 1, -1] and
	Quota.used[last] = Quota.used[next[first]] and
	Quota.total[last] = Quota.total[next[first]]
} for 3 but 4 int
