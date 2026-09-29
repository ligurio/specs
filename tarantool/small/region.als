// region.als -- model of the `region` allocator (small/region.c,
// include/small/region.h).
//
// A region is a list of slabs, newest first. Allocations append to the newest
// slab; all memory can only be freed at once (`region_free`) or rolled back to
// a previously recorded usage (`region_truncate`), which drops the newest
// slabs. A debug `reserved` flag guards the reserve/alloc protocol.
//
// LIMITATIONS:
//  - Three abstract slabs S0 (newest) / S1 / S2 (oldest) of equal size 4, in a
//    fixed order. Byte contents are abstract; only usage counters are modeled.
//  - `region_aligned_alloc` padding and `region_join` are not modeled.
//  - Callbacks (`on_alloc_cb`, `on_truncate_cb`) and the slab cache are
//    abstracted; `region_reserve_slow` allocating from the cache is modeled as
//    appending the next abstract slab.
//  - Bounded: Time=5, Int width 6. See ../README.md#model-limitations.
//
// C asserts covered: region.c:80,101 and region.h:218,239,248,273,290
// (the reserve/alloc protocol and the used/total accounting).

module region

open util/ordering[Time]
open util/integer
open common

sig Time {}

abstract sig Slab {
	nxt: lone Slab,
	size: one Int,
	used: Time -> one Int
}
one sig S0, S1, S2 extends Slab {}

one sig Region {
	head: Time -> lone Slab,
	present: Time -> set Slab,
	statsUsed: Time -> one Int,
	statsTotal: Time -> one Int,
	reserved: Time -> one Int
}

fact geometry {
	S0.size = 4 and S1.size = 4 and S2.size = 4
	S0.nxt = S1 and S1.nxt = S2 and no S2.nxt
	Region.reserved[first] = 0
}

/** Usage of `s` counted only while it is present. */
fun usedOn[t: Time, s: Slab]: Int { s in Region.present[t] => s.used[t] else 0 }
/** Size of `s` counted only while it is present. */
fun sizeOn[t: Time, s: Slab]: Int { s in Region.present[t] => s.size else 0 }

fun sumUsed[t: Time]: Int {
	plus[plus[usedOn[t, S0], usedOn[t, S1]], usedOn[t, S2]]
}
fun sumSize[t: Time]: Int {
	plus[plus[sizeOn[t, S0], sizeOn[t, S1]], sizeOn[t, S2]]
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

pred init[t: Time] {
	no Region.present[t]
	no Region.head[t]
	Region.statsUsed[t] = 0
	Region.statsTotal[t] = 0
	Region.reserved[t] = 0
	all s: Slab | s.used[t] = 0
}

/** region_reserve(): fast path, there is room in the head slab. */
pred reserveFast[t, t1: Time] {
	Region.reserved[t] = 0
	some Region.head[t]
	Region.present[t1] = Region.present[t]
	Region.head[t1] = Region.head[t]
	Region.statsUsed[t1] = Region.statsUsed[t]
	Region.statsTotal[t1] = Region.statsTotal[t]
	Region.reserved[t1] = 1
	all s: Slab | s.used[t1] = s.used[t]
}

/** region_reserve_slow(): prepend a new slab and reserve in it. */
pred reserveSlow[t, t1: Time] {
	Region.reserved[t] = 0
	some s: Slab - Region.present[t] {
		s.nxt = Region.head[t]
		Region.present[t1] = Region.present[t] + s
		Region.head[t1] = s
		Region.statsUsed[t1] = Region.statsUsed[t]
		Region.statsTotal[t1] = plus[Region.statsTotal[t], s.size]
		Region.reserved[t1] = 1
		s.used[t1] = 0
		all o: Slab - s | o.used[t1] = o.used[t]
	}
}

pred reserve[t, t1: Time] { reserveFast[t, t1] or reserveSlow[t, t1] }

/** region_alloc(): commit `n` bytes in the head slab. */
pred alloc[t, t1: Time, n: Int] {
	Region.reserved[t] = 1
	n >= 0
	some h: Region.head[t] {
		n <= minus[h.size, h.used[t]]
		Region.present[t1] = Region.present[t]
		Region.head[t1] = h
		Region.statsUsed[t1] = plus[Region.statsUsed[t], n]
		Region.statsTotal[t1] = Region.statsTotal[t]
		Region.reserved[t1] = 0
		h.used[t1] = plus[h.used[t], n]
		all o: Slab - h | o.used[t1] = o.used[t]
	}
}

/** region_truncate(): drop the newest slabs down to the requested usage. */
pred truncate[t, t1: Time, n: Int] {
	n >= 0 and n <= Region.statsUsed[t]
	some h: Region.present[t] {
		Region.head[t1] = h
		Region.present[t1] = h.*nxt
		// Slabs older than h stay full; h may be partially used.
		all o: Region.present[t1] - h | o.used[t1] = o.used[t]
		h.used[t1] >= 0 and h.used[t1] <= h.size
		Region.statsUsed[t1] = n
		n = sumUsed[t1]
		Region.statsTotal[t1] = sumSize[t1]
		Region.reserved[t1] = 0
		all o: Slab - Region.present[t1] | o.used[t1] = o.used[t]
	}
}

/** region_free(): drop everything. */
pred free[t, t1: Time] {
	no Region.present[t1]
	no Region.head[t1]
	Region.statsUsed[t1] = 0
	Region.statsTotal[t1] = 0
	Region.reserved[t1] = 0
	all s: Slab | s.used[t1] = 0
}

/** region_reset(): keep the slabs, zero the usage. */
pred reset[t, t1: Time] {
	Region.present[t1] = Region.present[t]
	Region.head[t1] = Region.head[t]
	Region.statsTotal[t1] = Region.statsTotal[t]
	Region.reserved[t1] = 0
	some Region.head[t] and Region.head[t].used[t1] = 0
	Region.statsUsed[t1] = minus[Region.statsUsed[t], Region.head[t].used[t]]
	all o: Slab - Region.head[t] | o.used[t1] = o.used[t]
}

pred stutter[t, t1: Time] {
	Region.present[t1] = Region.present[t]
	Region.head[t1] = Region.head[t]
	Region.statsUsed[t1] = Region.statsUsed[t]
	Region.statsTotal[t1] = Region.statsTotal[t]
	Region.reserved[t1] = Region.reserved[t]
	all s: Slab | s.used[t1] = s.used[t]
}

pred step[t, t1: Time] {
	reserve[t, t1] or (some n: Int | alloc[t, t1, n]) or
	(some n: Int | truncate[t, t1, n]) or free[t, t1] or reset[t, t1] or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

pred inv[t: Time] {
	isLinearFrom[nxt, Region.head[t], Region.present[t]]
	Region.statsUsed[t] = sumUsed[t]
	Region.statsTotal[t] = sumSize[t]
	Region.reserved[t] in 0 + 1
	all s: Region.present[t] | s.used[t] >= 0 and s.used[t] <= s.size
}

check inv_linear {
	all t: Time | isLinearFrom[nxt, Region.head[t], Region.present[t]]
} for 5 but 6 int
check inv_used_sum {
	all t: Time | Region.statsUsed[t] = sumUsed[t]
} for 5 but 6 int
check inv_total_sum {
	all t: Time | Region.statsTotal[t] = sumSize[t]
} for 5 but 6 int
check inv_reserved {
	all t: Time | Region.reserved[t] in 0 + 1
} for 5 but 6 int
check inv_used_bounds {
	all t: Time, s: Region.present[t] | s.used[t] >= 0 and s.used[t] <= s.size
} for 5 but 6 int
/** The usage counters always match the slab usages. */
check safety {
	all t: Time | inv[t]
} for 5 but 6 int

/** Truncate never increases usage and keeps the retained prefix byte-exact. */
check truncate_accounting {
	all t: Time - last, n: Int |
		truncate[t, next[t], n] implies
			(Region.statsUsed[next[t]] = n and n <= Region.statsUsed[t])
} for 5 but 6 int

/** An allocation is only allowed right after a reservation. */
check alloc_needs_reserve {
	all t: Time - last, n: Int |
		alloc[t, next[t], n] implies Region.reserved[t] = 1
} for 5 but 6 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Reserve, allocate, then truncate back to a previous usage. */
run alloc_then_truncate {
	some t1: Time, n1, n2: Int |
		reserve[t1, next[t1]] and alloc[next[t1], next[next[t1]], n1] and
		truncate[next[next[t1]], next[next[next[t1]]], n2] and
		n2 <= n1
} for 5 but 6 int

/** Appending beyond the first slab opens a second one. */
run slow_reserve_opens_slab {
	some t: Time |
		reserveSlow[t, next[t]] and
		#Region.present[next[t]] = 1
} for 4 but 6 int

/** Full region trace: reserve a slab, allocate, truncate, then free. */
run region_lifecycle {
	reserveSlow[first, next[first]] and
	alloc[next[first], next[next[first]], 2] and
	truncate[next[next[first]], next[next[next[first]]], 0] and
	free[next[next[next[first]]], last]
} for 5 but 6 int

/** Committing bytes never adds, drops or reorders slabs. */
run alloc_keeps_head {
	some t: Time, n: Int |
		alloc[t, next[t], n] and
		Region.present[next[t]] = Region.present[t] and
		Region.head[next[t]] = Region.head[t] and
		Region.statsTotal[next[t]] = Region.statsTotal[t]
} for 5 but 6 int
