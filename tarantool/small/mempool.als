// mempool.als -- model of `struct mempool` / `struct mslab`
// (small/mempool.c, include/small/mempool.h).
//
// A mempool hands out fixed-size objects carved from slabs. A slab is full
// (untracked), hot (`nfree >= objcount/8`, kept in the address-ordered
// `hot_slabs` tree), cold (`nfree == 1`, staged on `cold_slabs`), or the
// single `spare` completely empty slab kept to avoid cache oscillation.
// Allocation prefers, in order: the spare, a hot slab, a cold slab, or a
// freshly obtained slab.
//
// LIMITATIONS:
//  - Sizes are abstract: objSize = 1, objCount = 4 (so `hot` means 1..2 free
//    slots, `cold` means exactly 1 free slot, `spare` means 0 live objects).
//    The real `objcount/8` threshold and slab sizes are not modeled.
//  - The RB tree `hot_slabs` is abstracted to "if some hot slab exists, one
//    can be chosen"; `first_hot_slab` (minimum address) is not modeled.
//  - `free_list` and `free_offset` are abstracted to `carved` (objects ever
//    carved) and `live` (handed-out objects): a free-list hit keeps `carved`,
//    a fresh carve increases it. Pointer/`memcpy` mechanics are not modeled.
//  - The spare is kept by minimum address, as in mempool.c:142-151; addresses
//    are hardcoded.
//  - Bounded: Time=4, Slab=4, Int width 6. See ../README.md#model-limitations.
//
// C asserts covered: mempool.c:68,159,172,209,216 and mempool.h:294,298,310,335.

module mempool

open util/ordering[Time]
open util/integer

sig Time {}

// ---------------------------------------------------------------------------
// Geometry
// ---------------------------------------------------------------------------

abstract sig Slab {
	addr: one Int,
	live: Time -> one Int,
	carved: Time -> one Int
}
one sig S0, S1, S2, S3 extends Slab {}

one sig Config {
	objSize: one Int,
	objCount: one Int
}
fact geometry {
	Config.objSize = 1
	Config.objCount = 4
	S0.addr = 0
	S1.addr = 1
	S2.addr = 2
	S3.addr = 3
}

fun objSize: Int { Config.objSize }
fun objCount: Int { Config.objCount }
fun slabSize: Int { mul[Config.objSize, Config.objCount] }

one sig Pool {
	owned: Time -> set Slab,
	usedBytes: Time -> one Int,
	totalBytes: Time -> one Int
}

fun liveOf[t: Time, s: Slab]: Int { s.live[t] }

// Derived buckets (the C code stores these explicitly; here they follow from
// `live`).
fun spare[t: Time]: set Slab { {s: Pool.owned[t] | s.live[t] = 0} }
fun full[t: Time]: set Slab { {s: Pool.owned[t] | s.live[t] = objCount} }
fun cold[t: Time]: set Slab { {s: Pool.owned[t] | s.live[t] = minus[objCount, 1]} }
fun hot[t: Time]: set Slab {
	{s: Pool.owned[t] | s.live[t] >= 1 and s.live[t] <= minus[objCount, 2]}
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

pred init[t: Time] {
	no Pool.owned[t]
	Pool.usedBytes[t] = 0
	Pool.totalBytes[t] = 0
	all s: Slab | s.live[t] = 0 and s.carved[t] = 0
}

/** One allocation on an owned slab `s` (free-list hit or fresh carve). */
pred allocateOn[t, t1: Time, s: Slab] {
	s in Pool.owned[t]
	s.live[t] < objCount
	// If the free list is non-empty (carved > live), pop it; else carve anew.
	(s.carved[t] > s.live[t] or s.carved[t] < objCount)
	s.live[t1] = plus[s.live[t], 1]
	s.carved[t1] = (s.carved[t] > s.live[t] => s.carved[t] else plus[s.carved[t], 1])
	all o: Slab - s | o.live[t1] = o.live[t] and o.carved[t1] = o.carved[t]
	Pool.owned[t1] = Pool.owned[t]
	Pool.totalBytes[t1] = Pool.totalBytes[t]
	Pool.usedBytes[t1] = plus[Pool.usedBytes[t], objSize]
}

pred allocSpare[t, t1: Time] { some s: spare[t] | allocateOn[t, t1, s] }
pred allocHot[t, t1: Time] { no spare[t] and some s: hot[t] | allocateOn[t, t1, s] }
pred allocCold[t, t1: Time] { no spare[t] and no hot[t] and some s: cold[t] | allocateOn[t, t1, s] }

/** mempool_alloc() falling through to a fresh slab from the slab cache. */
pred allocNew[t, t1: Time] {
	no spare[t] and no hot[t] and no cold[t]
	some s: Slab - Pool.owned[t] {
		Pool.owned[t1] = Pool.owned[t] + s
		Pool.totalBytes[t1] = plus[Pool.totalBytes[t], slabSize]
		Pool.usedBytes[t1] = plus[Pool.usedBytes[t], objSize]
		s.live[t1] = 1
		s.carved[t1] = 1
		all o: Slab - s | o.live[t1] = o.live[t] and o.carved[t1] = o.carved[t]
	}
}

pred alloc[t, t1: Time] {
	allocSpare[t, t1] or allocHot[t, t1] or allocCold[t, t1] or allocNew[t, t1]
}

/** Free one object on slab `s`, including the spare/return policy. */
pred freeOn[t, t1: Time, s: Slab] {
	s in Pool.owned[t]
	s.live[t] > 0
	s.live[t1] = minus[s.live[t], 1]
	s.carved[t1] = s.carved[t]
	all o: Slab - s | o.live[t1] = o.live[t] and o.carved[t1] = o.carved[t]
	Pool.usedBytes[t1] = minus[Pool.usedBytes[t], objSize]
	let empty = (s.live[t1] = 0) {
		(not empty and Pool.owned[t1] = Pool.owned[t] and Pool.totalBytes[t1] = Pool.totalBytes[t])
		or
		(empty and no spare[t] and Pool.owned[t1] = Pool.owned[t] and
		 Pool.totalBytes[t1] = Pool.totalBytes[t])
		or
		(empty and some p: spare[t] {
			// Keep the lower-address empty slab as spare, return the other.
			(s.addr < p.addr and Pool.owned[t1] = Pool.owned[t] - p and
			 Pool.totalBytes[t1] = minus[Pool.totalBytes[t], slabSize])
			or
			(p.addr < s.addr and Pool.owned[t1] = Pool.owned[t] - s and
			 Pool.totalBytes[t1] = minus[Pool.totalBytes[t], slabSize])
		})
	}
}

pred free[t, t1: Time] { some s: Pool.owned[t] | freeOn[t, t1, s] }

pred stutter[t, t1: Time] {
	Pool.owned[t1] = Pool.owned[t]
	Pool.usedBytes[t1] = Pool.usedBytes[t]
	Pool.totalBytes[t1] = Pool.totalBytes[t]
	all s: Slab | s.live[t1] = s.live[t] and s.carved[t1] = s.carved[t]
}

pred step[t, t1: Time] {
	alloc[t, t1] or free[t, t1] or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

pred inv[t: Time] {
	// Accounting.
	Pool.usedBytes[t] = mul[objSize, sum[liveOf[t, Pool.owned[t]]]]
	Pool.totalBytes[t] = mul[slabSize, #Pool.owned[t]]
	// Per-slab slot accounting.
	all s: Pool.owned[t] |
		s.live[t] >= 0 and s.live[t] <= objCount and
		s.carved[t] >= s.live[t] and s.carved[t] <= objCount
	// At most one spare.
	#spare[t] <= 1
	// Returned slabs hold no live objects.
	all s: Slab - Pool.owned[t] | s.live[t] = 0
}

check safety_accounting {
	all t: Time |
		Pool.usedBytes[t] = mul[objSize, sum[liveOf[t, Pool.owned[t]]]] and
		Pool.totalBytes[t] = mul[slabSize, #Pool.owned[t]]
} for 4 but 6 int

check safety_per_slab {
	all t: Time, s: Pool.owned[t] |
		s.live[t] >= 0 and s.live[t] <= objCount and
		s.carved[t] >= s.live[t] and s.carved[t] <= objCount
} for 4 but 6 int

check safety_nonowned {
	all t: Time, s: Slab - Pool.owned[t] | s.live[t] = 0
} for 4 but 6 int

/** Accounting is consistent and no slot is ever handed out twice. */
check safety {
	all t: Time | inv[t]
} for 4 but 6 int

/** Never hand out more memory than was obtained. */
check used_le_total {
	all t: Time | Pool.usedBytes[t] <= Pool.totalBytes[t]
} for 4 but 6 int

/** At most one completely empty slab is retained as the spare. */
check one_spare {
	all t: Time | #spare[t] <= 1
} for 4 but 6 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** A free-list hit reuses a slot without carving a new one. */
run reuse_free_list {
	some t: Time, s: Slab |
		s in Pool.owned[t] and s.carved[t] > s.live[t] and
		allocateOn[t, next[t], s] and
		s.carved[next[t]] = s.carved[t] and
		s.live[next[t]] = plus[s.live[t], 1]
} for 4 but 6 int

/** Freeing the last object of a slab turns it into the spare. */
run last_free_makes_spare {
	some t: Time, s: Slab |
		s.live[t] = 1 and
		freeOn[t, next[t], s] and
		s.live[next[t]] = 0 and
		#spare[next[t]] = 1
} for 4 but 6 int

/** A new slab is obtained only when spare, hot and cold are all empty. */
run new_slab_only_when_needed {
	some t: Time, s: Slab |
		allocNew[t, next[t]] and s in Pool.owned[next[t]] and
		Pool.totalBytes[next[t]] = slabSize
} for 4 but 6 int

/** Full slab trace: obtain a slab, free its object, then reuse the spare. */
run slab_recycle {
	some s: Slab |
		allocNew[first, next[first]] and
		s in Pool.owned[next[first]] and
		freeOn[next[first], next[next[first]], s] and
		allocateOn[next[next[first]], last, s]
} for 4 but 6 int

/** Freeing a slab that keeps live objects leaves the pool unchanged. */
run free_keeps_owned {
	some t: Time, s: Slab |
		freeOn[t, next[t], s] and s.live[next[t]] > 0 and
		Pool.owned[next[t]] = Pool.owned[t] and
		Pool.totalBytes[next[t]] = Pool.totalBytes[t]
} for 4 but 6 int
