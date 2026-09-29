// lsregion.als -- model of the log-structured `lsregion` allocator
// (small/lsregion.c, include/small/lsregion.h).
//
// Memory is a list of equally sized slabs, oldest first. Every allocation
// carries a nondecreasing id; a slab remembers the maximal id allocated in it.
// `lsregion_gc(min_id)` drops the oldest prefix of slabs whose maximal id is
// <= min_id. At most one emptied slab is kept in `cached`.
//
// LIMITATIONS:
//  - Three abstract slabs L0 (oldest) / L1 / L2 (newest) with a fixed order,
//    payload capacity 2; the `lslab` header is not modeled (usage counts
//    payload units).
//  - Because the order is fixed, a cached slab is not reused as a new tail
//    (in the C code a cached slab is recycled); this is not modeled.
//  - Every allocation is one unit, so `slab_used` grows by one per alloc.
//    Large slabs (`slab_size > arena->slab_size`), the slab arena and
//    `lsregion_to_iovec` / savepoints are not modeled.
//  - Bounded: Time=5, Int width 5. See ../README.md#model-limitations.
//
// C asserts covered: lsregion.h:167,177,178,209,210,247,271 and lsregion.c:92.

module lsregion

open util/ordering[Time]
open util/integer

sig Time {}

abstract sig Slab {
	pre: lone Slab,
	used: Time -> one Int,
	maxId: Time -> one Int
}
one sig L0, L1, L2 extends Slab {}

one sig Region {
	present: Time -> set Slab,
	cached: Time -> lone Slab,
	statsUsed: Time -> one Int,
	statsTotal: Time -> one Int
}

fun cap: Int { 2 }
fun slabSize: Int { 2 }

fun usedOn[t: Time, s: Slab]: Int { s in Region.present[t] => s.used[t] else 0 }
fun sizeOn[t: Time, s: Slab]: Int {
	(s in Region.present[t] or Region.cached[t] = s) => slabSize else 0
}
fun sumUsed[t: Time]: Int { plus[usedOn[t, L0], plus[usedOn[t, L1], usedOn[t, L2]]] }
fun sumSize[t: Time]: Int { plus[sizeOn[t, L0], plus[sizeOn[t, L1], sizeOn[t, L2]]] }

fact order {
	no L0.pre
	L1.pre = L0
	L2.pre = L1
}

/** `a` is older than `b` (closer to L0). */
pred older[a, b: Slab] { a in b.^pre }

/** The newest present slab: no present slab has it as its predecessor. */
fun newest[t: Time]: lone Slab {
	{s: Region.present[t] | no o: Region.present[t] | o.pre = s}
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

pred init[t: Time] {
	no Region.present[t]
	no Region.cached[t]
	Region.statsUsed[t] = 0
	Region.statsTotal[t] = 0
	all s: Slab | s.used[t] = 0 and s.maxId[t] = -1
}

/** lsregion_aligned_reserve_slow(): open a slab to the right of the run. */
pred grow[t, t1: Time, s: Slab] {
	s !in Region.present[t]
	s !in Region.cached[t]
	(no Region.present[t] and s = L0) or (some newest[t] and s.pre = newest[t])
	Region.present[t1] = Region.present[t] + s
	Region.cached[t1] = Region.cached[t]
	Region.statsUsed[t1] = Region.statsUsed[t]
	Region.statsTotal[t1] = plus[Region.statsTotal[t], slabSize]
	all o: Slab |
		(o = s => o.used[t1] = 0 and o.maxId[t1] = -1
		       else o.used[t1] = o.used[t] and o.maxId[t1] = o.maxId[t])
}

/** lsregion_alloc(): append one unit with id `id` to the newest slab. */
pred allocOn[t, t1: Time, id: Int] {
	some s: newest[t] {
		s.used[t] < cap
		id >= s.maxId[t]
		Region.present[t1] = Region.present[t]
		Region.cached[t1] = Region.cached[t]
		Region.statsUsed[t1] = plus[Region.statsUsed[t], 1]
		Region.statsTotal[t1] = Region.statsTotal[t]
		all o: Slab |
			(o = s => o.used[t1] = plus[o.used[t], 1] and o.maxId[t1] = id
			       else o.used[t1] = o.used[t] and o.maxId[t1] = o.maxId[t])
	}
}

pred alloc[t, t1: Time] { some id: Int | allocOn[t, t1, id] }

/** lsregion_gc(): drop the oldest prefix of slabs with maxId <= min_id. */
pred gc[t, t1: Time, minId: Int] {
	// The oldest prefix ending just before the first slab with maxId > minId.
	let rm = {s: Region.present[t] |
		s.maxId[t] <= minId and
		all o: Region.present[t] | older[o, s] => o.maxId[t] <= minId} |
		Region.present[t1] = Region.present[t] - rm and
		Region.statsUsed[t1] = sumUsed[t1] and
		Region.statsTotal[t1] = sumSize[t1] and
		((some rm and Region.cached[t] = none and
		  Region.cached[t1] = {c: rm | no o: rm | older[o, c]})
		 or Region.cached[t1] = Region.cached[t]) and
		(all s: Slab | s.used[t1] = s.used[t] and s.maxId[t1] = s.maxId[t])
}

pred stutter[t, t1: Time] {
	Region.present[t1] = Region.present[t]
	Region.cached[t1] = Region.cached[t]
	Region.statsUsed[t1] = Region.statsUsed[t]
	Region.statsTotal[t1] = Region.statsTotal[t]
	all s: Slab | s.used[t1] = s.used[t] and s.maxId[t1] = s.maxId[t]
}

pred step[t, t1: Time] {
	(some s: Slab | grow[t, t1, s]) or alloc[t, t1] or
	(some m: Int | gc[t, t1, m]) or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

/** The present slabs are contiguous; ids and usage are consistent. */
pred inv[t: Time] {
	L0 in Region.present[t] and L2 in Region.present[t] => L1 in Region.present[t]
	Region.statsUsed[t] = sumUsed[t]
	Region.statsTotal[t] = sumSize[t]
	#Region.cached[t] <= 1
	no Region.cached[t] & Region.present[t]
	all s: Region.present[t] | s.used[t] >= 0 and s.used[t] <= cap
}

check safety {
	all t: Time | inv[t]
} for 5 but 5 int

/** gc removes only slabs whose maximal id is <= min_id. */
check gc_safety {
	all t: Time - last, m: Int |
		gc[t, next[t], m] implies
			(no s: Region.present[t] - Region.present[next[t]] | s.maxId[t] > m)
} for 5 but 5 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Allocate into two slabs, then gc the oldest one into the cache. */
run gc_keeps_cached {
	some t: Time, id: Int |
		allocOn[t, next[t], id] and
		gc[next[t], next[next[t]], id] and
		#Region.present[next[next[t]]] < #Region.present[next[t]] and
		#Region.cached[next[next[t]]] = 1
} for 6 but 5 int

/** gc never drops a slab whose maximal id is still live. */
run gc_keeps_live_slab {
	some t: Time, m: Int |
		L0 in Region.present[t] and L0.maxId[t] > m and
		gc[t, next[t], m] and L0 in Region.present[next[t]]
} for 5 but 5 int

/** Full slab trace: open a slab, allocate into it, then gc it to the cache. */
run slab_lifecycle {
	grow[first, next[first], L0] and
	allocOn[next[first], next[next[first]], 0] and
	gc[next[next[first]], next[next[next[first]]], 0] and
	Region.cached[next[next[next[first]]]] = L0 and
	stutter[next[next[next[first]]], last]
} for 5 but 5 int

/** An allocation never opens, closes or resizes a slab. */
run alloc_keeps_slabs {
	some t: Time |
		alloc[t, next[t]] and
		Region.present[next[t]] = Region.present[t] and
		Region.cached[next[t]] = Region.cached[t] and
		Region.statsTotal[next[t]] = Region.statsTotal[t]
} for 5 but 5 int
