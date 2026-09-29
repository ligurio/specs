// slab_cache.als -- model of the buddy allocator `struct slab_cache`
// (small/slab_cache.c).
//
// A slab cache obtains power-of-two slabs from an arena and splits/merges
// them with the buddy algorithm. `slab_get_with_order` splits the smallest
// available block down to the requested order; `slab_put_with_order` frees a
// block and greedily merges it with free buddies. A block of the maximum
// order is returned to the arena as soon as a second free maximum-order block
// exists, to avoid cache/arena oscillation.
//
// LIMITATIONS:
//  - The address space is fixed and tiny: two regions of order_max = 1, so
//    the blocks are M0,M1 (order 1) and Z0..Z3 (order 0). There are no
//    orders > 1 and no `slab_get_large` / huge slabs.
//  - `buddyOf`, `parentOf`, `childrenOf`, `addr`, `size` are hardcoded facts,
//    not computed from addresses (no XOR). `slab->in_use`, `magic`,
//    `next_in_cache` and the `allocated` list are not modeled as such.
//  - Only slab orders 0 and 1 are requested; the search order over free
//    lists is encoded by the cases below.
//  - Bounded: Time=4, Int width 4.
//  - See ../README.md#model-limitations.
//
// C asserts covered: slab_cache.c:66-75,83,130,141,159,178,224,294,325,334,368
// and the accounting checks slab_cache.c:428-472.

module slab_cache

open util/ordering[Time]
open util/integer

sig Time {}

// ---------------------------------------------------------------------------
// Fixed buddy geometry: two regions (M0, M1) of order 1, each split into two
// order-0 blocks (Z0/Z1 and Z2/Z3).
// ---------------------------------------------------------------------------

abstract sig Block {
	ord: one Int,
	idx: one Int,
	addr: one Int,
	size: one Int,
	buddyOf: lone Block,
	parentOf: lone Block,
	childrenOf: set Block
}
one sig M0, M1, Z0, Z1, Z2, Z3 extends Block {}

fact geometry {
	M0.ord = 1 and M0.idx = 0 and M0.addr = 0 and M0.size = 2 and
		no M0.buddyOf and no M0.parentOf and M0.childrenOf = Z0 + Z1
	M1.ord = 1 and M1.idx = 1 and M1.addr = 2 and M1.size = 2 and
		no M1.buddyOf and no M1.parentOf and M1.childrenOf = Z2 + Z3
	Z0.ord = 0 and Z0.idx = 0 and Z0.addr = 0 and Z0.size = 1 and
		Z0.buddyOf = Z1 and Z0.parentOf = M0 and no Z0.childrenOf
	Z1.ord = 0 and Z1.idx = 1 and Z1.addr = 1 and Z1.size = 1 and
		Z1.buddyOf = Z0 and Z1.parentOf = M0 and no Z1.childrenOf
	Z2.ord = 0 and Z2.idx = 2 and Z2.addr = 2 and Z2.size = 1 and
		Z2.buddyOf = Z3 and Z2.parentOf = M1 and no Z2.childrenOf
	Z3.ord = 0 and Z3.idx = 3 and Z3.addr = 3 and Z3.size = 1 and
		Z3.buddyOf = Z2 and Z3.parentOf = M1 and no Z3.childrenOf
}

/** Block `b` covers the address `x` (x is a unit of the smallest order). */
pred covers[b: Block, x: Int] {
	b.addr <= x and x < plus[b.addr, b.size]
}

/** A region is present if its order-1 block or one of its children is live. */
pred regionPresent[t: Time, m: Block] {
	m in Arena.live[t] or some m.childrenOf & Arena.live[t]
}

// ---------------------------------------------------------------------------
// Mutable state
// ---------------------------------------------------------------------------

one sig Arena {
	live: Time -> set Block,
	used: Time -> set Block,
	arenaTotal: Time -> one Int
}

/** Blocks currently present but not handed out. */
fun free[t: Time]: set Block {
	Arena.live[t] - Arena.used[t]
}

/** Free maximum-order blocks. */
fun freeMax[t: Time]: set Block {
	free[t] & (M0 + M1)
}

/** Regions currently obtained (either intact or split into children). */
fun presentRegions[t: Time]: set Block {
	{m: M0 + M1 | m in Arena.live[t] or some m.childrenOf & Arena.live[t]}
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

pred init[t: Time] {
	no Arena.live[t]
	no Arena.used[t]
	Arena.arenaTotal[t] = 0
}

/** slab_get_with_order(1) from an existing free order-1 block. */
pred getOrder1Free[t, t1: Time, m: Block] {
	m in freeMax[t]
	Arena.live[t1] = Arena.live[t]
	Arena.used[t1] = Arena.used[t] + m
	Arena.arenaTotal[t1] = Arena.arenaTotal[t]
}

/** slab_get_with_order(1): obtain a new region. */
pred getOrder1New[t, t1: Time, m: Block] {
	m in M0 + M1
	not regionPresent[t, m]
	Arena.live[t1] = Arena.live[t] + m
	Arena.used[t1] = Arena.used[t] + m
	Arena.arenaTotal[t1] = plus[Arena.arenaTotal[t], 2]
}

/** slab_get_with_order(0) from an existing free order-0 block. */
pred getOrder0Free[t, t1: Time, z: Block] {
	z in free[t] and z.ord = 0
	Arena.live[t1] = Arena.live[t]
	Arena.used[t1] = Arena.used[t] + z
	Arena.arenaTotal[t1] = Arena.arenaTotal[t]
}

/** slab_get_with_order(0) by splitting a free order-1 block. */
pred getOrder0Split[t, t1: Time, m: Block] {
	m in freeMax[t]
	some c: m.childrenOf {
		Arena.live[t1] = Arena.live[t] - m + m.childrenOf
		Arena.used[t1] = Arena.used[t] + c
	}
	Arena.arenaTotal[t1] = Arena.arenaTotal[t]
}

/** slab_get_with_order(0): obtain a new region and split it at once. */
pred getOrder0New[t, t1: Time, m: Block] {
	m in M0 + M1
	not regionPresent[t, m]
	some c: m.childrenOf {
		Arena.live[t1] = Arena.live[t] + m.childrenOf
		Arena.used[t1] = Arena.used[t] + c
	}
	Arena.arenaTotal[t1] = plus[Arena.arenaTotal[t], 2]
}

pred get[t, t1: Time] {
	(some m: Block | getOrder1Free[t, t1, m] or getOrder1New[t, t1, m] or
		getOrder0Split[t, t1, m] or getOrder0New[t, t1, m])
	or (some z: Block | getOrder0Free[t, t1, z])
}

/** slab_put_with_order(0) when the buddy is not free: no merge. */
pred putOrder0NoMerge[t, t1: Time, z: Block] {
	z in Arena.used[t] and z.ord = 0
	no z.buddyOf & free[t]
	Arena.live[t1] = Arena.live[t]
	Arena.used[t1] = Arena.used[t] - z
	Arena.arenaTotal[t1] = Arena.arenaTotal[t]
}

/**
 * slab_put_with_order(0) with a free buddy: merge into the order-1 parent.
 * The parent is unmapped (and the region dropped) if another free
 * maximum-order block already exists, mirroring slab_cache.c:361-371.
 */
pred putOrder0Merge[t, t1: Time, z: Block] {
	z in Arena.used[t] and z.ord = 0
	some z.buddyOf & free[t]
	let m = z.parentOf {
		Arena.used[t1] = Arena.used[t] - z
		(
			(some (M0 + M1) & (free[t] - z - z.buddyOf) and
			 Arena.live[t1] = Arena.live[t] - z - z.buddyOf and
			 Arena.arenaTotal[t1] = minus[Arena.arenaTotal[t], 2])
			or
			(no (M0 + M1) & (free[t] - z - z.buddyOf) and
			 Arena.live[t1] = Arena.live[t] - z - z.buddyOf + m and
			 Arena.arenaTotal[t1] = Arena.arenaTotal[t])
		)
	}
}

/** slab_put_with_order(1): free an order-1 block, with max-order retention. */
pred putOrder1[t, t1: Time, m: Block] {
	m in Arena.used[t] and m.ord = 1
	Arena.used[t1] = Arena.used[t] - m
	(
		(some freeMax[t] and
		 Arena.live[t1] = Arena.live[t] - m and
		 Arena.arenaTotal[t1] = minus[Arena.arenaTotal[t], 2])
		or
		(no freeMax[t] and
		 Arena.live[t1] = Arena.live[t] and
		 Arena.arenaTotal[t1] = Arena.arenaTotal[t])
	)
}

pred put[t, t1: Time] {
	(some z: Block | putOrder0NoMerge[t, t1, z] or putOrder0Merge[t, t1, z])
	or (some m: Block | putOrder1[t, t1, m])
}

pred stutter[t, t1: Time] {
	Arena.live[t1] = Arena.live[t]
	Arena.used[t1] = Arena.used[t]
	Arena.arenaTotal[t1] = Arena.arenaTotal[t]
}

pred step[t, t1: Time] {
	get[t, t1] or put[t, t1] or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

/** Live blocks tile exactly the obtained regions, without overlap. */
pred tiling[t: Time] {
	all x: Int |
		(0 <= x and x < 4) =>
			((one b: Arena.live[t] | covers[b, x]) iff
			 (some m: presentRegions[t] | covers[m, x]))
}

/** No two free buddies of the same order remain unmerged. */
pred mergeComplete[t: Time] {
	no free[t].buddyOf & free[t]
}

pred inv[t: Time] {
	Arena.used[t] in Arena.live[t]
	tiling[t]
	mergeComplete[t]
	#freeMax[t] <= 1
	Arena.arenaTotal[t] = mul[2, #presentRegions[t]]
}

/** The buddy state is always a valid tiling and free buddies are merged. */
check safety {
	all t: Time | inv[t]
} for 4 but 4 int

/** A get() only hands out more memory. */
check get_monotone_used {
	all t: Time - last |
		get[t, next[t]] implies Arena.used[t] in Arena.used[next[t]]
} for 4 but 4 int

/** At most one free maximum-order block is kept. */
check at_most_one_free_max {
	all t: Time | #freeMax[t] <= 1
} for 4 but 4 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Obtain and split a region, then free the used half so the halves merge. */
run split_and_coalesce {
	some t: Time, m, c: Block |
		getOrder0New[t, next[t], m] and
		c in Arena.used[next[t]] and
		putOrder0Merge[next[t], next[next[t]], c] and
		m in free[next[next[t]]]
} for 4 but 4 int

/** Obtain a new region while a free order-1 block already exists. */
run second_region_retention {
	some t: Time |
		getOrder1New[t, next[t], M0] and
		putOrder1[next[t], next[next[t]], M0] and
		getOrder1New[next[next[t]], next[next[next[t]]], M1] and
		Arena.arenaTotal[next[next[next[t]]]] <= 4
} for 5 but 4 int

/** Full region trace: obtain M0, free it, then get order 0 by splitting it. */
run region_lifecycle {
	getOrder1New[first, next[first], M0] and
	putOrder1[next[first], next[next[first]], M0] and
	getOrder0Split[next[next[first]], last, M0]
} for 4 but 4 int

/** A retained maximum-order block keeps both live memory and arena total. */
run free_max_retained {
	some t: Time |
		no freeMax[t] and
		putOrder1[t, next[t], M0] and
		Arena.live[next[t]] = Arena.live[t] and
		Arena.arenaTotal[next[t]] = Arena.arenaTotal[t]
} for 4 but 4 int
