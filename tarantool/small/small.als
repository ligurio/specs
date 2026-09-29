// small.als -- model of the `small` allocator (small/small.c).
//
// A `small` allocator is a set of mempools of increasing object size grouped
// by slab order. For each pool `p` the allocator keeps `used_pool(p)`, the
// currently chosen pool for allocations of `p`'s size class: the active pool
// with the smallest index not below `p`. Active pools are the last pool of a
// group plus every pool whose accumulated `waste` (excess bytes paid because
// a smaller class was served by a larger pool) reached `waste_max`; a pool
// with no data and low waste can be deactivated again by the sparse-sweep.
//
// LIMITATIONS:
//  - One group of three pools P0/P1/P2 with object sizes 2/4/8, waste_max = 8,
//    and a per-pool capacity of 4 objects. `small_class` and `mempool` are
//    abstracted: an object has a fixed class `cls` and is owned by a pool.
//  - SLAB_PER_GROUP_MAX, `appropriate_pool_mask` as a 32-bit word, group
//    creation from `small_class`, and `slab_cache`/OOM fallbacks are not
//    modeled. `appropriate(p) = {q | q.idx >= p.idx}`.
//  - `waste_max = slab_order_size / 4` is a fixed constant, not derived.
//  - Bounded: Time=6, Int width 8. See ../README.md#model-limitations.
//
// C asserts covered: small.c:56,58,59,86,96 and the waste/activation logic of
// small.c:340-369, the sparse sweep of small.c:102-138.

module small

open util/ordering[Time]
open util/integer

sig Time {}

// ---------------------------------------------------------------------------
// Geometry
// ---------------------------------------------------------------------------

abstract sig Pool {
	idx: one Int,
	objsize: one Int,
	waste: Time -> one Int,
	usedPool: Time -> lone Pool
}
one sig P0, P1, P2 extends Pool {}

abstract sig Obj {
	cls: one Int,
	owner: Time -> lone Pool
}
one sig O0, O1, O2, O3, O4, O5, O6 extends Obj {}

one sig Group {
	active: Time -> set Pool,
	wasteMax: one Int
}

fun cap: Int { 4 }
fun lastPool: Pool { P2 }

fact geometry {
	P0.idx = 0 and P0.objsize = 2
	P1.idx = 1 and P1.objsize = 4
	P2.idx = 2 and P2.objsize = 8
	Group.wasteMax = 8
	O0.cls = 1 and O1.cls = 1 and O2.cls = 1 and O5.cls = 1
	O3.cls = 0 and O6.cls = 0
	O4.cls = 2
}

/** Used pool: the active pool with the smallest index >= p.idx. */
fun minActive[t: Time, p: Pool]: lone Pool {
	{q: Group.active[t] |
		q.idx >= p.idx and
		no r: Group.active[t] | r.idx >= p.idx and r.idx < q.idx}
}

/** Objects of class `pcls` currently owned by pool `q`. */
fun countByOwner[t: Time, pcls: Int, q: Pool]: Int {
	#{o: Obj | o.cls = pcls and o.owner[t] = q}
}

/**
 * Waste derived from the live objects served by larger pools. Summed per
 * owner pool (not as a set of deltas) so that equal deltas are not collapsed.
 */
fun wasteDerived[t: Time, p: Pool]: Int {
	plus[
		mul[minus[P0.objsize, p.objsize], countByOwner[t, p.idx, P0]],
		plus[
			mul[minus[P1.objsize, p.objsize], countByOwner[t, p.idx, P1]],
			mul[minus[P2.objsize, p.objsize], countByOwner[t, p.idx, P2]]
		]
	]
}

/** Objects currently owned by pool `p`. */
fun ownedBy[t: Time, p: Pool]: set Obj {
	{o: Obj | o.owner[t] = p}
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

pred init[t: Time] {
	Group.active[t] = lastPool
	all p: Pool | p.waste[t] = 0
	all p: Pool | p.usedPool[t] = minActive[t, p]
	no o: Obj | some o.owner[t]
}

/** smalloc(): allocate an object of class `o.cls`. */
pred allocOn[t, t1: Time, o: Obj] {
	no o.owner[t]
	some p: Pool {
		p.idx = o.cls
		some k: p.usedPool[t] {
			#ownedBy[t, k] < cap
			o.owner[t1] = k
			all x: Obj - o | x.owner[t1] = x.owner[t]
			let delta = minus[k.objsize, p.objsize] {
				(k = p => p.waste[t1] = p.waste[t]
				      else p.waste[t1] = plus[p.waste[t], delta])
			}
			all q: Pool - p | q.waste[t1] = q.waste[t]
			(p.waste[t1] >= Group.wasteMax and Group.active[t1] = Group.active[t] + p)
			or
			(p.waste[t1] < Group.wasteMax and Group.active[t1] = Group.active[t])
			all q: Pool | q.usedPool[t1] = minActive[t1, q]
		}
	}
}

pred alloc[t, t1: Time] { some o: Obj | allocOn[t, t1, o] }

/** smfree(): free the object; only `waste` of its class decreases. */
pred freeOn[t, t1: Time, o: Obj] {
	some k: o.owner[t], p: Pool |
		p.idx = o.cls and
		o.owner[t1] = none and
		(all x: Obj - o | x.owner[t1] = x.owner[t]) and
		p.waste[t1] = minus[p.waste[t], minus[k.objsize, p.objsize]] and
		(all q: Pool - p | q.waste[t1] = q.waste[t]) and
		Group.active[t1] = Group.active[t] and
		(all q: Pool | q.usedPool[t1] = minActive[t1, q])
}

pred free[t, t1: Time] { some o: Obj | freeOn[t, t1, o] }

/** small_mempool_group_sweep_sparse(): deactivate a sparse pool. */
pred sweepOn[t, t1: Time, p: Pool] {
	p in Group.active[t]
	p != lastPool
	no ownedBy[t, p]
	p.waste[t] < div[Group.wasteMax, 4]
	Group.active[t1] = Group.active[t] - p
	all q: Pool | q.waste[t1] = q.waste[t]
	all o: Obj | o.owner[t1] = o.owner[t]
	all q: Pool | q.usedPool[t1] = minActive[t1, q]
}

pred sweep[t, t1: Time] { some p: Pool | sweepOn[t, t1, p] }

pred stutter[t, t1: Time] {
	Group.active[t1] = Group.active[t]
	all p: Pool | p.waste[t1] = p.waste[t]
	all o: Obj | o.owner[t1] = o.owner[t]
	all p: Pool | p.usedPool[t1] = p.usedPool[t]
}

pred step[t, t1: Time] {
	alloc[t, t1] or free[t, t1] or sweep[t, t1] or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

pred inv[t: Time] {
	some Group.active[t]
	lastPool in Group.active[t]
	// used_pool is always the minimal active pool not below the class.
	all p: Pool | some p.usedPool[t] and p.usedPool[t] = minActive[t, p]
	all p: Pool | p.usedPool[t].idx >= p.idx and p.usedPool[t].objsize >= p.objsize
	// The waste counter matches the live objects.
	all p: Pool | p.waste[t] = wasteDerived[t, p] and p.waste[t] >= 0
	// Per-pool capacity.
	all p: Pool | #ownedBy[t, p] <= cap
}

/** used_pool, waste and capacity are always consistent. */
check safety {
	all t: Time | inv[t]
} for 6 but 6 int

/** used_pool is exactly the minimal active pool of the class. */
check used_pool_is_minimal {
	all t: Time, p: Pool | p.usedPool[t] = minActive[t, p]
} for 6 but 6 int

/** The stored waste never drifts from the sum over live objects. */
check waste_is_consistent {
	all t: Time, p: Pool | p.waste[t] = wasteDerived[t, p]
} for 6 but 6 int

/** Allocation and free never deactivate a pool (only sweep does). */
check active_monotone_alloc_free {
	all t: Time - last |
		(alloc[t, next[t]] or free[t, next[t]]) =>
			Group.active[t] in Group.active[next[t]]
} for 6 but 6 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/**
 * gh-10217: after a class is switched from a larger to a smaller pool, objects
 * of the same class coexist with different real sizes (`owner.objsize`).
 */
run gh_10217_used_pool_switch {
	some t: Time, o1, o2: Obj |
		Group.active[first] = lastPool and
		Group.active[t] = P1 + P2 and
		o1.cls = 1 and o2.cls = 1 and
		o1.owner[t] = P2 and o2.owner[t] = P1 and
		P1.usedPool[t] = P1
} for 6 but 6 int

/** A sparse pool with no data and low waste can be deactivated. */
run sweep_deactivates_sparse_pool {
	some t: Time |
		P0 in Group.active[t] and P0 !in Group.active[next[t]] and
		no ownedBy[t, P0] and
		P0 != lastPool
} for 6 but 6 int

/**
 * Full pool trace: two class-1 allocations activate P1, a third is served by
 * it, then both are freed.
 */
run activation_lifecycle {
	allocOn[first, next[first], O0] and
	allocOn[next[first], next[next[first]], O1] and
	allocOn[next[next[first]], next[next[next[first]]], O2] and
	freeOn[next[next[next[first]]], next[next[next[next[first]]]], O2] and
	freeOn[next[next[next[next[first]]]], last, O1]
} for 6 but 6 int

/** Freeing an object never deactivates a pool. */
run free_keeps_active {
	some t: Time, o: Obj |
		freeOn[t, next[t], o] and
		Group.active[next[t]] = Group.active[t]
} for 6 but 6 int
