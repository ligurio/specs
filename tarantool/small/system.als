// system.als -- end-to-end integration of the Small allocation stack.
//
// This model composes the observable contract of the allocators in one
// abstract picture: a `small` allocator maps an object to a pool whose object
// size is at least the requested size, pools hold a bounded number of live
// objects, and the total used memory is derived from the pools. It checks that
// the accounting holds across allocate/free and that everything is released at
// the end.
//
// LIMITATIONS:
//  - This is *not* a composition of `small.als`, `mempool.als`, `slab_cache.als`
//    and `slab_arena.als`; those each have their own state and they are
//    abstracted here to two pools with a fixed capacity and the objects they
//    own. Slabs, buddy splitting/merging and the slab arena are not modeled.
//  - `small_class` is represented by an abstract class: the pool is chosen
//    among those with `objsize >= size` (the model does not compute classes).
//  - Bounded: Time=6, Int width 5. See ../README.md#model-limitations.

module system

open util/ordering[Time]
open util/integer

sig Time {}

abstract sig Pool {
	objsize: one Int,
	cap: one Int,
	live: Time -> one Int
}
one sig P0, P1 extends Pool {}

abstract sig Obj {
	size: one Int,
	owner: Time -> lone Pool
}
one sig O0, O1, O2, O3 extends Obj {}

one sig Sys {
	usedBytes: Time -> one Int,
	liveTotal: Time -> one Int
}

fact geometry {
	P0.objsize = 1 and P0.cap = 3
	P1.objsize = 2 and P1.cap = 2
	O0.size = 1 and O1.size = 1 and O2.size = 2 and O3.size = 2
}

fun poolLive[t: Time, p: Pool]: Int { p.live[t] }
fun liveSum[t: Time]: Int { plus[poolLive[t, P0], poolLive[t, P1]] }
fun usedSum[t: Time]: Int {
	plus[mul[P0.objsize, poolLive[t, P0]], mul[P1.objsize, poolLive[t, P1]]]
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

pred init[t: Time] {
	all p: Pool | p.live[t] = 0
	all o: Obj | no o.owner[t]
	Sys.usedBytes[t] = 0
	Sys.liveTotal[t] = 0
}

/** smalloc(size): find a pool with objsize >= size and room, then own it. */
pred allocOn[t, t1: Time, o: Obj] {
	no o.owner[t]
	some p: Pool {
		p.objsize >= o.size
		p.live[t] < p.cap
		o.owner[t1] = p
		all x: Obj - o | x.owner[t1] = x.owner[t]
		p.live[t1] = plus[p.live[t], 1]
		all q: Pool - p | q.live[t1] = q.live[t]
		Sys.liveTotal[t1] = plus[Sys.liveTotal[t], 1]
		Sys.usedBytes[t1] = plus[Sys.usedBytes[t], p.objsize]
	}
}

pred alloc[t, t1: Time] { some o: Obj | allocOn[t, t1, o] }

/** smfree(): return the object to its pool. */
pred freeOn[t, t1: Time, o: Obj] {
	some p: o.owner[t] {
		o.owner[t1] = none
		all x: Obj - o | x.owner[t1] = x.owner[t]
		p.live[t1] = minus[p.live[t], 1]
		all q: Pool - p | q.live[t1] = q.live[t]
		Sys.liveTotal[t1] = minus[Sys.liveTotal[t], 1]
		Sys.usedBytes[t1] = minus[Sys.usedBytes[t], p.objsize]
	}
}

pred free[t, t1: Time] { some o: Obj | freeOn[t, t1, o] }

pred stutter[t, t1: Time] {
	all p: Pool | p.live[t1] = p.live[t]
	all o: Obj | o.owner[t1] = o.owner[t]
	Sys.usedBytes[t1] = Sys.usedBytes[t]
	Sys.liveTotal[t1] = Sys.liveTotal[t]
}

pred step[t, t1: Time] { alloc[t, t1] or free[t, t1] or stutter[t, t1] }

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

pred inv[t: Time] {
	Sys.usedBytes[t] = usedSum[t]
	Sys.liveTotal[t] = liveSum[t]
	all p: Pool | p.live[t] >= 0 and p.live[t] <= p.cap
	all o: Obj | some o.owner[t] => o.owner[t].objsize >= o.size
}

check inv_used { all t: Time | Sys.usedBytes[t] = usedSum[t] } for 5 but 4 int
check inv_live { all t: Time | Sys.liveTotal[t] = liveSum[t] } for 5 but 4 int
check inv_cap {
	all t: Time, p: Pool | p.live[t] >= 0 and p.live[t] <= p.cap
} for 5 but 4 int
check inv_fits {
	all t: Time, o: Obj | some o.owner[t] => o.owner[t].objsize >= o.size
} for 5 but 4 int
check safety { all t: Time | inv[t] } for 5 but 4 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Allocate all objects, free all of them, and observe zero usage. */
run alloc_all_then_free_all {
	some t: Time |
		Sys.liveTotal[t] = 4 and Sys.usedBytes[t] = 6 and
		(all o: Obj | some o.owner[t]) and
		Sys.liveTotal[first] = 0 and Sys.usedBytes[first] = 0
} for 5 but 4 int

/** An object is always served by a pool that can hold it. */
run object_fits_pool {
	some t: Time, o: Obj |
		some o.owner[t] and o.owner[t].objsize >= o.size
} for 5 but 4 int

/** Full system trace: allocate two objects, then free them both. */
run alloc_free_lifecycle {
	alloc[first, next[first]] and
	alloc[next[first], next[next[first]]] and
	free[next[next[first]], next[next[next[first]]]] and
	free[next[next[next[first]]], last]
} for 5 but 4 int

/** Freeing an object leaves every other pool's occupancy unchanged. */
run free_keeps_other_pools {
	some t: Time, o: Obj |
		some o.owner[t] and
		freeOn[t, next[t], o] and
		(all q: Pool - o.owner[t] | q.live[next[t]] = q.live[t])
} for 5 but 4 int
