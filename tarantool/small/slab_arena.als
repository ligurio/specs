// slab_arena.als -- model of `struct slab_arena` (small/slab_arena.c).
//
// The arena hands out fixed-size, equally aligned slabs (`slab_map`) and takes
// them back into a lock-free LIFO cache (`slab_unmap`). Memory is never
// returned to the OS before `slab_arena_destroy`, which asserts that every
// carved slab is present in the cache (`total == arena->used`,
// slab_arena.c:233).
//
// LIMITATIONS:
//  - Slabs are abstract atoms, all of the same size; prealloc vs. mmap and the
//    concrete arena base address are not modeled. `used` is therefore the
//    number of slabs ever obtained, not a byte count.
//  - The lock-free ABA counter of `lf_lifo` is abstracted away: `slab_unmap`
//    and `slab_map` are single atomic steps. Lock-freedom/liveness is not
//    proven, only safety of the abstracted state.
//  - Quota is modeled as a count of charged slabs, not via `quota.als`.
//  - Bounded: Time=4, Slab=4, Int width 4.
//  - See ../README.md#model-limitations.
//
// C asserts covered: slab_arena.c:81,91,93,164,172,233.

module slab_arena

open util/ordering[Time]
open util/integer
open common

sig Time {}
sig Slab {}

one sig Arena {
	inCache: Time -> set Slab,
	out: Time -> set Slab,
	obtained: Time -> set Slab,
	top: Time -> lone Slab,
	link: Time -> Slab -> lone Slab,
	usedSlots: Time -> one Int,
	quotaCharged: Time -> one Int
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

pred init[t: Time] {
	no Arena.inCache[t]
	no Arena.out[t]
	no Arena.obtained[t]
	no Arena.top[t]
	no Arena.link[t]
	Arena.usedSlots[t] = 0
	Arena.quotaCharged[t] = 0
}

/** slab_map() from the LIFO cache: pop the current top slab. */
pred mapHit[t, t1: Time] {
	some h: Arena.inCache[t] {
		h = Arena.top[t]
		Arena.usedSlots[t1] = Arena.usedSlots[t]
		Arena.quotaCharged[t1] = Arena.quotaCharged[t]
		Arena.obtained[t1] = Arena.obtained[t]
		Arena.inCache[t1] = Arena.inCache[t] - h
		Arena.out[t1] = Arena.out[t] + h
		Arena.top[t1] = h.(Arena.link[t])
		Arena.link[t1] = Arena.link[t] - (h <: Arena.link[t])
	}
}

/** slab_map() miss: obtain one previously unused slab. */
pred mapMiss[t, t1: Time] {
	some s: Slab - Arena.obtained[t] {
		Arena.usedSlots[t1] = plus[Arena.usedSlots[t], 1]
		Arena.quotaCharged[t1] = plus[Arena.quotaCharged[t], 1]
		Arena.obtained[t1] = Arena.obtained[t] + s
		Arena.out[t1] = Arena.out[t] + s
		Arena.inCache[t1] = Arena.inCache[t]
		Arena.top[t1] = Arena.top[t]
		Arena.link[t1] = Arena.link[t]
	}
}

pred slabMap[t, t1: Time] { mapHit[t, t1] or mapMiss[t, t1] }

/** slab_unmap(): push a handed-out slab back onto the LIFO cache. */
pred slabUnmap[t, t1: Time] {
	some s: Arena.out[t] {
		Arena.usedSlots[t1] = Arena.usedSlots[t]
		Arena.quotaCharged[t1] = Arena.quotaCharged[t]
		Arena.obtained[t1] = Arena.obtained[t]
		Arena.out[t1] = Arena.out[t] - s
		Arena.inCache[t1] = Arena.inCache[t] + s
		Arena.top[t1] = s
		Arena.link[t1] = Arena.link[t] + (s -> Arena.top[t])
	}
}

pred stutter[t, t1: Time] {
	Arena.inCache[t1] = Arena.inCache[t]
	Arena.out[t1] = Arena.out[t]
	Arena.obtained[t1] = Arena.obtained[t]
	Arena.top[t1] = Arena.top[t]
	Arena.link[t1] = Arena.link[t]
	Arena.usedSlots[t1] = Arena.usedSlots[t]
	Arena.quotaCharged[t1] = Arena.quotaCharged[t]
}

pred step[t, t1: Time] {
	slabMap[t, t1] or slabUnmap[t, t1] or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

pred inv[t: Time] {
	// Cached and handed-out slabs are disjoint; nothing is lost.
	no Arena.inCache[t] & Arena.out[t]
	Arena.obtained[t] = Arena.inCache[t] + Arena.out[t]
	// Every obtained slab is one slot and is charged to the quota once.
	Arena.usedSlots[t] = #Arena.obtained[t]
	Arena.quotaCharged[t] = #Arena.obtained[t]
	Arena.usedSlots[t] >= 0
	// The cache is a well-formed LIFO stack.
	isLinearFrom[Arena.link[t], Arena.top[t], Arena.inCache[t]]
	some Arena.inCache[t] iff some Arena.top[t]
	Arena.top[t] in Arena.inCache[t]
}

/** No execution loses, duplicates, or double-charges a slab. */
check safety {
	all t: Time | inv[t]
} for 4 but 4 int

/** `slab_map` never returns a slab that is already handed out. */
check map_is_fresh {
	all t: Time - last |
		mapHit[t, next[t]] implies Arena.top[t] !in Arena.out[t]
} for 4 but 4 int

/** Quota is charged once per distinct slab, never per map() call. */
check quota_charged_once {
	all t: Time | Arena.quotaCharged[t] = #Arena.obtained[t]
} for 4 but 4 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Obtain a slab, return it, then obtain it again from the cache. */
run map_unmap_reuse {
	some t: Time |
		mapMiss[t, next[t]] and
		slabUnmap[next[t], next[next[t]]] and
		mapHit[next[next[t]], next[next[next[t]]]]
} for 4 but 4 int

/** After all slabs are returned, the cache holds exactly what was used. */
run destroy_after_all_returned {
	some t: Time |
		no Arena.out[t] and
		Arena.usedSlots[t] = #Arena.inCache[t] and
		Arena.quotaCharged[t] = #Arena.inCache[t]
} for 4 but 4 int

/** Full arena trace: obtain two slabs, then return one to the cache. */
run arena_lifecycle {
	mapMiss[first, next[first]] and
	mapMiss[next[first], next[next[first]]] and
	slabUnmap[next[next[first]], last]
} for 4 but 4 int

/** Returning a slab moves it between sets but does not change accounting. */
run unmap_keeps_counters {
	some t: Time |
		slabUnmap[t, next[t]] and
		Arena.usedSlots[next[t]] = Arena.usedSlots[t] and
		Arena.quotaCharged[next[t]] = Arena.quotaCharged[t]
} for 4 but 4 int
