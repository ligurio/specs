// matras.als -- model of the address-translating allocator `matras`
// (small/matras.c, include/small/matras.h).
//
// Matras hands out equally sized blocks identified by small integer ids and
// translates an id to a physical block. It also supports read views: a
// snapshot of (block_count, id->block mapping) that stays valid while the
// writer continues, using copy-on-write (`matras_touch`).
//
// LIMITATIONS:
//  - The extent tree is abstracted: `Id.phys` is the current id->block map
//    (one `Id` atom per block id) and blocks are abstract atoms. The concrete
//    3-level `root / n1 / n2 / n3` translation, `shift`/`mask` arithmetic,
//    lazy extent creation and `extent_count` / `read_view_extent_count`
//    accounting are not modeled.
//  - `matras_alloc_range` / `matras_dealloc_range` and `matras_touch_reserve`
//    are not modeled; `matras_dealloc` removes the highest id only.
//  - Ids are 4 atoms (capacity 4) and blocks are 4 atoms; read views are two
//    pre-declared atoms. A view is inactive when its count is 0.
//  - Bounded: Time=5, Int width 4. See ../README.md#model-limitations.
//
// C asserts covered: matras.c:52-58,247,265,395,461,510 and matras.h:376,427;
// plus address-translation injectivity and the COW property of matras_touch.

module matras

open util/ordering[Time]
open util/integer

sig Time {}

sig Block {}
one sig B0, B1, B2, B3 extends Block {}

sig Id {
	val: one Int,
	phys: Time -> lone Block
}
one sig I0, I1, I2, I3 extends Id {}

sig View {
	vcount: Time -> one Int,
	vphys: Id -> Time -> lone Block
}
one sig V0, V1 extends View {}

one sig M {
	count: Time -> one Int
}

fun capacity: Int { 4 }
fun idAt[k: Int]: lone Id { {i: Id | i.val = k} }
fun headOf[t: Time, k: Int]: lone Block { (idAt[k]).phys[t] }

pred mapUnchanged[t, t1: Time] {
	all i: Id | i.phys[t1] = i.phys[t]
}
pred viewsUnchanged[t, t1: Time] {
	all v: View | v.vcount[t1] = v.vcount[t] and
		(all i: Id | v.vphys[i][t1] = v.vphys[i][t])
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

pred init[t: Time] {
	M.count[t] = 0
	all i: Id | no i.phys[t]
	all v: View | v.vcount[t] = 0 and (all i: Id | no v.vphys[i][t])
}

/** matras_alloc(): add one block with the next id. */
pred allocOn[t, t1: Time] {
	M.count[t] < capacity
	some k: Int, b: Block {
		some idAt[k]
		k = M.count[t]
		(all i: Id | i.phys[t] != b)
		M.count[t1] = plus[M.count[t], 1]
		(idAt[k]).phys[t1] = b
		all i: Id | (i = idAt[k] or i.phys[t1] = i.phys[t])
	}
	viewsUnchanged[t, t1]
}

/** matras_dealloc(): drop the highest id. */
pred dealloc[t, t1: Time] {
	M.count[t] > 0
	M.count[t1] = minus[M.count[t], 1]
	mapUnchanged[t, t1]
	viewsUnchanged[t, t1]
}

/** matras_create_read_view(): snapshot count and mapping. */
pred createView[t, t1: Time, v: View] {
	v.vcount[t] = 0
	M.count[t] > 0
	v.vcount[t1] = M.count[t]
	all i: Id | (i.val < M.count[t] => v.vphys[i][t1] = i.phys[t]
	                                 else no v.vphys[i][t1])
	all o: View - v | o.vcount[t1] = o.vcount[t] and
		(all i: Id | o.vphys[i][t1] = o.vphys[i][t])
	M.count[t1] = M.count[t]
	mapUnchanged[t, t1]
}

/** matras_destroy_read_view(): forget a snapshot. */
pred destroyView[t, t1: Time, v: View] {
	v.vcount[t] > 0
	v.vcount[t1] = 0
	all i: Id | no v.vphys[i][t1]
	all o: View - v | o.vcount[t1] = o.vcount[t] and
		(all i: Id | o.vphys[i][t1] = o.vphys[i][t])
	M.count[t1] = M.count[t]
	mapUnchanged[t, t1]
}

/** matras_touch(): copy a block on write if a read view still references it. */
pred touchOn[t, t1: Time, k: Int] {
	some id: idAt[k] {
		k >= 0 and k < M.count[t]
		some old: id.phys[t] {
			(
				(some v: View | v.vcount[t] > k and v.vphys[id][t] = old)
					=> (some b: Block |
						b != old and id.phys[t1] = b and
						(all j: Id | j.phys[t] != b) and
						(no v: View, j: Id | v.vphys[j][t] = b))
					else id.phys[t1] = old
			)
			all i: Id | (i = id or i.phys[t1] = i.phys[t])
		}
		M.count[t1] = M.count[t]
	}
	viewsUnchanged[t, t1]
}

pred alloc[t, t1: Time] { allocOn[t, t1] }
pred deallocStep[t, t1: Time] { dealloc[t, t1] }
pred touch[t, t1: Time] { some k: Int | touchOn[t, t1, k] }

pred stutter[t, t1: Time] {
	M.count[t1] = M.count[t]
	mapUnchanged[t, t1]
	viewsUnchanged[t, t1]
}

pred step[t, t1: Time] {
	alloc[t, t1] or deallocStep[t, t1] or touch[t, t1] or
	(some v: View | createView[t, t1, v] or destroyView[t, t1, v]) or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

pred inv[t: Time] {
	M.count[t] >= 0 and M.count[t] <= capacity
	all k: Int | 0 <= k and k < M.count[t] => one headOf[t, k]
	// Translation is injective on allocated ids.
	all k1, k2: Int | 0 <= k1 and k1 < k2 and k2 < M.count[t] =>
		headOf[t, k1] != headOf[t, k2]
}

check safety { all t: Time | inv[t] } for 5 but 4 int

/** A live read view is immutable. */
check view_immutable {
	all t: Time - last, v: View |
		v.vcount[t] > 0 and v.vcount[next[t]] > 0 implies
			(v.vcount[next[t]] = v.vcount[t] and
			 all i: Id | v.vphys[i][next[t]] = v.vphys[i][t])
} for 5 but 4 int

/** After a touch, head no longer shares the block with any live view. */
check touch_isolates {
	all t: Time - last, k: Int |
		touchOn[t, next[t], k] and k < M.count[t] implies
			(no v: View | v.vcount[t] > k and v.vphys[idAt[k]][t] = headOf[next[t], k])
} for 5 but 4 int

/** A read view snapshot agrees with the writer at creation time. */
check view_matches_writer {
	all t: Time - last, v: View |
		createView[t, next[t], v] implies
			(v.vcount[next[t]] = M.count[t] and
			 all i: Id | i.val < M.count[t] => v.vphys[i][next[t]] = i.phys[t])
} for 5 but 4 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Allocate, snapshot, then touch so the writer diverges from the view. */
run touch_after_view {
	some t: Time, k: Int |
		M.count[t] > 0 and k < M.count[t] and
		(some v: View | v.vcount[next[t]] > k) and
		touchOn[next[t], next[next[t]], k] and
		headOf[next[t], k] != headOf[next[next[t]], k]
} for 5 but 4 int

/** Deallocation drops the highest id and leaves the lower ones. */
run dealloc_last_id {
	some t: Time |
		M.count[t] > 0 and dealloc[t, next[t]] and
		M.count[next[t]] = minus[M.count[t], 1]
} for 5 but 4 int

/** Full COW trace: alloc id 0, snapshot it, touch it, drop the view. */
run cow_lifecycle {
	some v: View |
		alloc[first, next[first]] and
		createView[next[first], next[next[first]], v] and
		touchOn[next[next[first]], next[next[next[first]]], 0] and
		destroyView[next[next[next[first]]], last, v]
} for 5 but 4 int

/** A live snapshot is unaffected by a later allocation. */
run view_stable_on_alloc {
	some v: View |
		alloc[first, next[first]] and
		createView[next[first], next[next[first]], v] and
		alloc[next[next[first]], next[next[next[first]]]] and
		v.vphys[idAt[0]][next[next[next[first]]]] =
			v.vphys[idAt[0]][next[next[first]]]
} for 5 but 4 int
