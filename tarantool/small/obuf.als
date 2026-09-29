// obuf.als -- model of the output buffer `struct obuf` (small/obuf.c,
// include/small/obuf.h).
//
// An obuf is a vector of iovecs. Each next iovec is (normally) twice as large
// as the previous one; the slot after the last allocated one is a zero
// sentinel. `obuf_reserve` ensures contiguous room in the current iovec (and
// may reallocate it), `obuf_alloc` commits, and `obuf_rollback_to_svp` forgets
// everything written after a savepoint.
//
// LIMITATIONS:
//  - Three abstract iovec slots S0/S1/S2, start_capacity 1; the slab cache and
//    `slab_get` are abstracted. `SMALL_OBUF_IOV_MAX = 3` here.
//  - `obuf_dup` (data copying) and `obuf_destroy` are not modeled; byte data
//    is abstract.
//  - The debug `reserved` flag is modeled as an integer 0/1.
//  - Bounded: Time=5, Int width 5. See ../README.md#model-limitations.
//
// C asserts covered: obuf.c:41-43,134,159,169,186,205,213 and obuf.h:177,209.

module obuf

open util/ordering[Time]
open util/integer

sig Time {}

abstract sig Slot {
	len: Time -> one Int,
	cap: Time -> one Int
}
one sig S0, S1, S2 extends Slot {}

one sig Buf {
	pos: Time -> one Int,
	nIov: Time -> one Int,
	used: Time -> one Int,
	reserved: Time -> one Int
}

fun startCap: Int { 1 }
fun maxIov: Int { 3 }

fun slotAt[i: Int]: lone Slot {
	i = 0 => S0 else i = 1 => S1 else i = 2 => S2 else none
}
fun lenSum[t: Time]: Int { plus[S0.len[t], plus[S1.len[t], S2.len[t]]] }

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

pred init[t: Time] {
	all s: Slot | s.len[t] = 0 and s.cap[t] = 0
	Buf.pos[t] = 0
	Buf.nIov[t] = 0
	Buf.used[t] = 0
	Buf.reserved[t] = 0
}

/** obuf_reserve(): ensure `size` bytes free in some current slot. */
pred reserveSlow[t, t1: Time, size: Int] {
	Buf.reserved[t] = 0
	size > 0
	some cur: slotAt[Buf.pos[t]] {
		// A non-empty current slot forces a move to the next one.
		(Buf.pos[t] < maxIov) and
		let p1 = (cur.len[t] > 0 => plus[Buf.pos[t], 1] else Buf.pos[t]) |
		some target: slotAt[p1] {
			target.len[t] = 0
			// Grow the target capacity if needed (in place or fresh).
			(size <= target.cap[t] and target.cap[t1] = target.cap[t]) or
			(size > target.cap[t] and
			 target.cap[t1] >= size and
			 target.cap[t1] >= target.cap[t] and
			 (target.cap[t] = 0 => target.cap[t1] >= mul[startCap, pow2[p1]])
			 and (target.cap[t] > 0 => target.cap[t1] >= mul[2, target.cap[t]]))
			Buf.pos[t1] = p1
			Buf.nIov[t1] = (p1 >= Buf.nIov[t] => plus[p1, 1] else Buf.nIov[t])
			Buf.used[t1] = Buf.used[t]
			Buf.reserved[t1] = 1
			all s: Slot | s.len[t1] = s.len[t]
			all s: Slot - target | s.cap[t1] = s.cap[t]
		}
	}
}

fun pow2[n: Int]: Int { n = 0 => 1 else n = 1 => 2 else 4 }

/** obuf_alloc(): commit `size` bytes in the current slot. */
pred alloc[t, t1: Time, size: Int] {
	Buf.reserved[t] = 1
	size >= 0
	some cur: slotAt[Buf.pos[t]] {
		plus[cur.len[t], size] <= cur.cap[t]
		Buf.pos[t1] = Buf.pos[t]
		Buf.nIov[t1] = Buf.nIov[t]
		Buf.used[t1] = plus[Buf.used[t], size]
		Buf.reserved[t1] = 0
		cur.len[t1] = plus[cur.len[t], size]
		all s: Slot - cur | s.len[t1] = s.len[t] and s.cap[t1] = s.cap[t]
		cur.cap[t1] = cur.cap[t]
	}
}

/** obuf_rollback_to_svp(): restore the savepoint (p, l). */
pred rollback[t, t1: Time, p: Int, l: Int] {
	p >= 0 and p <= Buf.pos[t]
	some s: slotAt[p] {
		l >= 0 and l <= s.cap[t]
		Buf.pos[t1] = p
		Buf.nIov[t1] = Buf.nIov[t]
		Buf.reserved[t1] = 0
		s.len[t1] = l
		all o: Slot | (o in slotAt[plus[p, 1]] + slotAt[plus[p, 2]] => o.len[t1] = 0)
		all o: Slot | (o = s or o in slotAt[plus[p, 1]] + slotAt[plus[p, 2]] or
			o.len[t1] = o.len[t])
		all o: Slot | o.cap[t1] = o.cap[t]
		Buf.used[t1] = lenSum[t1]
	}
}

/** obuf_reset(): logically empty the buffer, keep the memory. */
pred reset[t, t1: Time] {
	Buf.pos[t1] = 0
	Buf.nIov[t1] = Buf.nIov[t]
	Buf.used[t1] = 0
	Buf.reserved[t1] = 0
	all s: Slot | s.len[t1] = 0 and s.cap[t1] = s.cap[t]
}

pred stutter[t, t1: Time] {
	Buf.pos[t1] = Buf.pos[t]
	Buf.nIov[t1] = Buf.nIov[t]
	Buf.used[t1] = Buf.used[t]
	Buf.reserved[t1] = Buf.reserved[t]
	all s: Slot | s.len[t1] = s.len[t] and s.cap[t1] = s.cap[t]
}

pred step[t, t1: Time] {
	(some n: Int | reserveSlow[t, t1, n]) or (some n: Int | alloc[t, t1, n]) or
	(some p, l: Int | rollback[t, t1, p, l]) or reset[t, t1] or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

pred inv[t: Time] {
	Buf.used[t] = lenSum[t]
	all s: Slot | s.len[t] >= 0 and s.len[t] <= s.cap[t]
	Buf.pos[t] >= 0 and Buf.nIov[t] >= 0 and Buf.nIov[t] <= maxIov
	Buf.pos[t] <= Buf.nIov[t]
	Buf.reserved[t] in 0 + 1
	// Slots beyond the allocated prefix are zero (the sentinel).
	all i: Int | i >= Buf.nIov[t] and i < maxIov =>
		some s: slotAt[i] | s.len[t] = 0 and s.cap[t] = 0
	// Normal capacity growth: slot i has at least start_capacity * 2^i.
	all i: Int | 0 <= i and i < Buf.nIov[t] =>
		some s: slotAt[i] | s.cap[t] >= mul[startCap, pow2[i]]
}

check inv_used_sum { all t: Time | Buf.used[t] = lenSum[t] } for 5 but 5 int
check inv_len_bounds {
	all t: Time, s: Slot | s.len[t] >= 0 and s.len[t] <= s.cap[t]
} for 5 but 5 int
check inv_pos_bounds {
	all t: Time | Buf.pos[t] >= 0 and Buf.nIov[t] >= 0 and
		Buf.nIov[t] <= maxIov and Buf.pos[t] <= Buf.nIov[t]
} for 5 but 5 int
check inv_sentinel {
	all t: Time, i: Int | i >= Buf.nIov[t] and i < maxIov =>
		(some s: slotAt[i] | s.len[t] = 0 and s.cap[t] = 0)
} for 5 but 5 int
check inv_cap_growth {
	all t: Time, i: Int | 0 <= i and i < Buf.nIov[t] =>
		(some s: slotAt[i] | s.cap[t] >= mul[startCap, pow2[i]])
} for 5 but 5 int
check inv_reserved { all t: Time | Buf.reserved[t] in 0 + 1 } for 5 but 5 int

check safety {
	all t: Time | inv[t]
} for 5 but 5 int

/** A commit never overruns the current iovec. */
check alloc_no_overrun {
	all t: Time - last, n: Int |
		alloc[t, next[t], n] implies
			(some s: slotAt[Buf.pos[t]] | plus[s.len[t], n] <= s.cap[t])
} for 5 but 5 int

/** Rollback restores a consistent used count. */
check rollback_restores {
	all t: Time - last, p, l: Int |
		rollback[t, next[t], p, l] implies Buf.used[next[t]] = lenSum[next[t]]
} for 5 but 5 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Fill the first iovec, advance to the second, then roll back. */
run advance_and_rollback {
	some t: Time |
		Buf.pos[next[t]] > Buf.pos[t] and Buf.pos[next[t]] = 1 and
		(some p, l: Int | rollback[next[t], next[next[t]], p, l])
} for 5 but 5 int

/** A reservation grows the next iovec to at least twice the previous one. */
run capacity_doubles {
	some t: Time |
		reserveSlow[t, next[t], 2] and
		Buf.nIov[next[t]] = 1 and S0.cap[next[t]] >= 2
} for 5 but 5 int

/** Full iovec trace: reserve in S0, commit, advance to S1, then roll back. */
run iovec_lifecycle {
	reserveSlow[first, next[first], 1] and
	alloc[next[first], next[next[first]], 1] and
	reserveSlow[next[next[first]], next[next[next[first]]], 1] and
	rollback[next[next[next[first]]], last, 0, 0]
} for 5 but 5 int

/** A reservation repositions the cursor but keeps the written bytes. */
run reserve_keeps_contents {
	some t: Time, n: Int |
		reserveSlow[t, next[t], n] and
		(all s: Slot | s.len[next[t]] = s.len[t]) and
		Buf.used[next[t]] = Buf.used[t]
} for 5 but 5 int
