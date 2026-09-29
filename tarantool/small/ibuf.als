// ibuf.als -- model of the input buffer `struct ibuf` (small/ibuf.c,
// include/small/ibuf.h).
//
// An ibuf is one contiguous slab plus three cursors: `rpos` (read), `wpos`
// (write) and `end` (capacity). `ibuf_reserve` defragments in place (moving
// `rpos` back to the start) or grows the buffer (doubling, preserving the
// unread bytes); `ibuf_consume` and `ibuf_discard` move the cursors without
// touching memory.
//
// LIMITATIONS:
//  - Cursors are abstract integer offsets; the slab cache and `memcpy` are
//    abstracted, only the `used` byte count is preserved by a grow.
//  - `start_capacity` is 4; capacity is bounded by 16 (Int width 5).
//  - `ibuf_shrink` is modeled as any grow-free reallocation to a capacity
//    that still fits `used`.
//  - Bounded: Time=5, Int width 5. See ../README.md#model-limitations.
//
// C asserts covered: ibuf.c:72 and ibuf.h:86,94,112,194,207,215,224,225.

module ibuf

open util/ordering[Time]
open util/integer

sig Time {}

one sig Buf {
	rpos: Time -> one Int,
	wpos: Time -> one Int,
	cap: Time -> one Int
}

fun startCap: Int { 4 }
fun used[t: Time]: Int { minus[Buf.wpos[t], Buf.rpos[t]] }

pred init[t: Time] {
	Buf.rpos[t] = 0
	Buf.wpos[t] = 0
	Buf.cap[t] = 0
}

/** ibuf_reserve_slow(): defragment in place or grow (doubling). */
pred reserveSlow[t, t1: Time, size: Int] {
	size > 0 and size <= 8
	size > minus[Buf.cap[t], Buf.wpos[t]]
	(
		// In-place defragmentation: the unread bytes fit once moved.
		size <= minus[Buf.cap[t], used[t]] and
		Buf.cap[t1] = Buf.cap[t]
		or
		// Grow: double until it fits, preserving the unread bytes.
		size > minus[Buf.cap[t], used[t]] and
		Buf.cap[t1] >= plus[used[t], size] and
		Buf.cap[t1] >= mul[2, Buf.cap[t]] and
		Buf.cap[t1] >= startCap and Buf.cap[t1] <= 8
	)
	Buf.rpos[t1] = 0
	Buf.wpos[t1] = used[t]
}

/** ibuf_alloc(): append `size` bytes at `wpos`. */
pred alloc[t, t1: Time, size: Int] {
	size >= 0 and size <= 8
	size <= minus[Buf.cap[t], Buf.wpos[t]]
	Buf.rpos[t1] = Buf.rpos[t]
	Buf.wpos[t1] = plus[Buf.wpos[t], size]
	Buf.cap[t1] = Buf.cap[t]
}

/** ibuf_consume(): drop `size` bytes from the read end. */
pred consume[t, t1: Time, size: Int] {
	size >= 0 and size <= used[t]
	Buf.rpos[t1] = plus[Buf.rpos[t], size]
	Buf.wpos[t1] = Buf.wpos[t]
	Buf.cap[t1] = Buf.cap[t]
}

/** ibuf_discard(): drop `size` bytes from the write end. */
pred discard[t, t1: Time, size: Int] {
	size >= 0 and size <= used[t]
	Buf.rpos[t1] = Buf.rpos[t]
	Buf.wpos[t1] = minus[Buf.wpos[t], size]
	Buf.cap[t1] = Buf.cap[t]
}

/** ibuf_shrink(): reallocate to the smallest capacity holding `used`. */
pred shrink[t, t1: Time] {
	Buf.cap[t1] >= used[t]
	Buf.cap[t1] <= Buf.cap[t]
	Buf.rpos[t1] = 0
	Buf.wpos[t1] = used[t]
}

/** ibuf_reset(): forget the contents. */
pred reset[t, t1: Time] {
	Buf.rpos[t1] = 0
	Buf.wpos[t1] = 0
	Buf.cap[t1] = Buf.cap[t]
}

pred stutter[t, t1: Time] {
	Buf.rpos[t1] = Buf.rpos[t]
	Buf.wpos[t1] = Buf.wpos[t]
	Buf.cap[t1] = Buf.cap[t]
}

pred step[t, t1: Time] {
	(some n: Int | reserveSlow[t, t1, n]) or (some n: Int | alloc[t, t1, n]) or
	(some n: Int | consume[t, t1, n]) or (some n: Int | discard[t, t1, n]) or
	shrink[t, t1] or reset[t, t1] or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

pred inv[t: Time] {
	Buf.rpos[t] >= 0
	Buf.rpos[t] <= Buf.wpos[t]
	Buf.wpos[t] <= Buf.cap[t]
	Buf.cap[t] >= 0
	used[t] >= 0
}

check safety { all t: Time | inv[t] } for 5 but 6 int

/** A grow (reserveSlow that reallocates) preserves the unread bytes. */
check grow_preserves_used {
	all t: Time - last, n: Int |
		reserveSlow[t, next[t], n] and plus[used[t], n] > Buf.cap[t] implies
			used[next[t]] = used[t]
} for 5 but 6 int

/** consume/discard never drop more bytes than are buffered. */
check consume_bounds {
	all t: Time - last, n: Int |
		(consume[t, next[t], n] or discard[t, next[t], n]) implies n <= used[t]
} for 5 but 6 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Consume from the front, then reserve so the bytes are defragmented. */
run defragment_after_consume {
	some t: Time |
		(some n: Int | consume[t, next[t], n] and n > 0) and
		reserveSlow[next[t], next[next[t]], 1] and
		Buf.rpos[next[next[t]]] = 0
} for 5 but 6 int

/** Grow the buffer when the remaining bytes plus the request do not fit. */
run grow_doubles {
	some t: Time |
		reserveSlow[t, next[t], 8] and
		Buf.cap[next[t]] >= 8 and
		Buf.cap[next[t]] >= mul[2, Buf.cap[t]]
} for 5 but 6 int

/** Full buffer trace: grow, fill, consume, then defragment in place. */
run write_consume_defrag {
	reserveSlow[first, next[first], 2] and
	alloc[next[first], next[next[first]], 2] and
	consume[next[next[first]], next[next[next[first]]], 1] and
	reserveSlow[next[next[next[first]]], last, 3]
} for 5 but 6 int

/** consume() moves only the read cursor, leaving capacity and wpos. */
run consume_keeps_capacity {
	some n: Int |
		reserveSlow[first, next[first], 2] and
		alloc[next[first], next[next[first]], 2] and
		consume[next[next[first]], next[next[next[first]]], n] and
		n > 0 and
		Buf.cap[next[next[next[first]]]] = Buf.cap[next[next[first]]] and
		Buf.wpos[next[next[next[first]]]] = Buf.wpos[next[next[first]]] and
		Buf.rpos[next[next[next[first]]]] > Buf.rpos[next[next[first]]]
} for 5 but 6 int
