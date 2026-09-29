// static.als -- model of the thread-local static buffer (include/small/static.h).
//
// `static_storage_pos` walks a fixed BSS buffer. `static_reserve(size)` returns
// NULL when `size` exceeds the buffer; otherwise, if the request does not fit
// before the end, the position wraps to 0 (the buffer is recycled). `static_alloc`
// reserves and advances the position.
//
// LIMITATIONS:
//  - `SMALL_STATIC_SIZE` is 8 units; only the position is modeled, not the
//    bytes or the thread-locality of the buffer.
//  - `static_aligned_*` (alignment padding) is not modeled.
//  - Bounded: Time=5, Int width 5. See ../README.md#model-limitations.
//
// C asserts covered: the bounds logic of static_reserve/static_alloc.

module static

open util/ordering[Time]
open util/integer

sig Time {}

one sig Buf {
	pos: Time -> one Int
}

fun SIZE: Int { 8 }

pred init[t: Time] { Buf.pos[t] = 0 }

/** static_alloc(size): reserve and advance, wrapping or failing. */
pred allocStep[t, t1: Time, size: Int, ret: Int] {
	size >= 0
	(
		// Too big for the whole buffer: always NULL, position unchanged.
		(size > SIZE and ret = 0 and Buf.pos[t1] = Buf.pos[t])
		or
		// Does not fit before the end: recycle from 0.
		(size <= SIZE and size > minus[SIZE, Buf.pos[t]] and
		 ret = size and Buf.pos[t1] = size)
		or
		// Fits: advance.
		(size <= SIZE and size <= minus[SIZE, Buf.pos[t]] and
		 ret = size and Buf.pos[t1] = plus[Buf.pos[t], size])
	)
}

/** static_reset(): rewind to the start. */
pred reset[t, t1: Time] { Buf.pos[t1] = 0 }

pred stutter[t, t1: Time] { Buf.pos[t1] = Buf.pos[t] }

pred step[t, t1: Time] {
	(some s, r: Int | allocStep[t, t1, s, r]) or reset[t, t1] or stutter[t, t1]
}

fact trace {
	init[first]
	all t: Time - last | step[t, next[t]]
}

pred inv[t: Time] {
	Buf.pos[t] >= 0 and Buf.pos[t] <= SIZE
}

check safety { all t: Time | inv[t] } for 5 but 5 int

/** An allocation larger than the buffer always fails and changes nothing. */
check oversized_alloc_fails {
	all t: Time - last, s, r: Int |
		s > SIZE and allocStep[t, next[t], s, r] implies
			(r = 0 and Buf.pos[next[t]] = Buf.pos[t])
} for 5 but 5 int

/** A successful allocation leaves the position within bounds. */
check alloc_stays_in_bounds {
	all t: Time - last |
		Buf.pos[next[t]] >= 0 and Buf.pos[next[t]] <= SIZE
} for 5 but 5 int

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/** Two allocations that together exceed the buffer wrap the position. */
run wrap_around {
	some t: Time, a, b: Int |
		allocStep[t, next[t], a, a] and
		allocStep[next[t], next[next[t]], b, b] and
		Buf.pos[next[t]] = plus[Buf.pos[t], a] and
		Buf.pos[next[next[t]]] = b and
		b > minus[SIZE, Buf.pos[next[t]]]
} for 5 but 5 int

/** A single oversized request fails. */
run oversized_request {
	some t: Time |
		some s: Int | s > SIZE and allocStep[t, next[t], s, 0]
} for 4 but 5 int

/** Full buffer trace: fill, wrap on the next allocation, then reset. */
run buffer_lifecycle {
	allocStep[first, next[first], 6, 6] and
	allocStep[next[first], next[next[first]], 3, 3] and
	reset[next[next[first]], next[next[next[first]]]] and
	stutter[next[next[next[first]]], last]
} for 5 but 5 int

/** An oversized allocation fails and leaves the position untouched. */
run oversized_keeps_pos {
	allocStep[first, next[first], 9, 0] and
	Buf.pos[next[first]] = Buf.pos[first]
} for 4 but 5 int
