// common.als -- shared abstractions for the Tarantool/Small Alloy specs.
//
// LIMITATIONS:
//  - This module contains only generic structural helpers; it defines no
//    allocator state and no signatures of its own.
//  - All models use the *classic* Alloy encoding:
//      * every model declares `sig Time {}` and `open util/ordering[Time] as ord`;
//      * mutable C fields become `var` relations;
//      * a transition relates a pre-state `t` and the post-state `ord/next[t]`;
//      * `Init` constrains `ord/first`; operation predicates relate `t`/`next[t]`;
//      * `check`/`run` scopes set the number of `Time` atoms *exactly*, so the
//        trace length equals the scope given to `Time`.
//  - `Int` width and the number of objects are bounded per command, see the
//    `check`/`run` lines of each model.
//  - Higher-order helpers below quantify over `univ`; keep scopes small.

module common

// ---------------------------------------------------------------------------
// Intrusive singly-linked structures (stacks, lists, free lists).
// ---------------------------------------------------------------------------

/** `r` has no cycles (no atom reaches itself in one or more steps). */
pred isAcyclic[r: univ -> univ] {
	no iden & ^r
}

/** The set of atoms reachable from `roots` by zero or more `r` steps. */
fun reach[r: univ -> univ, roots: set univ]: set univ {
	roots.*r
}

/**
 * `r` is a well-formed intrusive linear list: `elems` is exactly the chain
 * starting at `head` (which may be empty), the chain is acyclic and
 * functional, `head` has no predecessor, and every other element has exactly
 * one predecessor. This models the `lf_lifo` / `rlist` / `slab_list` links.
 */
pred isLinearFrom[r: univ -> univ, head: lone univ, elems: set univ] {
	elems = reach[r, head]
	isAcyclic[r]
	all x: elems | lone x.r
	no head.~r & elems
	all x: elems - head | one x.~r & elems
}

/** Alias for `isLinearFrom`: a LIFO stack whose top is `top`. */
pred isStack[next: univ -> univ, top: lone univ, elems: set univ] {
	isLinearFrom[next, top, elems]
}

// ---------------------------------------------------------------------------
// Smoke tests: the helpers are consistent and admit the expected shapes.
// ---------------------------------------------------------------------------
// LIMITATIONS: this is a sanity check of the helpers only, not an allocator.

run helpers_smoke {
	some r: univ -> univ, h: univ |
		isLinearFrom[r, h, h.*r] and #(h.*r) = 2
} for 3

check empty_is_acyclic {
	isAcyclic[none -> none]
} for 2
