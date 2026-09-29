// small_class.als -- model of the size-class evaluator (`struct small_class`,
// small/small_class.c, include/small/small_class.h).
//
// `small_class_calc_offset_by_size` maps a requested size to a class index and
// `small_class_calc_size_by_offset` maps a class index back to the class size.
// Class sizes grow linearly up to `effective_size` classes and exponentially
// afterwards; class sizes are rounded up to `granularity`.
//
// LIMITATIONS:
//  - The concrete `small_class` instance is fixed to the parameters used by
//    test/small_class.c::test_class: granularity=2, desired_factor=1.2,
//    min_alloc=12. This yields ignore_bits=1, effective_bits=2,
//    effective_size=4, size_shift=10.
//  - Floating point (`actual_factor`, `log`, rounding of `effective_bits`) is
//    not modeled; the integer fields are given directly.
//  - Integer operations (`>>`, `&`, `|`) are modeled with `div`/`rem`/arith.
//  - The domain is bounded: 0 <= size <= 31, 0 <= class < 12, Int width 6.
//  - See ../README.md#model-limitations.
//
// C asserts covered: small_class.c:41-46 (creation preconditions) and the
// size<->class round-trip exercised by small_class.c:52-61,115-124.

module small_class

// Fixed integer fields of the concrete instance.
fun granularity: Int { 2 }
fun ignoreBits: Int { 1 }
fun effBits: Int { 2 }
fun effSize: Int { 4 }
fun effMask: Int { 3 }
fun sizeShift: Int { 10 }
fun shiftPlus1: Int { 11 }

fun pow2[n: Int]: Int {
	n = 0 => 1 else n = 1 => 2 else n = 2 => 4 else n = 3 => 8 else 16
}

/** Position of the most significant bit (0-based); argument must be > 0. */
fun fls[v: Int]: Int {
	v < 2 => 0 else v < 4 => 1 else v < 8 => 2 else v < 16 => 3 else 4
}

/** small_class_calc_offset_by_size(): size -> class. */
fun offsetBySize[size0: Int]: Int {
	// Unsigned underflow: size < size_shift + 1 yields zero.
	let sh = (size0 < shiftPlus1 => 0 else minus[size0, shiftPlus1]) |
	let s = div[sh, pow2[ignoreBits]] |
		(s < effSize => s
		 else let lg = fls[div[s, effSize]] |
			plus[div[s, pow2[lg]], mul[lg, effSize]])
}

/** small_class_calc_size_by_offset(): class -> class size. */
fun sizeByOffset[cls: Int]: Int {
	let c = plus[cls, 1] |
	let linear0 = rem[c, effSize] |
	let lg0 = div[c, effSize] |
	let linear = (lg0 = 0 => linear0 else plus[linear0, effSize]) |
	let lg = (lg0 = 0 => 0 else minus[lg0, 1]) |
		plus[sizeShift, mul[linear, pow2[plus[lg, ignoreBits]]]]
}

// ---------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------

/** Round-up: the class of `size` is the smallest class size >= size. */
check round_up {
	all size: Int |
		0 <= size and size <= 31 =>
			sizeByOffset[offsetBySize[size]] >= size
} for 6 but 8 int

/** Stability: re-classifying a class size yields the same class. */
check class_stable {
	all size: Int |
		0 <= size and size <= 31 =>
			offsetBySize[sizeByOffset[offsetBySize[size]]] = offsetBySize[size]
} for 6 but 8 int

/** The size->class map is monotone. */
check class_monotone {
	all s1, s2: Int |
		0 <= s1 and s1 <= s2 and s2 <= 31 =>
			offsetBySize[s1] <= offsetBySize[s2]
} for 6 but 8 int

/** Class sizes are strictly increasing. */
check class_size_monotone {
	all c: Int |
		0 <= c and c < 11 =>
			sizeByOffset[c] < sizeByOffset[plus[c, 1]]
} for 6 but 8 int

/** Every class size is a multiple of granularity. */
check class_size_aligned {
	all c: Int |
		0 <= c and c < 12 =>
			rem[sizeByOffset[c], granularity] = 0
} for 6 but 8 int

/** The first class size equals the minimal allocation. */
check first_class_size {
	sizeByOffset[0] = 12
} for 6 but 8 int

// ---------------------------------------------------------------------------
// Scenario: class boundaries as in test/small_class.c::test_class.
// ---------------------------------------------------------------------------

run class_boundaries {
	some size: Int |
		0 <= size and size <= 31 and
		offsetBySize[size] = 3 and
		size = plus[sizeByOffset[2], 1]
} for 6 but 8 int
