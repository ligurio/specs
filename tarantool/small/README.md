# Alloy specs for Tarantool/SMALL allocators

Formal [Alloy][alloy-site] specifications for the allocators of
[tarantool/small][small-repo] - a collection of specialized memory
allocators for small allocations.

Every `*.als` file models one allocator (or one aspect of it),
states invariants as `check` commands and concrete scenarios as
`run` commands. The models are intentionally abstract: they focus
on the algorithms and the accounting invariants, not on real
pointers or 64-bit arithmetic (see [Model limitations](#model-limitations)).

The models were written against
[tarantool/small][small-repo] at `1.1-172-g14ab53f` (commit
`14ab53f7fb8f44d70ed63fe5f19ce545c3579ed5`, `master`, 2026-05-07).
The `file:line` references in the `LIMITATIONS` headers and in
this README point to that revision.

## Scope

The following facilities are covered:

| Allocator | C sources | Alloy model |
|---|---|---|
| `quota` | `include/small/quota.h` | `quota.als` |
| `slab_arena` | `small/slab_arena.c`, `include/small/slab_arena.h` | `slab_arena.als` |
| `slab_cache` (buddy) | `small/slab_cache.c`, `include/small/slab_cache.h` | `slab_cache.als` |
| `mempool` | `small/mempool.c`, `include/small/mempool.h` | `mempool.als` |
| `small_class` | `small/small_class.c`, `include/small/small_class.h` | `small_class.als` |
| `small` | `small/small.c`, `include/small/small.h` | `small.als` |
| `region` | `small/region.c`, `include/small/region.h` | `region.als` |
| `lsregion` | `small/lsregion.c`, `include/small/lsregion.h` | `lsregion.als` |
| `matras` | `small/matras.c`, `include/small/matras.h` | `matras.als` |
| `obuf` | `small/obuf.c`, `include/small/obuf.h` | `obuf.als` |
| `ibuf` | `small/ibuf.c`, `include/small/ibuf.h` | `ibuf.als` |
| `quota_lessor` | `include/small/quota_lessor.h` | `quota_lessor.als` |
| `static` | `include/small/static.h` | `static.als` |
| integration | all of the above | `system.als` |

## How to run

Requirements: `python3`, `make` and Alloy Analyzer.

```sh
make check
make clean
```

The `Makefile` runs `alloy exec -f -o TMP -t none MODEL.als` for
every model, renames the generated `receipt.json` to `MODEL.json`
and calls `check.py` on all receipts. A `check` succeeds when no
counterexample is found, a `run` succeeds when an instance is
found (an `expect` clause, if present, overrides this). `check.py`
prints a verdict per command and per receipt and exits `0` when
everything passed, `1` when a command failed and `2` on a
usage/read error.

### Global abstractions

- **No real arithmetic** Sizes, addresses and counters are small
  Alloy `Int`s (`bitwidth` 6–8) or abstract atoms, not
  `size_t`/`intptr_t`. Any result about a concrete constant (e.g.
  `4 MB`) is symbolic.
- **No pointers** Slabs/blocks are abstract atoms. Alignment,
  pointer tagging, `mmap`/`munmap`, `madvise`, page sizes and
  address-space layout are not modeled.
- **Bounded number of objects** Every scope (number of slabs,
  pools, groups, extents, threads, time steps) is bounded. A
  `check` that reports "no counterexample" means *no
  counterexample within the used bounds*, it is **not** a proof.
  The used scope and bit width are written in each `.als`.
- **No floating point** `small_class` uses `float` for
  `actual_factor`; floating-point rounding is not modeled.
- **No ASAN** `*_asan` implementations (`small/*_asan.c`,
  `include/small/*_asan.h`) are out of scope.
- **Threads** are modeled only for facilities documented as
  thread-safe (`quota`, `slab_arena`) and only with 2 threads.

### Bounded semantics

The Alloy Analyzer searches for counterexamples up to a finite
scope. Therefore:

- `check` results are "bounded correctness": an invariant holds
  for all executions that fit the scope, not for all executions.
- `run` results are concrete bounded traces used to
  illustrate/validate the intended behavior (e.g. regression
  scenarios taken from `small/test/*.c`).
- Where a property is expected to be *unbounded*, it is a
  documented limitation, not a verified theorem.

### Per-module limitations

This table is filled in as models are added. Each `*.als` repeats
its own row in its `LIMITATIONS` header.

| Model | Abstracted / omitted |
|---|---|
| `common.als` | shared helpers only; no allocator state |
| `quota.als` | units abstracted to small ints; atomic CAS treated as atomic step |
| `slab_arena.als` | `mmap`/prealloc as abstract slab pool; ABA counter abstracted |
| `slab_cache.als` | addresses as ordered atoms; `buddy` as a relation, not XOR; no magic constant |
| `mempool.als` | objSize=1, objCount=4; RB tree `hot_slabs` abstracted to "some hot slab"; `free_list`/`free_offset` as `carved`/`live` counts |
| `small_class.als` | fixed instance (gr=2, factor=1.2, min=12); `float` not modeled; sizes 0..31, classes 0..11 |
| `small.als` | one group of 3 pools (obj 2/4/8), waste_max=8, cap 4, 7 objects; `slab_cache`/`mempool` abstracted |
| `region.als` | 3 equal slabs, fixed order; byte contents abstract; callbacks omitted; `region_join`/aligned padding omitted |
| `lsregion.als` | 3 slabs, fixed order, capacity 2; cached-slab **reuse not modeled**; `to_iovec`/savepoints omitted |
| `matras.als` | extent tree abstracted to `Id.phys`; 4 ids/4 blocks; `alloc_range`/`dealloc_range`/`touch_reserve` and extent accounting omitted |
| `obuf.als` | 3 iovec slots, start capacity 1; slab cache and `obuf_dup`/`obuf_destroy` omitted |
| `ibuf.als` | slab cache abstracted; cursors as offsets; capacity ≤ 8; `shrink` as any realloc fitting `used` |
| `quota_lessor.als` | source quota abstracted; `minUse`=2 and hysteresis scaled down; `use/=2` retry omitted |
| `static.als` | size=8; no thread-locality; aligned variants omitted |
| `system.als` | **not** a composition of the other models: two abstract pools + capacity; slabs/arena omitted |

### Known gaps

- `mempool`: the red-black tree shape of `hot_slabs` is not
  modeled; only its observable contract (a hot slab can be chosen)
  is.
- `slab_arena`: lock-freedom/liveness is not proven; only safety
  of the abstracted state and the ABA counter itself are not
  modeled.
- `lsregion`: because the order is fixed, a slab kept in `cached`
  is not reused as a new tail; `lsregion_to_iovec` and savepoints
  are not modeled.
- `matras`: the 3-level `root/n1/n2/n3` translation, lazy extent
  creation and the `extent_count` / `read_view_extent_count`
  accounting are not modeled; the read view is a two-atom
  abstraction.
- `ibuf`/`obuf`: capacity in bytes is abstracted; no `slab_order`
  rounding.
- `system.als` checks the end-to-end accounting only; it does not
  compose the actual `small`/`mempool`/`slab_cache`/`slab_arena`
  states.
- No model checks integer overflow at real widths; `--nooverflow`
  is not used.
- Thread interleavings for the thread-safe tiers (`quota`,
  `slab_arena`) are modeled as atomic steps; real
  concurrency/refinement is not verified.

### Mapping C to Alloy

Each model documents its mapping in the file header. As a rule:

- A C struct becomes an Alloy `sig` (for identities) plus `var`
  fields (for mutable state);
- A C operation becomes an Alloy predicate over `Time` (pre-state
  `t`, post-state `next[t]`, classic `util/ordering[Time]`
  encoding);
- A C `assert` becomes an Alloy `check` (and a `run` for the
  corresponding scenario).

[alloy-site]: https://alloytools.org/
[small-repo]: https://github.com/tarantool/small
