# Specs

Formal specifications of distributed protocols and data structures,
written in different modeling languages and checked with different
model checkers.

## Models

### Two-phase commit

[spin/2pc.pml](spin/2pc.pml) models two-phase commit, a protocol
that ensures atomic commitment of distributed transactions. A
manager process drives `NPROC` resource-manager processes through
a start/vote/decision round; the model asserts that every process
observes the common decision.

### Tarantool's SMALL

[tarantool/small](tarantool/small/) contains Alloy specifications
for the allocators of [SMALL][small-repo] - specialized memory
allocators for small allocations. The full list of models, scope,
and limitations is in the [README](tarantool/small/README.md).

[small-repo]: https://github.com/tarantool/small
