# Arithmetic homotopy types of prime exits

- **ID:** RIAC-prime-exit-bouquet
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION
- **Source:** [Signed localization](../3-formalized/riac-prime-vertex-signed-localization.md)

The actual homotopy type of every local exit is classified, beyond its signed
Euler characteristic. At a prime vertex `p`, if no larger prime `q` has `pq≤N`, the exit is empty.
Otherwise let `a` be its least prime neighbour. The exit model is
a wedge of spheres indexed by prime supports `S` satisfying

`all q∈S exceed a`, `p·∏S≤N<p·a·∏S`,

with sphere dimension `|S|−1`. The finite ambient realization retains
exactly its available prime labels; ambient bound `B≥N` includes all of them.

The star of `a` contracts. For a complementary face, replace any removed
vertex `q` by `a≤q`: its product cannot increase. Thus every proper subface
lies in that star, and the existing geometric cone-star bouquet theorem
applies. Composing with the constructed exit-to-link equivalence gives the
actual exit model. Minimal-neighbour selection and the empty case are proved, so no geometric
premise remains assumed in the classification.

[PrimeExitBouquet.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeExitBouquet.lean)
constructs `primeExitBouquetEquiv`, proves the unconditional classification
`primeExit_bouquet_or_empty`, and identifies the sphere labels by
`primeExit_bouquet_window`. The production file passed its direct Lean check;
four capstone audits use only `propext`, `Classical.choice` and `Quot.sound`.

This refines the local objects; it supplies no cancellation estimate or
zero-dependent completion. The existing [cone-star bouquet construction](bjorner-wedge-realization.md)
is the geometric input. The arithmetic contribution identifies the actual
local exits and their exact multiplicative windows.
