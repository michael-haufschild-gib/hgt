# Relative cone normalization of the arithmetic Euler count

- **ID:** RIAC-relative-cone
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md), relative localization
- **Statement:** Compare the actual prime-product complex with its canonical cone pair, including singular relative homology and the isolated-prime correction.

## Candidate

For `N≥1`, the full prime complex `K_N` has ordinary Euler characteristic
`1−M(N)`.
The canonical cone pair `(CK_N,K_N)` therefore suggests relative Euler
characteristic `M(N)`. At `N≥4`, using the connected core instead leaves `M(N)+P_N`,
where `P_N` counts primes in `(N/2,N]`. The cone is determined by the complex;
no cells are chosen from the value of `M(N)`.

The precise target is an actual pair comparison, with the canonical relative
chain quotient, finite homology type, shifted reduced homology and cutoff
naturality. The generic singular relative quotient and Euler subtraction
already exist in `DifferentialGeometry.Topology.Homology.Relative`.
HHAC supplies the exact arithmetic face partition and its sign convention.

## Limits and discriminating test

A cone pair changes the ambient space. It does not construct a pair
`(core,A)`, signed fixed-point indices, modular action or cancellation bound.
An Euler subtraction formula alone would only repackage the known Mertens
identity. The useful output would be the canonical chain comparison and its
compatibility with a separately constructed arithmetic action.

No cone comparison or new relative-homology theorem is presently formalized.
