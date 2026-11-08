# Arithmetic prime-vertex exit pairs and signed singular indices

- **ID:** RIAC-prime-exit-indices
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION
- **Source:** [Signed localization](../1-in-progress/riac-prime-vertex-signed-localization.md)

## Actual objects

On the original prime-product realization, normalize coordinates by
`F(x)_p=(p+1)x_p/Σ_q(q+1)x_q`. The map preserves every face and cutoff,
is homotopic to identity, and fixes exactly the prime vertices.

The projective chart at `p` has coordinates `y_q=x_q/x_p` for `q≠p`.
The flow multiplies them by `exp(t(log(q+1)−log(p+1)))`. Bound both upper
and lower coordinate mass by one. This gives a compact block with apex
as its only full invariant orbit, in its interior. Its compact forward
exit has upper mass one. Every escaping orbit crosses that exit;
positive exit trajectories leave immediately. The block contracts to
the apex, and deleting lower coordinates deformation retracts its exit
onto the actual upper-link realization.

## Signed arithmetic theorem

Define `ι_p(N)=χ(H_*(B_p,E_p;ℚ))` using actual relative singular homology.
For an arithmetic prime vertex with `p≤N≤p³`, the upper link has no edges:
two larger primes would have `pqr>p³`. Thus

`ι_p(N)=1−#{q prime : p<q, pq≤N}`.

In finite ambient `Fin(B+3)`, the count uses precisely those labels;
`B≥N` includes every arithmetic neighbour. These indices are unbounded
below. If `2^k≤p` and `N=p³`, each Bertrand interval
`(2^j p,2^(j+1)p]`, `j<k`, supplies a distinct exit component below `p²`.
Hence `ι_p(p³)≤1−k`.

## Lean declarations

- `PrimeVertexDynamics.lean`: `primeVertexMapHomotopy`, `primeVertexMap_fixed_iff`.
- `PrimeVertexLocalFlow.lean`: `primeVertexChart`, `isCompact_primeVertexBlock`,
  `primeVertexBlock_maximal_invariant`, `primeVertexBlock_exit_crossing`,
  `primeExitLinkHomotopyEquiv`, `primeVertexBlock_contractible`.
- `PrimeVertexSingularIndex.lean`: `primeVertexRelativeIndex_cubic`,
  `primeVertexRelativeIndex_unbounded_below`.

All three production files passed direct Lean checks. Their capstone axiom
audits use only `propext`, `Classical.choice` and `Quot.sound`.

## Boundary

This constructs signed local singular-homology indices independently of
`M(N)` and `Q`. It supplies no cancellation bound, product-formula height
or zero-dependent invariant. The all-vertex Mertens comparison and exact
time-one comparison with `F` remain on the active localization card.
