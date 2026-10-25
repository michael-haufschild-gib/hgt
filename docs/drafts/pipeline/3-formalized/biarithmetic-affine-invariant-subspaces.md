# Invariant subspaces of the natural finite affine representation

- **ID:** biarithmetic-affine-invariant-subspaces
- **Stage:** 3-formalized
- **Type:** CLASSICAL LINEAR ALGEBRA CALIBRATION
- **Parent:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md)
- **Statement:** The invariant subspaces of the natural absorbing affine representation on `span(e_0,...,e_N)` are precisely the tails `span(e_m,...,e_N)`, including zero at `m=N+1`. Invariance under the successor alone already suffices.

## Paper proof

Let `U e_j=e_(j+1)`, with cells beyond `N` zero. Every tail is preserved by every positive affine map, since `a*j+b>=j`.

Conversely let `W` be successor invariant. If `W=0`, take `m=N+1`. Otherwise choose the least index `m` at which some vector of `W` has nonzero coefficient, and choose such a vector `v`. Every vector in `W` vanishes below `m`, so `W` is contained in the `m`-tail.

Descending induction on `j=N,...,m` shows `e_j` belongs to `W`. The vector `U^(j-m)v` belongs to `W`, vanishes below `j`, and has coefficient `v_m != 0` at `j`. Its coefficients above `j` can be subtracted using the already established cells in `W`. Division by `v_m` then gives `e_j`. Therefore the whole tail belongs to `W` and equality follows.

The threshold is unique: if `m<n<=N+1`, the cell `e_m` belongs to the `m`-tail and not the `n`-tail. Thus the submodule lattice is a chain of exactly `N+2` terms, and the natural affine representation is indecomposable. Each successive quotient is one-dimensional. This is the usual single nilpotent Jordan-block argument applied to the source-defined absorbing action, not a novelty claim for uniseriality.

## Scope

This classifies subrepresentations of the natural cell module, not all representations of its finite image semigroup. Scalar common commutant does not imply irreducibility: the tails give all counterexamples. The result supplies structural Class III geometry but does not distinguish coefficient sources or prove cancellation.

## Verification

- [x] Dependency-closed paper argument and classical status identified.
- [x] Lean tail submodules and exact invariant-subspace classification.
- [x] Uniqueness, chain law, and indecomposability in Lean.
- [x] Direct source check and transitive axiom audit.

`AffineInvariantSubspaces.lean` passed its direct check. Audits of
`horizon_successor_submodules`, `horizon_affine_submodules`, `horizonTail_injective`,
`horizonInvariantSubspaceEquiv`, `card_horizonInvariantSubspaces`, and
`horizon_affine_indecomposable` report only `propext`, `Classical.choice`, and `Quot.sound`.
The umbrella imports the leaf; no umbrella build was run.
