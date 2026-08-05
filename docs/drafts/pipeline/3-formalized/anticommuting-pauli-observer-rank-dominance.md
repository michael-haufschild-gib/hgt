# Anticommuting Pauli observer-rank dominance

- **ID:** `anticommuting-pauli-observer-rank-dominance`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / noncommuting exceptional-carrier exclusion
- **Date:** 2026-08-05
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/AnticommutingPauliObserverRankDominance.lean`
- **Paper proof:** `../2-fully-proven/anticommuting-pauli-observer-rank-dominance.md`

## Exact theorem

Every finite pairwise anticommuting family `A` of `n`-qubit Pauli words obeys

\[
 |A|\leq2n+1.
\]

For `n>=2` and locality order `q>=2`, its cardinality plus the exact
product-input observer rank is at most the number of nonidentity
weight-at-most-`q` Pauli directions:

\[
 |A|+2\sum_{k=1}^{q}{n\choose k}
 \leq\sum_{k=1}^{q}3^k{n\choose k}.
\]

Thus every canonical anticommuting spherical exact-return carrier has
transverse coefficient codimension at least observer rank.

## Formal declarations

- `Quantum.augmentedPauliVector_linearIndependent`;
- `Quantum.card_pairwiseAnticommutingPauli_le`;
- `Quantum.two_mul_add_one_le_commutingPauliCapacity`;
- `Quantum.pairwiseAnticommutingPauli_card_add_observerRank_le_pauliWeightCount`.

## Verification

Foreground target compilation passed with:

```text
lake env lean GaloisForLFunctions/HTGeometry/AnticommutingPauliObserverRankDominance.lean
```

Cached foreground compilation passed. Project lint passed. Axiom audit of
the load-bearing declarations reports only `propext`, `Classical.choice`,
and `Quot.sound`.

## Boundary

This closes pairwise anticommuting Pauli carriers only. It does not classify
arbitrary noncommuting Lie closures, nonlinear fast-forwardable components,
or circuit-selected unions, and therefore does not prove the parent
fixed-time shortcut-action conjecture.
