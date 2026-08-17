# Context anomaly rank law

Stage: 3-formalized

Status: `[LITERATURE] [PAPER-PROVED] [LEAN PROVED] [STRENGTHENED]`

Source: Theorem 5.4 of *Locally Quantum, Globally Non-Hilbertizable* (Zenodo 21982163).

## Exact claim

An `n`-context kernel with internal dimension `d` acts on dimension `nd`.  If a selected
`k`-context sector of dimension `kd` is nonnegative, every subspace on which its quadratic form is
strictly negative has dimension at most

```text
(n-k)d.
```

The statement is stronger than an eigenvalue-list formulation: it applies to every complex
negative-definite subspace and needs no eigenvalue ordering or diagonalization.

## Proof

A strictly negative subspace and a nonnegative subspace intersect only at zero.  Their direct sum
therefore has dimension equal to the sum of their dimensions, bounded by ambient dimension `nd`.
Subtracting the certified `kd` dimensions gives the result.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/ContextAnomalyRankLaw.lean`, declarations
`complexNegativeSector_finrank_add_nonnegativeSector_le` and
`ContextAnomalyRankDatum.negativeSector_finrank_le`.  Context bound `k<=n`, sector rank, and sign
certificates are intrinsic fields of `ContextAnomalyRankDatum`; headline theorem has no external
premises and introduces no axioms.
