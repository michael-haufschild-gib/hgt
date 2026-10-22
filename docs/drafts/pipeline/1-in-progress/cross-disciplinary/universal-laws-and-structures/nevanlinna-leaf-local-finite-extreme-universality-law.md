# Nevanlinna leaf local-finite extreme universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/FiberFinite.lean`
  - `finite_finiteDenominatorFiber_inter`
- `HTGeometry/LeafUniqueness.lean`
  - `nevLeaf_finite_carried`
- `HTGeometry/LeafExtreme.lean`
  - `nevLeaf_of_half_mixture`
- Mathlib measure restriction identities already imported by `HTGeometry/FiberClosed.lean`

## Universal law

Every compact observation of a canonical finite-parameter Nevanlinna leaf is exactly its
restriction to a finite denominator-fibre section. Nevertheless, any half-half decomposition into
representing probability measures with the same complete moments collapses globally to the leaf.
Thus global extremality coexists with exact finite tomography on every compact window.

## Lean status

Formalized in
`formal/GaloisForLFunctions/HTGeometry/NevLeafLocalFiniteExtremeUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/HTGeometry/NevLeafLocalFiniteExtremeUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
