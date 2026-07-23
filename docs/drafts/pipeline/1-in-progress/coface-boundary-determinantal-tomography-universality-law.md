# Coface-boundary determinantal tomography universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/CofaceBoundaryReconstruction.lean`
  - `cofaceBoundaryMaximalMinorIdeal_eq_veroneseIdeal`
- `HTGeometry/SquarefreeVeronesePairDetection.lean`
  - `mem_veroneseIdeal_iff_every_pair_meets_support`
- `HTGeometry/SourceConstraintHeight.lean`
  - `veroneseIdeal_hasExactSquarefreeConstraintHeight`

## Universal law

At every order `r`, the ideal reconstructed from maximal minors of the weighted coface boundary has
exact squarefree source height `r`. Membership in that determinantal ideal is equivalent to every
nonzero monomial support meeting every two-coordinate face. Thus pair tomography detects the full
determinantal boundary exactly at its first possible source width.

## Lean status

Formalized in
`formal/GaloisForLFunctions/HTGeometry/CofaceBoundaryDeterminantalTomographyUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/HTGeometry/CofaceBoundaryDeterminantalTomographyUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
