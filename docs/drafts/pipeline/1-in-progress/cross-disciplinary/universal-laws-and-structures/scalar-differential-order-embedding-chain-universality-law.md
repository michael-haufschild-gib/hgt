# Scalar differential-order embedding-chain universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/ScalarDifferentialRationalOrder.lean`
  - `HasScalarDifferentialOrder.map`
- `HTGeometry/DifferentialClockEmbeddingCovariance.lean`
  - `jetObservableField_map_algHom`
- `HTGeometry/DifferentialClockEmbeddingComposition.lean`
  - `differentialAlgHom_comp_preserves_derivation`
- `HTGeometry/DifferentialClockResolutionRigidity.lean`
  - `jetObservableField_map_algHom_eq_iff_resolution_eq`

## Universal law

Exact scalar differential order is preserved by a derivation-compatible field embedding into an
arbitrary different codomain, extending the corpus endomorphism theorem. Along every two-step
embedding chain, every scalar observable keeps its exact order and a transported finite clock slice
equals a target slice exactly when the numerical resolution index is unchanged.

## Lean status

Formalized in
`formal/GaloisForLFunctions/HTGeometry/ScalarDifferentialOrderEmbeddingChainUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/HTGeometry/ScalarDifferentialOrderEmbeddingChainUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
