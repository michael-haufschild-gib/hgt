# Prime-collision coordinate-fusion escape universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/PrimeCollisionConvolution.lean`
  - `primePowerLayerProjection_mul_columns`
- `HTGeometry/PrimeValuationCoordinateFusionCompletion.lean`
  - `cofiniteTailDenseOn_primeResidueValuationUpperEndCoordinateVacuumCreationLaw`

## Universal law

Prime-valuation fusion is not an auxiliary product: it is the same-prime layer projection of
native Dirichlet convolution. Every finite coordinate-relative valuation prefix contains a
depth-`n` carrier and neutral depth-zero carrier, but the same-prime component of their native
product is exactly the next carrier. That carrier is relatively differentially independent and
lies outside the prefix field, so no finite prefix is closed under its native collision law.

## Lean status

Formalized in
`formal/GaloisForLFunctions/HTGeometry/PrimeCollisionCoordinateFusionEscapeUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/HTGeometry/PrimeCollisionCoordinateFusionEscapeUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
