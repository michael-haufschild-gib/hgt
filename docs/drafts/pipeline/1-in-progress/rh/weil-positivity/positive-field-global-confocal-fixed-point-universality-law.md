# Positive-field global confocal fixed-point universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `RHTower/PositiveFieldBicompletionLaw.lean`
  - `localPositiveScaleField_selects_maximalConfocalHull`
  - `localPositiveScaleField_agrees_iff_source_and_maximalHull_eq`
- `HTGeometry/ConfocalGlobalSupportTransform.lean`
  - `isLUB_confocalGlobalEnvelope`
  - `confocalGlobalDefect_isGreatest_fixedPoint`
- `HTGeometry/ConfocalEnvelopeHull.lean`
  - `isConfocalEnvelopeOn_confocalLorentzLift_image`

The RHT theorem recovers equality of exterior confocal upper fields from equality on one local
positive scale window. The HT theorem independently identifies each global defect as the greatest
nonnegative fixed point of a source-specific nonlinear null-support operator.

## Universal law

For two admissible bounded atomic presentations, equality of the positive Bernstein observation on
any nonempty open scale interval forces equality of their complete pointed moment sources. At every
exterior radius, their possibly different null-support operators then share exactly one observed
greatest nonnegative fixed-point value: the common global confocal defect.

## Lean status

Formalized in
`formal/GaloisForLFunctions/RHTower/PositiveFieldGlobalConfocalFixedPointUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/RHTower/PositiveFieldGlobalConfocalFixedPointUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
