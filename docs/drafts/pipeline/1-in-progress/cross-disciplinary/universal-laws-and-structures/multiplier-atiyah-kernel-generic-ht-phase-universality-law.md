# Multiplier Atiyah-kernel generic-HT phase universality law

## Status

In progress — paper proof and Lean source complete; exact check and literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/AtiyahKernelProjectiveFinitenessUniversalityLaw.lean`
  - `multiplierAtiyahKernel_orderOne_universal_or_projectivelyFinite`
- `HTGeometry/ProjectiveDirectionalFullMeasure.lean`
  - `complexProjectiveDirectionalFiniteLaw_exactDichotomy`

## Universal law

For every compatible complex two-direction equivariant multiplier system, exactly one of the
following phase mechanisms applies:

1. some finite jet order is dependent in every projective direction; or
2. the projectivized multiplier-Atiyah kernel is finite, while complete-HT directions form a dense
   residual conull subset of every standard projective chart.

This identifies the Atiyah-zero directions as a finite exceptional subconfiguration inside every
noncollapsed projective law phase, while the ambient law space is generically completely
hypertranscendental in topology and measure.

## Paper proof

Apply the exact projective directional dichotomy. Its collapse branch is the first alternative. In
the noncollapse branch, apply the multiplier Atiyah-kernel dichotomy. Its order-one-universal
branch would itself witness finite-order collapse at `N = 1`, contradicting the noncollapse
hypothesis. Therefore the projectivized Atiyah kernel is finite. The remaining half of the exact
projective dichotomy gives density, residuality, and null complement in every standard chart.

## Lean status

Source complete in
`formal/GaloisForLFunctions/HTGeometry/MultiplierAtiyahKernelGenericHTPhaseUniversalityLaw.lean`.

Direct source check is deferred to final audit because the Atiyah-kernel provenance module lacks a
cached `.olean` artifact; no early `lake build` was run.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only; corpus search found
the finite Atiyah-kernel phase split and the dense-residual-conull projective HT phase split
separately, but no theorem identifying both simultaneously in the same noncollapsed law space.
