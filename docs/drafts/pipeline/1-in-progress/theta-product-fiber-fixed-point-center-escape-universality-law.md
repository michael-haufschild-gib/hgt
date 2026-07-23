# Theta product-fibre fixed-point centre-escape universality law

## Status

In progress — paper proof and Lean source complete; exact check deferred to final module build because
the existing transitive cache lacks `XiCTaylorThetaTailPhasePotentialSeam.olean`.

## Theorem-first provenance

- `RHTower/ThetaFixedPointMomentProductFiberUniversalityLaw.lean`
  - `thetaProductFiberActualPhaseCurrent_zero_eq_endpointGibbsSum`
- `RHTower/XiCTaylorThetaTailCompletedValuationReflection.lean`
  - `thetaProductFiberActualPhaseCurrent_zero_pos`
- `RHTower/XiCTaylorThetaTailProductFiberCenteredSeamNoGo.lean`
  - `tendsto_thetaProductFiberCenteredCorrectedPhaseSeamCurrent_atTop_actual`

## Universal law

For every positive product fibre, sending the common corrected-seam centre to infinity converges to
the explicit fixed-point endpoint Gibbs sum. That limit is strictly positive. Centre escape therefore
removes the tail penalty but cannot erase the arithmetic fixed-point current.

## Lean status

Lean source is in
`formal/GaloisForLFunctions/RHTower/ThetaProductFiberFixedPointCenterEscapeUniversalityLaw.lean`.
Final exact and module checks remain pending under the mandated final audit.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
