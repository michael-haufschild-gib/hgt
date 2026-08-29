# Theta-Cusp C5 Lowest-Weight Anomaly

- **ID:** CLG-TTF-C5-lowest-weight-anomaly
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Module:** `GaloisForLFunctions.HTGeometry.ExactCompletedC5LowestWeightAnomaly`

## Result

At zero-scale algebraic seam `U=B=0`, `Q=-3/8`, exact source-positive physical field equals hidden
`sl₂F` after evaluation on every polynomial observable. Completed C5 orientation vanishes there,
but its exact corrected slope is

`(-3/8)^6 * modularThetaC5FixedActionSeamPolynomial(0)`.

Fixed-action polynomial has nonzero negative constant term. Covariant C5 Lie law therefore gives
exact, strictly positive lowering derivative

`sl₂F(Ω_clear) = (-3/8)^5 * modularThetaC5FixedActionSeamPolynomial(0) > 0`

at this seam. Hence `Ω_clear` is not lowest weight and genuinely depends on adapted clock coordinate
`b`.

## RH consequence

This kills reduction

`sl₂F(Ω_clear)=0`
→ `Ω_clear=r*P(r,k)`
→ `two-variable physical sign classification`
→ `global completed C5 orientation`
→ `direct-J seam closure`
→ `CLG/TTF or Weil positivity`
→ `RH`.

Positive survivor is exact C5 lowering anomaly. Any compact incidence proof must retain `b` dynamics
or introduce invariant carrying same fixed-action charge; `(r,k)` alone cannot determine orientation.

## Lean audit

- `lake env lean GaloisForLFunctions/HTGeometry/ExactCompletedC5LowestWeightAnomaly.lean`: pass.
- `lake build GaloisForLFunctions.HTGeometry.ExactCompletedC5LowestWeightAnomaly`: pass.
- Both capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Global lint reaches new module through `HTGeometry` umbrella; it remains red only on unrelated,
  pre-existing/concurrent unreachable modules listed by lint.
- Proof uses structural chart transport and covariant Lie law; no C5 full expansion and no heartbeat
  override.
