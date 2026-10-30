# Conductor scale controls completed energy

- **ID:** conductor-scale-controls-completed-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For the tilted spline, every `c>0` and positive integer `m` satisfy `E_m(c)≥δ(m/φ(m)) min(1,(m/c)^7)`, where `δ=2 tiltedSplineTailConstant/∫φ²>0`.

## Proof

Let `T(z)=∫_(t>z)|φ̂(2πt)|²dt`. The proved nonnegative coprime-tail expansion contains its `a=1` term, hence

`E_m(c)≥(2/M)(m/φ(m))T(c/m)`.

For `c/m≥1`, the proved tilted-spline tail bound gives `T(c/m)≥tiltedSplineTailConstant(m/c)^7`. For `c/m≤1`, monotonicity gives `T(c/m)≥T(1)≥tiltedSplineTailConstant`. Combining the two cases proves the statement. In particular `m≥c` gives `E_m(c)≥δ m/φ(m)≥δ`.

## Consequence and boundary

Degeneration of the diagonal energies is confined to conductors below the overlap scale. This does not control the complete matrix on their orthogonal complement or supply a growing-conductor residual estimate.

## Lean certificate

[ConductorScaleControlsTheCompletedEnergy.lean](../../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/ConductorScaleControlsTheCompletedEnergy.lean)
proves the scaled-tail floor, the stated conductor-scale bound, and the common positive floor for `m≥c`.
The focused `lake --old env lean` check passed without warnings. All three transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
