# Gamma integer-shift intensity-blindness universality law

## Status

- Stage: 1-in-progress
- Lean target: `GaloisForLFunctions.HTGeometry.GammaIntegerShiftIntensityBlindnessUniversalityLaw`

## Theorem-generated route

Source statements were read first:

- `gammaOppositeShiftIntensityMero_eq_integerShiftGauge`
- `differentialAlgebraicOver_gammaOppositeShiftIntensityMero_add_nat`
- `hypertranscendentalOver_gammaOppositeShiftPhaseMero`
- `hypertranscendentalOver_gammaOppositeShiftWignerSmithLogMero`
- `gammaOppositeShiftPhase_mul_intensity`
- `no_scalarAwareFiniteDifferentialCircuit_gammaWignerSmith_from_integerShiftIntensity`
- Coulomb and de Sitter intensity-observability specializations

The shared selector is the integer difference of two opposite-orientation Gamma shifts.  It makes
intensity a DA reflection gauge without changing the HT phase or HT logarithmic delay.  Finite
differential-circuit source extraction then excludes reconstruction of either orientation-aware
observable from intensity.

## Candidate law

Integer-separated Gamma scattering has a universal observability split: intensity collapses to a
DA gauge, while phase and Wigner--Smith clock remain HT and finite-circuit inaccessible.

## Open audits

- Exact Lean check
- Axiom audit
- Literature novelty audit
