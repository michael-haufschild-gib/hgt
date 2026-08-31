# Suzuki first-moment critical-error classification

- **ID:** CCM-FU-FM-CE
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Classify bounded central unit-Riesz source, hence linear Suzuki curvature first moment, as RH plus bounded square-root-normalized Chebyshev error on natural apertures.

## Goal
Kill or validate the proposed CCM-FU first-moment producer. Chain: central bound ↔ first-moment bound → triangular-curvature bound → RH.

## Corpus facts
- `weightedFirstMomentLinearBound_of_unitRieszCentralBarycenterNaturalBound` proves central → first moment.
- `unitRiesz_center_eq_weightedSignedCurvature_add_arch` and `abs_suzukiCheckpointWeightedArchRenormalization_le` should prove first moment → central.
- `unitRieszCoherentBoundaryJump_eq_normalizedChebyshevError` gives outgoing − central + endpoint = normalized Chebyshev error.
- `riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded` and `unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half` classify bounded outgoing charge as RH.
- `normalizedChebyshevError_log_nat_eq_psiRemainder_div_sqrt` identifies the residual condition exactly.

## Live theorem
`CCMUnitRieszCentralBarycenterNaturalBound ↔ RiemannHypothesis ∧ CriticalMellinNormalizedChebyshevErrorLogNatBounded`; transfer the equivalence to `CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound`.

## Status
Lean complete in `SuzukiFirstMomentCriticalErrorClassification`: first moment ↔ central ↔ `RH ∧ |ψ(M)-M|=O(√M)`. Targeted build passes; axioms are only `propext`, `Classical.choice`, `Quot.sound`. Classical Littlewood `Ω±(√x log log log x)` kills the proposed producer mathematically. Remaining Lean no-go gap: formalize that oscillation theorem on natural apertures.
