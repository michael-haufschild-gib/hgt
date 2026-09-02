# FZZ balanced Gamma phase-order rigidity

- **ID:** FZZ-P-PHASE-ORDER-2026-09
- **Stage:** 3-formalized
- **Type:** SIGNIFICANT PREMISE DISCHARGE
- **Source:** `FZZCigarParityExternalBRSTBalancedGammaPhaseRecurrenceNoGo`
- **Statement:** At physical level `k=4`, the canonical unwrapped balanced external-Gamma phase is strictly increasing on `ℝ`; hence it vanishes exactly at zero radial momentum.

## Goal

Close the information-faithfulness premise exposed by the pointwise-amplitude no-go:

`source Ward phase = 0 → P = 0 → linear replica-area passivity → FZZ parity-Mellin completeness → RH`.

This does not assume or prove the remaining source-dynamical Ward phase law.

## Gates

- [x] 0 → 1  in-progress: corpus-derived statement, exact FZZ-P chain, cancellation proof idea
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build`, axioms audit
- [ ] 3 → 4  publication-ready: standalone paper

## Approach

Differentiate

`4(phase Γ(1/2+iy) + atan(2y) + atan(2y/3))`.

In the Gauss digamma series, the `n=0` and `n=1` increments exactly cancel the losses of the two rational arctangent slopes. Every later increment is nonnegative, so the slope is minimized at zero. At zero,

`ψ(1/2)+8/3 = 8/3-γ-2 log 2 > 0`.

`γ < 29/50` and `log 2 < 1` make this positive. Hence the phase derivative is positive everywhere; strict monotonicity gives the unique zero. `[PROVED HERE]`

## Novelty audit

Corpus search and primary-source review (`Halder--Jafferis 2402.00932`, `Jafferis--Schneider 2004.05223`, `Ikhlef--Jacobsen--Saleur 1109.1119`) found no exact global order/injectivity theorem for this balanced `k=4` phase.

## Certificate

- Lean: `RHTower.fzzHJBalancedExternalGammaPhaseLift_eq_zero_iff_passive`
- Module: `GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBalancedGammaPhaseOrderRigidity`
- Direct Lean PASS; targeted build `13152/13152` PASS.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Remaining edge: source Ward dynamics must force zero unwrapped phase.
