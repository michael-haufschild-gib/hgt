# HCF safe-shift Robin--Plemelj normal form

- **ID:** hcf-safe-shift-robin-plemelj
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** HCF source-Plemelj covariance route
- **Statement:** The Euler-safe pole--Gamma--von-Mangoldt jet is exactly the Robin datum `2π(D_t(1) - D_t'(1))` of the zero-independent source density `D_t(η) = π⁻¹ Im P(t-iη)`; hence every compact corrected HCF budget is a finite sum of local Robin--Plemelj defects.

## Goal
Replace derivative-plus-value syntax of the safe-line source diagonal by one vertical Robin datum, then localize corrected covariance site by site before any divisor scalarization.  `[BRIDGE] [NOVELTY UNVERIFIED]`  This does not prove the open `1452/4225` covariance ceiling.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: exact Lean theorem surface in `HedenmalmCriticalFeatureSafeShiftRobinPlemelj.lean`; direct-file check and leaf build green
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
`[PROVED HERE]`

Let `P` be `primeArchSourceRelativeTrace` and set
`D_t(η) = π⁻¹ Im P(t-iη)`.  At `η=1`, the ordinary coordinate is
`1/2 + i(t-i) = 3/2+it`, inside the absolute Euler half-plane.  Thus `P` is holomorphic there.
The real chain rule gives
`D_t'(1) = π⁻¹ Im(P'(t-i)(-i)) = -π⁻¹ Re P'(t-i)`.
Consequently
`2π(D_t(1)-D_t'(1)) = 2(Im P(t-i)+Re P'(t-i))`, exactly
`criticalFeaturePoleGammaVMJet t`.  Finite distributivity then rewrites each compact source-Plemelj
corrected budget as the sum over lattice sites of this Robin datum minus the corresponding compact
positive-shift boundary limit.  No zero set, zero enumeration, or numerical input enters either side.

## Open core
Prove a source-side inequality for the local Robin--Plemelj defect whose canonical height sum is at
most `(1452/4225) N(T) + o(N(T))`.  Existing corpus identities establish exactness, not this sign or
size estimate.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Not falsified.
- **Strongest positive survivor:** Exact local Robin--Plemelj decomposition.
- **New insight:** Quantitative HCF gate can be attacked as a vertical Robin-to-boundary defect rather than cancellation between unrelated lattice totals.
- **Status:** Paper proof and Lean formalization complete.

## Lean certificate

- **Module:** `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmCriticalFeatureSafeShiftRobinPlemelj.lean`
- **Exact source derivative:** `hasDerivAt_criticalFeatureSafeShiftSourceDensity_one`
- **Exact Robin identity:** `criticalFeatureSafeShiftRobinJet_eq_poleGammaVMJet`
- **Finite localization:** `criticalFeatureSourcePlemeljCorrectedLatticeBudget_eq_sum_robinDefects`
- **Cofinal limit:** `tendsto_criticalFeatureSafeShiftRobinPlemeljDefect_sum`
- **Reachability:** imported by `formal/GaloisForLFunctions/RHTower.lean`
- **Verification (2026-08-29):** `lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmCriticalFeatureSafeShiftRobinPlemelj.lean` passed; leaf target `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSafeShiftRobinPlemelj` passed.
- **Axiom audit:** not rerun; no declarations were created or modified in this promotion pass.

## Log
- 2026-08-28 — created in 1-in-progress from source-Plemelj and safe Euler-jet corpus theorems.
- 2026-08-28 — hostile review passed: exact chain-rule identity is dependency-closed; moved to 2-fully-proven.  Quantitative ceiling remains open.
- 2026-08-29 — audited exact existing Lean surface, verified leaf module, and promoted to Stage 3.
