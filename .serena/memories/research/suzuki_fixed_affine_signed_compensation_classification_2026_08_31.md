# Suzuki fixed-affine signed-compensation classification (2026-08-31)

## Qualifying result

Killed the entire fixed constant-affine signed-compensation producer class for the shared Suzuki/Ward chain into HB/FZZ-P/PW-B/RBH.

Let
- `C_N = suzukiNaturalApertureTransitionCoreCauchyEnergy N`,
- `E_N = suzukiTransitionCoreAlignedGammaCompletedEnergy N`,
- `K_N(a,b)=a C_N+b E_N`,
- `R_N(a,b)=C_N-K_N(a,b)`.

Lean proves:
1. `K_N(a,b)/C_N -> a`.
2. Core saturation `K/C -> 1` iff `a=1`.
3. Then `R_N(1,b)=-b E_N` exactly.
4. If `b<0`, residual is nonnegative and eventual upper boundedness iff RH.
5. If `b=0`, residual is identically zero (source erasure).
6. If `b>0`, residual is nonpositive and unconditionally upper bounded by zero (sign-reversed vacuity).

Therefore no fixed affine coefficient choice produces a nontrivial positive source-order premise weaker than RH. Any successor must be scale-dependent, nonlinear, singular, or nonlocal before energy projection.

This uses and strengthens `mem:research/suzuki_canonical_signed_compensation_saturation_2026_08_31`.

## Conjecture loop

C0 conjectured a fixed affine compensation yielding a positive bounded residual upstream of RH. Hostile verdict: CIRCULAR, because saturation forces `a=1` and the residual is scalar `E_N`. Stronger C1 classified the full coefficient plane and became the positive survivor / route-class no-go.

## Exact RH chain

fixed affine Suzuki compensation -> transition-core/Ward residual -> common HB/FZZ-P/PW-B/RBH Ward endpoint -> RH.

This fixed-affine branch is terminal. The surviving source problem remains boundedness of `E_N`, exactly RH.

## Files

- Lean: `formal/GaloisForLFunctions/RHTower/SuzukiFixedAffineSignedCompensationClassification.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Formalized theorem card: `docs/drafts/pipeline/3-formalized/suzuki-fixed-affine-signed-compensation-classification.md`
- Failed route card: `docs/drafts/pipeline/5-failed/suzuki-fixed-affine-signed-compensation-producer.md`

Frontier map remained read-only.

## Principal declarations

- `tendsto_suzukiTransitionCoreFixedAffineSignedCorrection_div_core_atTop`
- `suzukiTransitionCoreFixedAffineCorrectionSaturates_iff`
- `suzukiTransitionCoreFixedAffineResidual_one_eq`
- `suzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove_iff_alignedEnergy`
- `riemannHypothesis_iff_suzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove_of_neg`
- `suzukiFixedAffineSignedCompensation_routeClassification`

## Audits

- Direct Lean check passed.
- Targeted build passed: 13733/13733.
- Five capstones use only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint sees module reachable and reports no local issue.
- Global lint blocked only by unrelated shared-tree unwired modules: `HedenmalmCriticalFeatureFirstOrderWindingReduction`, `HedenmalmCriticalFeaturePoleGammaVerticalFTC`, `HTGeometry.FormationClockTransmutation`.
- No own Lean process left running. A concurrent `KloostermanHybridResidueParseval` Lean process belonged to another workspace actor and was preserved.
