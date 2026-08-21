# Projective gauge realizes the intact matched CCM source on a positive rank-two trace-class carrier

- **ID:** `ccm-projective-gauge-nuclear-tomography`
- **Stage:** 3-formalized
- **Type:** THEOREM `[PROVED HERE]`
- **Source:** corpus weld: `CCMActualHeadMatchedPhaseProjectiveFockCocycle` × `CCMActualHeadMatchedSymmetricFirstMomentControl` × `PSDKernelOperations` × `SchattenOneBanach`
- **Statement:** One source-independent projective half-density realizes the full matched-CCM Gram kernel, including both reporter anchors, as matrix coefficients of a positive rank-at-most-two Schatten-one operator. A total nonlinear ratio of its matrix coefficients recovers the complete signed oriented phase symbol exactly; every finite actual matched prime--polar block is the spectral integral of this reporter.

## Result

Let

`a_n = sqrt (criticalMellinAtomWeight n ^ 2 / exp (log n / 2))`.

Code the weight anchor, source anchor, and atom `n` by `0`, `1`, and `n + 2` in `ℕ`. The two feature columns are

- `w = (1, 0, a_0, a_1, ...)`,
- `s_xi = (0, 1, a_0 S_0(xi), a_1 S_1(xi), ...)`,

where `S_n(xi)` is the real intact oriented matched source. The phase-disk law and trigonometric Cauchy--Schwarz give `S_n(xi)^2 ≤ 16`. Existing first-moment control makes `∑ a_n^2` summable, so both columns lie in `ℓ²`.

Define

`T_xi = |w><w| + |s_xi><s_xi|`.

Then `T_xi` is a positive Schatten-one operator of rank at most two, and every full projective-gauge kernel entry is exactly a coordinate matrix coefficient of `T_xi`. Dividing atom/source-anchor by atom/weight-anchor coefficients cancels `a_n`. If the arithmetic weight vanishes, the existing disk law forces the oriented source to vanish, making the total zero branch exact without a premise.

## Lean certificate

Modules:

- `GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeSummableKernel`
- `GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator`

Main theorems:

- `ccmActualHeadMatchedOrientedPhaseSymbol_re_sq_le_sixteen`
- `summable_ccmActualHeadMatchedPhaseProjectiveGaugeArithmeticDiagonal`
- `ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator_isPositive`
- `ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator_hasRankLE_two`
- `ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassOperator_matrix`
- `ccmActualHeadMatchedPhaseProjectiveGaugeTraceClassReporter_eq`
- `ccmActualHeadMatchedPrimePolarFiniteBlock_eq_projectiveGaugeTraceClassOperator`

Both exact leaf builds passed. Endpoint axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into `GaloisForLFunctions.RHTower`.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and attack
- [x] 1 → 2 fully-proven: dependency-closed proof above
- [x] 2 → 3 formalized: closed Lean theorems, exact leaf builds, standard-only axiom audits
- [ ] 3 → 4 publication-ready: standalone manuscript and external novelty audit

## Novelty / no-theatre audit

Earlier corpus branches supplied either a globally positive Fock carrier with nonsummable natural diagonal or a summable arithmetic half-density without a source-faithful operator. Their projective weld changes the obstruction: orientation survives a nonlinear homogeneous ratio while the entire carrier becomes a genuine positive rank-two trace-class operator. This strictly exceeds kernel-PSD packaging because anchors, operator positivity, rank bound, Schatten membership, exact matrix realization, and the actual finite CCM block identity are all formalized.

This theorem does not prove positivity of the signed completed source or RH. Remaining route question is whether projective operator fields admit a compact/limit principle strong enough to transfer the nonlinear matrix ratio through the completed CCM limit without denominator collapse.

## Log

- 2026-08-21 — Broad corpus search found projective gauge invariance plus independently formalized summable half-density; Deninger-`H²`, Gamma-horizon, ABHN, and ordinary Gram-positivity welds were rejected after exact premise/orientation audits.
- 2026-08-21 — Closed summable kernel, full `ℓ²` anchor encoding, positive rank-two Schatten-one realization, exact nonlinear matrix reporter, and actual finite prime--polar spectral identity in Lean.
