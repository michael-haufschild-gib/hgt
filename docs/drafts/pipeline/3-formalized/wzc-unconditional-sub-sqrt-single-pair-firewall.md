# Unconditional sub-square-root single-pair firewall and RH `{0, 1, 2}`-edit realization on `(1/2, 2/3)`

- **ID:** wzc-unconditional-sub-sqrt-single-pair-firewall
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `WorldsOfTheZeroConfiguration/TheSignedGroupedEditCountsBelowTheSquareRoot.lean`; `WorldsOfTheZeroConfiguration/TheWorldOneScenarioTable.lean`; `ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean`
- **Statement:** Unconditionally, for every `β ∈ (1/2, 27001/48000)` and `γ ∈ ℝ`, either `ζ(β + iγ) = 0` (`¬ RiemannHypothesis`) or a `{0, 1, 2}`-multiplicity rational-prime edit realizes `β ± iγ` with sub-square-root integer norm count `c < 1/2` and holomorphic continuation below `Re s = 1/2` (and on `(1/2, 15001/24000)` realizes subpolynomial `L²` strip defects with arbitrarily large least deleted prime); under `RiemannHypothesis`, every `β ∈ (1/2, 2/3)` and `γ ≠ 0` is realized as the unique right-of-line off-line zero pair of such a sub-square-root edit while every Hamburger strip defect of that edit is unbounded and non-decaying.

## Lean
Module `WorldsOfTheZeroConfiguration/UnconditionalSubSquareRootSinglePairFirewall.lean` (namespace `GaloisForLFunctions.WorldsOfTheZeroConfiguration`):
`unconditional_subSqrt_singlePair_dichotomy`,
`rh_subSqrt_singlePair_realization_and_defect_barrier`,
`unconditional_subpolynomialDefect_dichotomy_below_five_eighths`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.

## Paper proof
1. **Unconditional `(1/2, 27001/48000)` sub-square-root dichotomy.** By `zetaZeroAbscissa_le_sub_seven_eighths`, `Θ ≤ 20999/24000`. For `1/2 < β < 27001/48000 < 2/3`, `Θ + 2β < 20999/24000 + 27001/24000 = 2`. If `ζ(β + iγ) = 0`, `1/2 < β < 1` violates `RiemannHypothesis` directly; otherwise `exists_isIntegerNormFakeAt_sEdit_lt_half` yields `sEdit α β γ k₀` with count exponent `c < 1/2` and continuation `editG` on `Re s > σ₁` (`σ₁ < 1/2`).
2. **Full `(1/2, 2/3)` single-pair realization under `RiemannHypothesis` and FE defect barrier.** Under `RiemannHypothesis`, `Θ = 1/2`, so `Θ + 2β = 1/2 + 2β < 11/6 < 2` and `ζ(β + iγ) ≠ 0` throughout `1/2 < β < 2/3`. Moreover, for `Re s > 1/2`, `zetaResidueUnit s ≠ 0` (`ζ(s) ≠ 0` for `s ≠ 1` and `zetaResidueUnit 1 = 1`), so `editG s = 0 ↔ s ∈ {β + iγ, β - iγ}` on `Re s > 1/2`: the edit carries a single off-line conjugate pair right of `1/2` with `N_B(x) = A x + O(x^c)` (`c < 1/2`), while `worldOne_row_one` forces every Hamburger strip defect of `ζ_B` to be unbounded and non-decaying.
3. **Unconditional `(1/2, 15001/24000)` subpolynomial-defect dichotomy.** Since `3/2 - Θ ≥ 3/2 - 20999/24000 = 15001/24000`, every `β₀ ∈ (1/2, 15001/24000)` satisfies `β₀ < 3/2 - Θ` unconditionally; splitting on `ζ(β₀ + iγ₀) = 0` vs. `≠ 0` discharges both premises of `worldOne_row_two` and `worldOne_row_three`.

## What it changes
Removes the conditional `Θ + 2β < 2`, `β₀ < 3/2 - Θ`, and `ζ(β + iγ) ≠ 0` premises from the World-I prime-edit theorems, and proves unconditionally that under `RiemannHypothesis` every single off-line pair in `1/2 < Re s < 2/3` is realized over the rational primes with `{0, 1, 2}` multiplicities, sub-square-root integer norm counting `c < 1/2`, and continuation below `1/2`, isolating the functional equation as the sole obstruction.

## Log
- 2026-11-18 — created; proved; formalized.
