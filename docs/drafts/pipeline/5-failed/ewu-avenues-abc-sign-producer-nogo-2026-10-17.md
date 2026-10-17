# EWU Avenues A, B, and C Sign-Producer Programme No-Go and Positive Survivors

- **ID:** ewu-avenues-abc-sign-producer-nogo-2026-10-17
- **Stage:** 5-failed
- **Type:** FALSIFIED (with 3 Lean-formalized positive survivors)
- **Source:** docs/reports/ewu-review.md · docs/drafts/pipeline/1-in-progress/ewu-blind-minimum-sign-2026-10-16.md
- **Statement:** Avenues A, B, and C of `docs/reports/ewu-review.md` cannot unconditionally produce the asymptotic sign `0 ≤ evenBlindMinimum a` for all `a > 0`: Avenue A succeeds up to `a ≤ (log 2 + 1/50)/2` (`1/20 ≤ evenBlindMinimum a`) but loses its Dirichlet spectral gap as `a → ∞`; Avenue B is invariant under constant shifts `γ ↦ γ - C/2` of the archimedean symbol; Avenue C fails unconditionally because all-integer cosine blindness (`n ≥ 2`) on `G(r) = |f̂(r)|^2 ≥ 0` still permits strictly negative `β = 0` archimedean energy without the off-axis zero `f̂(±i/2) = 0`.

## Goal
Audit and formalize Avenues A, B, and C from `docs/reports/ewu-review.md` to determine whether they yield an unconditional Lean 4 proof of `RiemannHypothesis` via route EWU, or prove their exact obstructions and extract all dependency-closed positive structural survivors.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof of obstructions and positive survivors, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean modules `EvenSectorBlindMinimumSmallAperturePositivity`, `EvenSectorBlindGroundShiftInvariance`, `EvenSectorMultiPrimePeriodizationNoGo`, `lake --old build` green, `#print axioms` PASS

## Approach
1. **Avenue A (Paley–Wiener factor `(r^2 + 1/4)^2`):** Combine the four-stage ground-energy dominance chain `ccmRestrictedWeilGroundEnergy a ≤ ccmRestrictedWeilPolarGroundEnergy a ≤ evenGroundEnergy a ≤ evenBlindMinimum a` with the unconditional Suzuki prime-`2` positivity threshold to establish positivity on small apertures, aperture extension, antitonicity, and exact equivalence with `RiemannHypothesis` beyond prime `2`.
2. **Avenue B (OWU de Branges ground-state transport to EWU):** Analyze the constant-shifted restricted Weil quadratic form `Q_{a,C}(u) = Q_a(u) - C ‖J_a u‖^2` on `BlindUnitSource a` and on the full form domain `CCMArchimedeanFormDomain a`.
3. **Avenue C (Multi-prime cosine periodization of `γ(r)`):** Test whether simultaneous vanishing of `logValue f n` at all integers `n ≥ 2` forces nonnegativity of the pure archimedean functional `poleWeightArchRe 0` on even tests.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:**
  1. **Avenue A asymptotic gap loss:** On `BlindUnitSource a`, the unit norm constraint `‖f‖_{L^2}^2 = (2π)^{-1} ∫ (r^2 + 1/4)^2 |ĝ(r)|^2 dr = 1` carries `(r^2 + 1/4)^2 > 0` in both numerator and denominator; as `a → ∞`, the Dirichlet ground eigenvalue `(π/(2a))^2 + 1/4` of `-∂^2 + 1/4` on `[-a, a]` converges to `1/4`, inside the negative well `{|r| < 6.2898}` of `γ(r)`.
  2. **Avenue B shift-gauge invariance (`EvenSectorBlindGroundShiftInvariance.lean`):** Subtracting the shifted blind minimum `(evenBlindMinimum a - C) ‖J_a u‖^2` from `Q_{a,C}(u) - Σ_j λ_j Tr_j(u)` cancels `C` identically across `CCMArchimedeanFormDomain a` (`shiftedSourceQuadratic_sub_shiftedEvenBlindMinimum_eq`, `shiftedRestrictedWeilForm_sub_shiftedEvenBlindMinimum_eq`, `oddSector_shifted_arithmeticForm_sub_shiftedBlindMinimum_eq`). Thus the Farkas dual multipliers, nonnegative residual form, ground eigenspace, paired-division closure, and canonical polynomial generator are unchanged even when `C > evenBlindMinimum a` makes the blind minimum strictly negative (`shifted_evenBlindMinimum_neg_of_gt`).
  3. **Avenue C all-integer blind `β = 0` counterexample (`EvenSectorMultiPrimePeriodizationNoGo.lean`):** `not_weilPositiveEvenAt_of_lt_one`, `not_weilPositiveEvenAt_zero`, and `exists_even_blind_mixture_zeroPole_neg` prove unconditionally that there exists a finite nonnegative even mixture that is blind at **every** integer `n ≥ 2` and has strictly negative pure archimedean energy `c.sum (fun f t => t * poleWeightArchRe 0 f.1) < 0` (and hence negative `β = 0` Weil energy for every arithmetic sequence `lam : ℕ → ℝ`).
- **Strongest positive survivor:**
  1. **Unconditional positivity past prime `2`, antitonicity, and large-aperture RH reduction (`EvenSectorBlindMinimumSmallAperturePositivity.lean`):**
     - `one_twentieth_le_evenBlindMinimum_of_le_primeTwo`: `a.1 ≤ (Real.log 2 + 1 / 50) / 2 → 1 / 20 ≤ evenBlindMinimum a`.
     - `evenBlindMinimum_antitone`: `a.1 ≤ b.1 → evenBlindMinimum b ≤ evenBlindMinimum a`.
     - `riemannHypothesis_iff_evenBlindMinimum_nonneg_beyond_primeTwo`: `RiemannHypothesis ↔ ∀ a : SuzukiPositiveAperture, (Real.log 2 + 1 / 50) / 2 < a.1 → 0 ≤ evenBlindMinimum a`.
  2. **Exact shift-gauge invariance laws (`EvenSectorBlindGroundShiftInvariance.lean`):**
     - `isMin_shiftedSourceQuadratic_iff`, `shiftedSourceQuadratic_sub_shiftedEvenBlindMinimum_eq`, `shiftedRestrictedWeilForm_sub_shiftedEvenBlindMinimum_eq`, `oddSector_shifted_arithmeticForm_sub_shiftedBlindMinimum_eq`, `shifted_multiplier_inequality_iff`.
  3. **Polar collapse and non-polar support separation (`EvenSectorMultiPrimePeriodizationNoGo.lean`):**
     - `poleWeightArchRe_evenPolar_eq_weilArchRe`, `re_weilPoleWeightFunctional_evenPolar_eq_full`, `not_weilPositiveEvenAt_of_lt_one`, `exists_even_blind_mixture_zeroPole_neg`, `exists_nonpolar_support_of_poleWeightArchRe_ne`.
- **New insight:**
  - Separates the small-aperture differential-gap regime (`a ≤ (log 2 + 1/50)/2`, where `evenBlindMinimum a ≥ 1/20` unconditionally) from the asymptotic multi-prime regime (`a > (log 2 + 1/50)/2`).
  - Proves that neither real-frequency cosine periodization across all primes (`n ≥ 2`) nor the post-subtraction Farkas/de Branges ground-state operator can see the sign of `evenBlindMinimum a`: any viable sign producer must simultaneously use the off-axis complex zero `f̂(±i/2) = 0` (`exists_nonpolar_support_of_poleWeightArchRe_ne`) and the unshifted archimedean scale (`γ(0)` vs. high-frequency growth) prior to subtracting `evenBlindMinimum a`.
- **Status:** Dependency-closed on paper and 100% formalized in Lean 4 (`GaloisForLFunctions.RHTower.EvenSectorBlindMinimumSmallAperturePositivity`, `GaloisForLFunctions.RHTower.EvenSectorBlindGroundShiftInvariance`, `GaloisForLFunctions.RHTower.EvenSectorMultiPrimePeriodizationNoGo`), wired into `formal/GaloisForLFunctions/RHTower.lean`.

## Log
- 2026-10-17 — created and closed in `5-failed` with all 3 positive survivor modules formalized and audited in Lean 4.
