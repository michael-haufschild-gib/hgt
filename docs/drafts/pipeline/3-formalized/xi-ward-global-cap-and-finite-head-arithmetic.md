# Polynomial heat inversion, finite-head Prime–Cesàro explicit formula, and Global Ward Cap doubling

- **ID:** WD-WARD-HEAD-ARITH
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route WD (`XiSlice`) · Route G (`XiWardGlobalCap`)
- **Statement:** Exact polynomial heat inversion removes the full-slice three-radii loss on retained finite zero blocks (`λ(t) ≤ δ₀² / (320 log(180|t|))`), couples `[y¹] sliceTruncPoly t H` to the compensated Prime–Cesàro explicit formula, and unifies `zetaZeroWidth ≤ σ` across finite-head heat positivity, `collisionMass` vanishing above `σ²/2`, and almost-everywhere vanishing of the doubled Global Ward Cap on `(0, 366/25]`.

## Goal

Eliminate the `log(3/δ)` three-radii loss and `|t| ≥ e^{16}` height threshold in full-slice Hermite zero-width detection by passing directly through the retained finite zero-head polynomial `sliceTruncPoly t (xiSliceGaussianRadiusHead t R)`, express its linear Taylor coefficient directly through primes and archimedean digamma data via compensated Cesàro truncation, and establish a graded equivalence between `zetaZeroWidth ≤ σ`, arbitrarily-small-heat finite-head Taylor positivity, and the Global Ward Cap Stieltjes functional.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.RHTower.XiWardGlobalCapAndFiniteHeadArithmetic`, direct check PASS, standard axioms only
- [ ] 3 → 4  publication-ready: standalone paper

## Mechanism and main theorems

1. **Polynomial heat semigroup inversion and root obstruction (`forwardPolyHeat_forwardPolyHeat`, `polyHeat_forwardPolyHeat`, `eval_polyHeat_eq_sum_hermiteWeight`, `not_coeffNonneg_taylor_forwardPolyHeat_of_eval_zero`):**
   On `ℝ[X]`, `forwardPolyHeat s₁ (forwardPolyHeat s₂ p) = forwardPolyHeat (s₁ + s₂) p` and `polyHeat s (forwardPolyHeat s p) = p`. Evaluating `polyHeat (λ/2) Q` at `δ > σ ≥ 0` expands against scaled probabilists' Hermite weights `sliceHermiteWeight λ (δ - σ) N`. Whenever `P ≠ 0` vanishes at `δ > σ ≥ 0` and `4 λ deg P ≤ (δ - σ)²`, all Hermite weights up to `deg P` are strictly positive (`sliceHermiteWeight_pos_of_four_mul_le`), obstructing `CoeffNonneg (taylor σ (forwardPolyHeat (λ/2) P))`.

2. **Multiplicity-sharp finite-head pure-quadratic strip law (`not_coeffNonneg_taylor_forwardPolyHeat_finiteHead_of_offLine_zero`, `zetaZeroWidth_le_of_finiteHead_pure_quadratic_heat`, `zetaZeroWidth_le_iff_forall_pos_taylor_forwardPolyHeat_finiteHead_nonneg`):**
   For `R ∈ [1/2, 1]` and `|t| ≥ 73/5`, bounding `natDegree` of `expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R))` via explicit local zero counting (`80 log(180|t|)`) removes the Hadamard tail and three-radii interpolation: `CoeffNonneg` at pure quadratic heat `0 ≤ λ(t) ≤ δ₀² / (320 log(180|t|))` forces `zetaZeroWidth ≤ δ₀`. Removing `Ξ(t) ≠ 0` unconditionally yields the exact equivalence `zetaZeroWidth ≤ σ ↔ ∀ λ > 0, ∀ t, CoeffNonneg (taylor σ (forwardPolyHeat (λ/2) (expand ℝ 2 (sliceTruncPoly t H))))`.

3. **Compensated Prime–Cesàro finite-head explicit formula (`coeff_one_sliceTruncPoly_radius_eq_sum_re`, `coeff_one_sliceTruncPoly_radius_eq_cesaro`, `coeff_one_sliceTruncPoly_radius_eq_cesaro_compensated`):**
   `[y¹] sliceTruncPoly t H = ∑_{q ∈ H} Re((z_q - t)⁻²)`. At `Ξ(t) ≠ 0` and `Y > 1`, splitting the `Y`-twisted divisor sum across `H` cancels the leading `-1/(ρ_q - s)²` tail against `xiSliceGaussianTailQuadratic t H`, leaving `log Y · Re(archLogDeriv(1/2 + it)) - Re(cesaroPrimeSum Y (1/2 + it)) + Re(laguerreRemainder Y (1/2 + it))` minus the finite-head `Y`-twist and the compensated `(Y^{ρ_q - s} - 1)/(ρ_q - s)²` tail.

4. **Global Ward Cap reflection doubling and corpus zero-width dictionary (`re_xiWardZeroStieltjes_neg_of_offLine`, `tsum_xiWardZeroStieltjes_eq_im_logDeriv_xi`, `neg_re_xiWardZeroStieltjes_lt_lineConj`, `two_mul_xiWardRightStieltjesSum_le_euler_sub_critical`, `riemannHypothesis_iff_xiWardCriticalStieltjesSum_eq_euler`, `zetaZeroWidth_le_iff_ae_xiWardGlobalCap_eq_zero_above`, `routeWD_and_corpus_zeroWidth_dictionary`):**
   Off-line Ward–Stieltjes sign definiteness extends from `τ ≤ 12` to `τ ≤ 366/25 = 14.64`. Because the Ward pole center `-1/100` lies strictly left of `1/2`, reflecting `Re ρ > 1/2` to `1 - ρ̄` strictly increases `-Re(((ρ + 1/100)² + τ²)⁻¹)` on `(0, 366/25]`, bounding **twice** the Global Ward Cap by `8π Im(ξ'/ξ(101/100 + iτ)) - xiWardCriticalStieltjesSum τ` and unifying `zetaZeroWidth ≤ σ` across Route WD, Route G, de Bruijn–Newman (`newmanConstant ≤ σ²/2`, `collisionMass = 0` above `σ²/2`), and `theRoutesMeasureOneZeroWidth`.

## Log
- 2026-10-25 — Formalized unconditionally in `formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean` and wired into `RHTower.lean`; verified standard axioms `[propext, Classical.choice, Quot.sound]`.
