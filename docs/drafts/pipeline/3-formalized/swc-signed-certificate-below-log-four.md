# Resolution of Signed Window Certificates Below `log 4`

- **ID:** swc-signed-certificate-below-log-four
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.8
- **Lean Modules:**
  - `formal/GaloisForLFunctions/SignedWindowCriticality/BelowLogFour/GaugeExtensionInvarianceAndHalfNormDual.lean`
  - `formal/GaloisForLFunctions/SignedWindowCriticality/BelowLogFour/TwoProfileRefutationBelowLogFour.lean`
  - `formal/GaloisForLFunctions/SignedWindowCriticality/BelowLogFour/RetainedVarianceAndHalfWindowBandBelowLogFour.lean`
- **Primary Declarations:**
  - `not_exists_odd_sinhCharged_gauge_below_log_four`
  - `not_exists_odd_thetaGauge_certificate_below_log_four`
  - `exists_shiftedGroundState_windowLower_neg_below_log_four`
  - `outsideCosh_pos_of_nonneg_weights`
  - `evenThetaGauge_coshChargedDefect_neg`
  - `two_mul_chargeVariance_eq_setIntegral_sq_sub`
  - `signedJumpEnergy_add_sinhDefect_eq_markovEnergy_sub`
  - `signedJumpEnergy_add_outsideSinh_thetaGauge_eq`
  - `shiftedGroundState_windowLower_eq_markovEnergy_sub`
  - `two_profile_sinhQuotient_ge_halfNorm_sq`
  - `primeFree_halfWindow_iff_le_log_two`
  - `zetaWindowPositive_iff_two_three_band`
  - `zetaWindowPositive_iff_two_three_markov_hankel`
  - `even_nonneg_iff_retainedVariance_evenThetaGauge`
  - `odd_nonneg_iff_retainedVariance_shiftedGroundState`
  - `zetaWindowPositive_below_log_four_equivalences`
  - `convex_belowLogFourBandWeights`
  - `not_mem_belowLogFourBandWeights_of_nonpos`
  - `fst_pos_of_mem_belowLogFourBandWeights`
  - `hodgeIndexAtLevel_of_mem_belowLogFourBandWeights`
  - `question_two_eight_complete_resolution`
- **Axioms:** `[propext, Classical.choice, Quot.sound]`

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `GaloisForLFunctions/SignedWindowCriticality/BelowLogFour/`, individual `lake --old env lean` checks green, `#print axioms` PASS

## Formalized Results (`[PROVED HERE]`)

1. **Unconditional Refutation of Variance-Dropping Signed Certificates Below `log 4`:**
   - **Gauge-extension invariance & universal `L^{1/2}` dual (`signedJumpEnergy_add_sinhDefect_eq_markovEnergy_sub`, `signedJumpEnergy_add_outsideSinh_thetaGauge_eq`, `two_profile_sinhQuotient_ge_halfNorm_sq`):** For any `C²_c` gauge `ω` (even if extended arbitrarily outside `S = (−c, c)`) or non-compact odd theta gauge `ω = translateSpan s α b` positive on `(0, c)`, the sum of the signed jump form and the sinh-charged defect / outside-charge potential on two odd tests `F₁, F₂` supported in `(−c, c)` is bounded above uniformly over all gauges by `M(F₁) + M(F₂) − 2(∫_S √(F₁² + F₂²)|sinh(x/2)|)²`.
   - **Two-profile refutation below `log 4` (`exists_two_odd_tests_halfNormDual_neg_below_log_four`, `not_exists_odd_sinhCharged_gauge_below_log_four`, `not_exists_odd_thetaGauge_certificate_below_log_four`, `exists_shiftedGroundState_windowLower_neg_below_log_four`):** At `c₀ = 17/25` (`2c₀ = 34/25 = 1.36 < log 4`), mollifying `u(1 − u²)²` and `(9/2)u(u² − 1/4)(1 − u²)²` yields smooth odd tests `F₁, F₂` supported in `[−273/400, 273/400]` with `M(F₁) + M(F₂) < 2(∫ √(F₁² + F₂²)|sinh(x/2)|)²`. Consequently, for every `c > 273/400` (in particular every `c ∈ (273/400, log 2)`, i.e. `2c ∈ (273/200, log 4)`), **no** `C²_c` odd pole-charged supersolution, **no** odd non-compact theta-gauge outside-charge certificate, and **no** shifted ground state lower bound `2S_a(u) − D_a(u) + 8τ_c(a)∫_{x>0} u² m_a sinh ≥ 0` (`a > 0`) holds on `(−c, c)`.
   - **Even-sector outside-cosh obstruction (`outsideCosh_pos_of_nonneg_weights`, `evenThetaGauge_coshChargedDefect_neg`):** On every bounded window `(−c, c)` (`c ≥ 0`), every even theta gauge with `M = Φω ≥ 0` and positive mass outside `[−c, c]` (in particular every nonzero nonnegative combination of translates of `Φ`) has strictly positive outside cosh charge and strictly negative cosh-charged subsolution defect wherever `ω > 0`.

2. **Mandatory Retained Pole Variance, Sharp `log 4` Boundary, and `{2, 3}` Band Equivalence:**
   - **Pole-jump conductance (`two_mul_chargeVariance_eq_setIntegral_sq_sub`):** `2V^S(u) = ∫_S∫_S m(x)m(y)(u(x) − u(y))² dx dy`, supplying in the odd sector the `4 sinh(x/2) sinh(y/2)` pole-jump conductance that completes `J_{Φω}` into SWC's odd light cone.
   - **Sharp prime-free half-window boundary at `2c = log 4` (`primeFree_halfWindow_iff_le_log_two`):** For `c > 0`, `primeSum f = 0` holds for all `C²` half-window tests `f` on `[−c, 0]` if and only if `c ≤ log 2` (`2c ≤ log 4`).
   - **Multi-way equivalence below `log 4` (`zetaWindowPositive_below_log_four_equivalences`):** For every `0 < c < log 2` (`2c < log 4`) and `a > 0`, `ZetaWindowPositive c` is unconditionally equivalent to: (i) the prime-free half-window `{2, 3}` Hankel band `(w₂, w₃) ∈ belowLogFourBandWeights c`, (ii) the `{2, 3}` Markov–Hankel sector pair (`zetaWindowPositive_iff_two_three_markov_hankel`), (iii) `(scalingSubsurface (realTestsAt c)).HodgeIndex`, (iv) Künneth effectivity at `c`, and (v) the retained-variance Doob–theta signed certificate in `(Φ, ω_a)`.
   - **Convex weight geometry & unconditional nonpositive-`w₂` exclusion (`convex_belowLogFourBandWeights`, `not_mem_belowLogFourBandWeights_of_nonpos`, `fst_pos_of_mem_belowLogFourBandWeights`):** `belowLogFourBandWeights c ⊆ ℝ × ℝ` is convex, and for every `c ≥ 21/40` (`2c ≥ 21/20`), every `(w₂, w₃)` with `w₂ ≤ 0` (including `(0, w₃)` and `(−w₂, w₃)` for all `w₃ : ℝ`) is unconditionally excluded without assuming `ZetaWindowPositive c`.

## No-go closure
- **Exact killing theorem:** `not_exists_odd_sinhCharged_gauge_below_log_four`, `not_exists_odd_thetaGauge_certificate_below_log_four`, `exists_shiftedGroundState_windowLower_neg_below_log_four`, `evenThetaGauge_coshChargedDefect_neg`.
- **Strongest positive survivor:** `two_mul_chargeVariance_eq_setIntegral_sq_sub`, `primeFree_halfWindow_iff_le_log_two`, `zetaWindowPositive_below_log_four_equivalences`, `convex_belowLogFourBandWeights`, `not_mem_belowLogFourBandWeights_of_nonpos`, `question_two_eight_complete_resolution`.
