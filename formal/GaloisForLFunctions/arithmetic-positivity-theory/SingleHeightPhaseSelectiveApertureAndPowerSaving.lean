import GaloisForLFunctions.SquareRootThreshold.SharpArchimedeanHorizonOfTheZetaSymbol
import GaloisForLFunctions.SquareRootThreshold.KroneckerBohrPrimePhaseRealizationAndExponentialHeightEscape
import GaloisForLFunctions.SquareRootThreshold.WindowedExcursionBalanceAndDoubleWindowRealVarianceLaw
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# Syndetic Bohr–Kronecker Obstruction, High-Height Pole Decay, and Phase-Selective Single-Height Power-Saving Laws

At aperture `a` (`X = e^{2a}`), the localized Weil explicit formula for `ζ` at height `2πξ` splits
as `W_ζ(S_ξ f, S_ξ f) = A_f(ξ) - Π_f(⌊e^{2a}⌋₊, ξ)`, where `A_f(ξ)` is the pole-plus-archimedean
part and `Π_f` is the finite prime-power trigonometric polynomial. Unconditional height-uniform
bounds pay the full `ℓ¹` prime cost `O(√X)` (`c = 2`, horizon exponent `4√X`), restricting
unconditional single-height positivity to `X ≲ (log |ξ|)²`. This module establishes the complete
two-sided structure of single-height prime cancellation, pole decay, and trans-horizon positivity:

1. **Syndetic Bohr–Kronecker Prime-Phase Realization, Eventual-in-Height Impossibility, and
   Smooth `C²` Endpoint-Interferometer Saturation (§1):**
   * Combining prime-torus Kronecker density (`exists_height_prime_phase_approx`) with Bohr almost
     periodicity (`HTGeometry.IsBohrAlmostPeriodic`) upgrades simultaneous prime-phase
     approximation from existential heights to **syndetic (bounded-gap)** height sets
     (`exists_relDense_height_prime_phase_approx`): for every `N`, phase pattern `θ`, and `δ > 0`,
     there is `L > 0` such that *every* interval `[T₀, T₀ + L]` contains a height `ξ` aligning all
     primes `p ≤ N` within `δ` of `e^{iθ(p)}`.
   * Consequently, `PX X τ` returns within `η` of `PX X 0` with bounded gaps
     (`exists_relDense_abs_PX_sub_PX_zero_le`), so **no** lower bound `PX X τ ≥ -(c√X + C)/π` with
     `c < 2` (`not_exists_eventually_atTop_PX_ge_of_lt_two`) and **no** power saving
     `PX X τ ≥ -C X^{θ/2}` with `θ < 1` (`not_exists_eventually_atTop_PX_power_saving`) can hold
     even *eventually* in height `τ ≥ T₁(X)`.
   * Using Abel summation with `Chebyshev.psi_sub_theta_le`, we prove the explicit polynomial
     composite prime-power bound `primePowerTailEnvelope f ⌊e^{2a}⌋₊ ≤ 2 (∫ ‖f‖²) (4a + 4a²)`
     (`primePowerTailEnvelope_exp_le`), and construct the explicit `C²` endpoint-pair interferometer
     `endpointPairProfile a` supported in `[-a, a]` with `L²` norm in `[1/2048, 8]`, uniform
     second-derivative norm `B_f ≤ 336` independent of `a`, and
     `primeOnlyEnvelope - primePowerTailEnvelope > κ₀ e^a ∫ ‖f‖²`
     (`exists_endpointPairProfile_saturation`). Thus smooth `C²` test convolution also cannot
     rescue a height-eventual power saving (`not_exists_eventually_atTop_endpointPair_power_saving`).

2. **Two-Sided `(1 + 2π|ξ|)⁻⁴` High-Height Pole Decay, Forbidden Post-Pole Desert, and Sharp
   Exponential Height Escape (§2):**
   * Shifting `paperFT (heightShift ξ f) (±I/2) = paperFT f (±I/2 + 2πξ)` before applying `C²`
     transform decay yields the two-sided high-height pole bound
     `|Re(h_k(i/2) + h_k(-i/2))| ≤ 2 e^a B_f² / (1 + 2π|ξ|)⁴` (`abs_re_pole_terms_heightShift_le_decay`),
     eliminating the height-independent `2 S(a) ≈ e^a` and `2 e^a (∫ ‖f‖)²` pole barriers in both
     directions (`re_archPart_ge_decay`, `re_archPart_le_decay`).
   * **Unconditional sharp-coefficient horizon (`zetaZeroConfig_re_W_heightShift_nonneg_of_sharp_horizon`):**
     removes `2 S(a)` from `zetaZeroConfig_re_W_heightShift_nonneg_of_horizon`, attaining the
     optimal symbol coefficient `(4 + ε) e^a` on `Re W_ζ(S_ξ f, S_ξ f)` itself.
   * **Forbidden post-pole desert (`re_primePolynomial_le_in_post_pole_desert_of_re_W_nonneg`):**
     once `2 e^a B_f² ≤ (1 + 2π|ξ|)⁴` (`|ξ| ≳ X^{1/8}`), nonnegativity `Re W_ζ(S_ξ f, S_ξ f) ≥ 0`
     forbids `Re Π_f(⌊e^{2a}⌋₊, ξ) > B` throughout the entire intermediate desert up to
     `‖f‖₂² log(1 + 2π|ξ|) ≤ B - 1 - B_f²(1/2 + πC)`.
   * **Non-vacuous post-pole exponential height escape (`exists_gt_height_re_W_neg_or_sharp_escape`,
     `exists_endpointPair_sharp_escape_and_recurrence_lower_bound`):** syndetic Bohr–Kronecker
     alignment past the pole zone forces genuinely superexponential heights `1 + 2πξ > exp(c₀ e^a)`
     (and superexponential Bohr recurrence gaps `L`) under `RiemannHypothesis`.

3. **Barrier-Free Trans-Horizon Graded Power-Saving Single-Height Positivity (§3):**
   * At any single height `ξ` satisfying `(primePolynomial f ⌊e^{2a}⌋₊ ξ).re ≤ c e^{θ a} ∫ ‖f‖²`,
     high-height pole decay gives `Re W_ζ(S_ξ f, S_ξ f) ≥ 0` all the way to the trans-horizon
     aperture `12 + c e^{θ a} ≤ log(1 + π|ξ|/4)` (`X ≍ (log |ξ|)^{2/θ}` for `θ ∈ (0, 1)`, and
     polynomial `X ≲ |ξ|^8` in the phase-selective destructive cone `Re Π_f ≤ 0`)
     (`zetaZeroConfig_re_W_heightShift_nonneg_of_power_saving`).

4. **Single-Height Power Saving Excludes Isolated Depth-`δ` Off-Line Zeros (§4):**
   * Identifying `modulatedTest γ₀ s = heightShift (-γ₀/(2π)) (fun u => (s u : ℂ))`
     (`modulatedTest_eq_heightShift`), a power-saving prime bound at the *single* height
     `ξ₀ = -ρ₀.im / (2π)` on `sinhTest a δ` (without global level-`a` Weil positivity) forces an
     off-line companion zero within ordinate distance `R`
     (`zeta_single_height_power_saving_forces_offLine_companion`).

5. **Syndetic High-Height Kronecker Troughs, Barrier-Free Bad-Height Measure, and Universal
   `O(a² e^{-2θ a})` Power-Saving Violation Measure (§5):**
   * Syndetic Kronecker troughs give bounded-gap heights `ξ` where `Re W_ζ(S_ξ f, S_ξ f)` exceeds
     `(log(1 + π|ξ|/4) - 10) ‖f‖₂² + B - o(1)` free of `-2 S(a)`
     (`exists_relDense_kronecker_trough_re_W_ge_decay`).
   * Upgrading Chebyshev's bad-height inequality with `re_archPart_ge_decay` makes the `O((log X / log Ξ)²)`
     measure bound non-vacuous throughout the full polynomial sub-threshold range `(log Ξ)² ≤ X ≤ Ξ^{1-ε}`
     (`lintegral_bad_heights_le_of_height_decay`), and proves that in every sub-threshold window
     `2r e^{2a} ≤ 1`, heights violating a `θ`-power saving carry universal profile-norm-free weight
     at most `‖η‖₂² · 2(2a(2a + C)) / (c² e^{2θ a}) = O(X^{-θ} (log X)² ‖η‖₂²)`
     (`exists_lintegral_power_saving_violation_heights_le`).
-/

open MeasureTheory Complex Set Filter Topology Finset
open scoped Real ComplexConjugate BigOperators ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositivityTheory

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular
open GaloisForLFunctions GaloisForLFunctions.SquareRootThreshold

/-! ## §1. Syndetic Bohr–Kronecker Realization, Eventual Impossibility, and Smooth `C²` Saturation -/

private theorem expChar_zero_right (μ : ℝ) : expChar μ 0 = 1 := by
  simp [expChar]

private theorem cexp_two_pi_I_add_mul (ξ₀ τ μ : ℝ) :
    cexp (2 * π * I * ((ξ₀ + τ : ℝ) : ℂ) * (μ : ℂ)) =
      cexp (2 * π * I * (ξ₀ : ℂ) * (μ : ℂ)) * expChar (2 * π * μ) τ := by
  unfold expChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Syndetic Bohr–Kronecker Prime-Phase Realization.** For every prime cutoff `N`, target phase
pattern `θ : ℕ → ℝ`, and tolerance `δ > 0`, there exists a bounded gap `L > 0` such that *every*
closed height interval `[T₀, T₀ + L]` contains a height `ξ` simultaneously aligning all prime
phases `e^{2πiξ log p}` (`p ∈ primeIndices N`) within `δ` of `e^{iθ(p)}`. -/
theorem exists_relDense_height_prime_phase_approx (N : ℕ) (θ : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℝ, 0 < L ∧ ∀ T₀ : ℝ, ∃ ξ ∈ Icc T₀ (T₀ + L),
      ∀ p ∈ primeIndices N,
        ‖cexp (2 * π * I * ξ * Real.log p) - cexp ((θ p : ℝ) * I)‖ < δ := by
  obtain ⟨ξ₀, hξ₀⟩ := exists_height_prime_phase_approx N θ (half_pos hδ)
  let F : ℕ → ℝ → ℂ := fun p t =>
    (expChar (2 * π * Real.log p) t - 1) * conj (expChar (2 * π * Real.log p) t - 1)
  have hFc : ∀ p ∈ primeIndices N, Continuous (F p) := fun p _ => by
    have hc : Continuous (fun t => expChar (2 * π * Real.log p) t - 1) :=
      (continuous_expChar _).sub continuous_const
    exact hc.mul (Complex.continuous_conj.comp hc)
  have hFa : ∀ p ∈ primeIndices N, HTGeometry.IsBohrAlmostPeriodic (F p) := fun p _ => by
    have hc : Continuous (fun t => expChar (2 * π * Real.log p) t - 1) :=
      (continuous_expChar _).sub continuous_const
    have ha : HTGeometry.IsBohrAlmostPeriodic (fun t => expChar (2 * π * Real.log p) t - 1) :=
      isBohrAlmostPeriodic_sub (continuous_expChar _) (isBohrAlmostPeriodic_expChar _)
        continuous_const (isBohrAlmostPeriodic_const 1)
    exact isBohrAlmostPeriodic_mul hc ha (Complex.continuous_conj.comp hc)
      (isBohrAlmostPeriodic_conj ha)
  let H : ℝ → ℂ := fun t => ∑ p ∈ primeIndices N, F p t
  have hHa : HTGeometry.IsBohrAlmostPeriodic H :=
    isBohrAlmostPeriodic_sum (primeIndices N) hFc hFa
  have hH0 : H 0 = 0 := by
    simp only [H, F, expChar_zero_right, sub_self, map_zero, mul_zero, Finset.sum_const_zero]
  have hε : 0 < (δ / 2) ^ 2 / 2 := by positivity
  obtain ⟨L, hL, hdense⟩ := hHa ((δ / 2) ^ 2 / 2) hε
  refine ⟨L, hL, fun T₀ => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense (T₀ - ξ₀)
  refine ⟨ξ₀ + τ, ⟨by linarith [hτmem.1], by linarith [hτmem.2]⟩, fun p hp => ?_⟩
  have hHτ : ‖H τ‖ ≤ (δ / 2) ^ 2 / 2 := by
    have h0 := hτ 0
    rwa [zero_add, hH0, sub_zero] at h0
  have hre_eq : ∀ q : ℕ, (F q τ).re = ‖expChar (2 * π * Real.log q) τ - 1‖ ^ 2 := fun q => by
    simp only [F, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hre_sum : (H τ).re =
      ∑ q ∈ primeIndices N, ‖expChar (2 * π * Real.log q) τ - 1‖ ^ 2 := by
    simp only [H, Complex.re_sum, hre_eq]
  have hterm_le : ‖expChar (2 * π * Real.log p) τ - 1‖ ^ 2 ≤ (H τ).re := by
    rw [hre_sum]
    exact Finset.single_le_sum (fun q _ => sq_nonneg _) hp
  have hsq_lt : ‖expChar (2 * π * Real.log p) τ - 1‖ ^ 2 < (δ / 2) ^ 2 := by
    have h1 : (H τ).re ≤ ‖H τ‖ := Complex.re_le_norm _
    have h2 : (δ / 2) ^ 2 / 2 < (δ / 2) ^ 2 := by positivity
    linarith
  have hnorm_lt : ‖expChar (2 * π * Real.log p) τ - 1‖ < δ / 2 := by
    nlinarith [norm_nonneg (expChar (2 * π * Real.log p) τ - 1)]
  rw [cexp_two_pi_I_add_mul]
  have hsplit :
      cexp (2 * π * I * (ξ₀ : ℂ) * (Real.log p : ℂ)) * expChar (2 * π * Real.log p) τ -
        cexp ((θ p : ℝ) * I) =
      cexp (2 * π * I * (ξ₀ : ℂ) * (Real.log p : ℂ)) *
          (expChar (2 * π * Real.log p) τ - 1) +
        (cexp (2 * π * I * (ξ₀ : ℂ) * (Real.log p : ℂ)) - cexp ((θ p : ℝ) * I)) := by
    ring
  rw [hsplit]
  have hunit : ‖cexp (2 * π * I * (ξ₀ : ℂ) * (Real.log p : ℂ))‖ = 1 :=
    norm_cexp_two_pi_I_mul ξ₀ (Real.log p)
  calc ‖cexp (2 * π * I * (ξ₀ : ℂ) * (Real.log p : ℂ)) *
          (expChar (2 * π * Real.log p) τ - 1) +
        (cexp (2 * π * I * (ξ₀ : ℂ) * (Real.log p : ℂ)) - cexp ((θ p : ℝ) * I))‖
      ≤ ‖cexp (2 * π * I * (ξ₀ : ℂ) * (Real.log p : ℂ)) *
          (expChar (2 * π * Real.log p) τ - 1)‖ +
        ‖cexp (2 * π * I * (ξ₀ : ℂ) * (Real.log p : ℂ)) - cexp ((θ p : ℝ) * I)‖ :=
        norm_add_le _ _
    _ = ‖expChar (2 * π * Real.log p) τ - 1‖ +
        ‖cexp (2 * π * I * (ξ₀ : ℂ) * (Real.log p : ℂ)) - cexp ((θ p : ℝ) * I)‖ := by
        rw [norm_mul, hunit, one_mul]
    _ < δ / 2 + δ / 2 := add_lt_add hnorm_lt (hξ₀ p hp)
    _ = δ := add_halves δ

/-- Arbitrarily-large-height Kronecker prime-phase approximation: for every `T₀ ∈ ℝ`, there exists
`ξ > T₀` aligning all prime phases `p ∈ primeIndices N` within `δ`. -/
theorem exists_gt_height_prime_phase_approx (N : ℕ) (θ : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (T₀ : ℝ) :
    ∃ ξ : ℝ, T₀ < ξ ∧ ∀ p ∈ primeIndices N,
      ‖cexp (2 * π * I * ξ * Real.log p) - cexp ((θ p : ℝ) * I)‖ < δ := by
  obtain ⟨L, _, hdense⟩ := exists_relDense_height_prime_phase_approx N θ hδ
  obtain ⟨ξ, hξmem, hξ⟩ := hdense (T₀ + 1)
  exact ⟨ξ, by linarith [hξmem.1], hξ⟩

/-- Syndetic phase realization for `primeOnlyPolynomial`: there is a bounded gap `L > 0` such that
every `[T₀, T₀ + L]` contains a height `ξ` at which `(primeOnlyPolynomial f N ξ).re` is within `ε`
of `∑_{p ∈ primeIndices N} 2 Re(primeCoeff f (p, true) e^{iθ(p)})`. -/
theorem exists_relDense_re_primeOnlyPolynomial_approx_phase (f : ℝ → ℂ) (N : ℕ) (θ : ℕ → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ T₀ : ℝ, ∃ ξ ∈ Icc T₀ (T₀ + L),
      |(primeOnlyPolynomial f N ξ).re -
        ∑ p ∈ primeIndices N, 2 * (primeCoeff f (p, true) * cexp ((θ p : ℝ) * I)).re| < ε := by
  set M := primeOnlyEnvelope f N
  have hM0 : 0 ≤ M := primeOnlyEnvelope_nonneg f N
  have hM1 : 0 < M + 1 := by linarith
  set δ := ε / (M + 1) with hδ_def
  have hδ : 0 < δ := div_pos hε hM1
  obtain ⟨L, hL, hdense⟩ := exists_relDense_height_prime_phase_approx N θ hδ
  refine ⟨L, hL, fun T₀ => ?_⟩
  obtain ⟨ξ, hξmem, hξ⟩ := hdense T₀
  refine ⟨ξ, hξmem, ?_⟩
  rw [re_primeOnlyPolynomial_eq_sum, ← Finset.sum_sub_distrib]
  have hle : |∑ p ∈ primeIndices N,
      (2 * (primeCoeff f (p, true) * cexp (2 * π * I * ξ * Real.log p)).re -
        2 * (primeCoeff f (p, true) * cexp ((θ p : ℝ) * I)).re)| ≤
      ∑ p ∈ primeIndices N, (2 * ‖primeCoeff f (p, true)‖) * δ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    have hsub : 2 * (primeCoeff f (p, true) * cexp (2 * π * I * ξ * Real.log p)).re -
        2 * (primeCoeff f (p, true) * cexp ((θ p : ℝ) * I)).re =
        2 * (primeCoeff f (p, true) *
          (cexp (2 * π * I * ξ * Real.log p) - cexp ((θ p : ℝ) * I))).re := by
      rw [mul_sub, Complex.sub_re]
      ring
    rw [hsub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hre : |(primeCoeff f (p, true) *
        (cexp (2 * π * I * ξ * Real.log p) - cexp ((θ p : ℝ) * I))).re| ≤
        ‖primeCoeff f (p, true)‖ *
          ‖cexp (2 * π * I * ξ * Real.log p) - cexp ((θ p : ℝ) * I)‖ :=
      (Complex.abs_re_le_norm _).trans (le_of_eq (norm_mul _ _))
    have hlt := (hξ p hp).le
    nlinarith [norm_nonneg (primeCoeff f (p, true))]
  rw [← Finset.sum_mul, ← primeOnlyEnvelope_eq_sum_two_mul_norm_true] at hle
  have hstrict : M * δ < ε := by
    rw [hδ_def, mul_div_assoc', div_lt_iff₀ hM1]
    linarith
  exact lt_of_le_of_lt hle hstrict

/-- **Syndetic Coherent Peaks and Troughs of `primePolynomial`.** For every
`B < primeOnlyEnvelope f N - primePowerTailEnvelope f N`, there exists a single bounded gap `L > 0`
such that *every* closed interval `[T₀, T₀ + L]` contains both a coherent peak `ξ₊` with
`(primePolynomial f N ξ₊).re > B` and a coherent trough `ξ₋` with
`(primePolynomial f N ξ₋).re < -B`. -/
theorem exists_relDense_re_primePolynomial_gt_and_lt (f : ℝ → ℂ) (N : ℕ) {B : ℝ}
    (hB : B < primeOnlyEnvelope f N - primePowerTailEnvelope f N) :
    ∃ L : ℝ, 0 < L ∧ ∀ T₀ : ℝ,
      (∃ ξ₊ ∈ Icc T₀ (T₀ + L), B < (primePolynomial f N ξ₊).re) ∧
      (∃ ξ₋ ∈ Icc T₀ (T₀ + L), (primePolynomial f N ξ₋).re < -B) := by
  set B' := B + primePowerTailEnvelope f N
  have hε : 0 < primeOnlyEnvelope f N - B' := by simp only [B']; linarith
  obtain ⟨L₁, hL₁, hd₁⟩ := exists_relDense_re_primeOnlyPolynomial_approx_phase f N
    (fun p => -(primeCoeff f (p, true)).arg) hε
  obtain ⟨L₂, hL₂, hd₂⟩ := exists_relDense_re_primeOnlyPolynomial_approx_phase f N
    (fun p => π - (primeCoeff f (p, true)).arg) hε
  refine ⟨max L₁ L₂, lt_max_of_lt_left hL₁, fun T₀ => ⟨?_, ?_⟩⟩
  · obtain ⟨ξ₊, hmem, hξ₊⟩ := hd₁ T₀
    have hsum : ∑ p ∈ primeIndices N,
        2 * (primeCoeff f (p, true) * cexp (((-(primeCoeff f (p, true)).arg : ℝ) : ℂ) * I)).re =
        primeOnlyEnvelope f N := by
      rw [primeOnlyEnvelope_eq_sum_two_mul_norm_true]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [re_mul_cexp_neg_arg]
    rw [hsum] at hξ₊
    have h1 : B' < (primeOnlyPolynomial f N ξ₊).re := by linarith [(abs_lt.mp hξ₊).1]
    have htail := (abs_le.mp (abs_re_primePowerTailPolynomial_le f N ξ₊)).1
    refine ⟨ξ₊, ⟨hmem.1, hmem.2.trans (by linarith [le_max_left L₁ L₂])⟩, ?_⟩
    rw [primePolynomial_eq_primeOnly_add_tail, Complex.add_re]
    simp only [B'] at h1
    linarith
  · obtain ⟨ξ₋, hmem, hξ₋⟩ := hd₂ T₀
    have hsum : ∑ p ∈ primeIndices N,
        2 * (primeCoeff f (p, true) * cexp (((π - (primeCoeff f (p, true)).arg : ℝ) : ℂ) * I)).re =
        -primeOnlyEnvelope f N := by
      rw [primeOnlyEnvelope_eq_sum_two_mul_norm_true, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [re_mul_cexp_pi_sub_arg]
      ring
    rw [hsum] at hξ₋
    have h1 : (primeOnlyPolynomial f N ξ₋).re < -B' := by linarith [(abs_lt.mp hξ₋).2]
    have htail := (abs_le.mp (abs_re_primePowerTailPolynomial_le f N ξ₋)).2
    refine ⟨ξ₋, ⟨hmem.1, hmem.2.trans (by linarith [le_max_right L₁ L₂])⟩, ?_⟩
    rw [primePolynomial_eq_primeOnly_add_tail, Complex.add_re]
    simp only [B'] at h1
    linarith

/-- **Syndetic Return of the Prime Symbol `PX` to Its Height-Zero Extremum `PX X 0`.** For every
cutoff `X : ℝ` and tolerance `η > 0`, there exists `L > 0` such that every interval `[T₀, T₀ + L]`
contains `τ` with `|PX X τ - PX X 0| ≤ η`. -/
theorem exists_relDense_abs_PX_sub_PX_zero_le (X : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ L : ℝ, 0 < L ∧ ∀ T₀ : ℝ, ∃ τ ∈ Icc T₀ (T₀ + L), |PX X τ - PX X 0| ≤ η := by
  let S : ℝ → ℂ := fun t =>
    ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (((Λ n : ℝ) / Real.sqrt n : ℝ) : ℂ) * expChar (Real.log n) t
  have hSa : HTGeometry.IsBohrAlmostPeriodic S := by
    refine isBohrAlmostPeriodic_sum (Finset.Ioc 0 ⌊X⌋₊) (fun n _ => ?_) (fun n _ => ?_)
    · exact continuous_const.mul (continuous_expChar _)
    · exact isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _)
  let G : ℝ → ℂ := fun t => ((-(1 / π) : ℝ) : ℂ) * S t
  have hGa : HTGeometry.IsBohrAlmostPeriodic G := isBohrAlmostPeriodic_const_mul _ hSa
  have hGre : ∀ t : ℝ, (G t).re = PX X t := fun t => by
    simp only [G, S, Complex.re_ofReal_mul, Complex.re_sum, PX]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_ofReal_mul, expChar, Complex.exp_ofReal_mul_I_re, mul_comm (Real.log n) t]
  obtain ⟨L, hL, hdense⟩ := hGa η hη
  refine ⟨L, hL, fun T₀ => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense T₀
  refine ⟨τ, hτmem, ?_⟩
  rw [← hGre τ, ← hGre 0, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  simpa only [zero_add] using hτ 0

/-- **Eventual-in-Height Optimality of `c = 2` for `PX`.** No bound `PX X τ ≥ -(c√X + C)/π` with
`c < 2` can hold even *eventually* in height `τ ≥ T₁ X` (for any height threshold function
`T₁ : ℝ → ℝ`), because `PX X` returns syndetically to `PX X 0`. -/
theorem not_exists_eventually_atTop_PX_ge_of_lt_two {c : ℝ} (hc : c < 2) :
    ¬ ∃ (C : ℝ) (T₁ : ℝ → ℝ), ∀ X : ℝ, 0 ≤ X → ∀ τ : ℝ, T₁ X ≤ τ →
      -((c * Real.sqrt X + C) / π) ≤ PX X τ := by
  rintro ⟨C, T₁, hC⟩
  have hev := FreeLagTrace.tendsto_sum_vonMangoldt_div_sqrt.eventually
    (Ioi_mem_nhds (show (c + 2) / 2 < 2 by linarith))
  have hev2 : ∀ᶠ X : ℝ in atTop, (2 * |C| + 2) / (2 - c) < Real.sqrt X :=
    Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨X, hX1, hX2, hX3⟩ := (hev.and (hev2.and (eventually_gt_atTop 0))).exists
  obtain ⟨L, _, hdense⟩ := exists_relDense_abs_PX_sub_PX_zero_le X
    (show (0 : ℝ) < 1 / (2 * π) by positivity)
  obtain ⟨τ, hτmem, hτ⟩ := hdense (T₁ X)
  have hbound := hC X hX3.le τ hτmem.1
  have hclose : PX X τ ≤ PX X 0 + 1 / (2 * π) := by linarith [(abs_le.mp hτ).2]
  have hge := (lt_div_iff₀ (Real.sqrt_pos.mpr hX3)).mp hX1
  rw [sum_Icc_zero_eq_sum_Ioc_vonMangoldt_div_sqrt] at hge
  have hPX0 : PX X 0 < -(((c + 2) / 2) * Real.sqrt X) / π := by
    rw [PX_zero, one_div, neg_mul, ← div_eq_inv_mul, neg_div]
    exact neg_lt_neg ((div_lt_div_iff_of_pos_right Real.pi_pos).mpr hge)
  have h2 := (div_lt_iff₀ (by linarith : (0 : ℝ) < 2 - c)).mp hX2
  have hgap : -(((c + 2) / 2) * Real.sqrt X) / π + 1 / (2 * π) <
      -((c * Real.sqrt X + C) / π) := by
    have hpi : (0 : ℝ) < 2 * π := Real.two_pi_pos
    rw [show -(((c + 2) / 2) * Real.sqrt X) / π + 1 / (2 * π) =
        (-(c + 2) * Real.sqrt X + 1) / (2 * π) by field_simp; ring,
      show -((c * Real.sqrt X + C) / π) = (-2 * c * Real.sqrt X - 2 * C) / (2 * π) by
        field_simp; ring,
      div_lt_div_iff_of_pos_right hpi]
    nlinarith [le_abs_self C]
  linarith

/-- **Eventual-in-Height Power-Saving Impossibility for `PX`.** For every exponent `θ < 1`,
constant `C : ℝ`, and arbitrary height-threshold function `T₁ : ℝ → ℝ`, it is impossible that
`-C * X ^ (θ / 2) ≤ PX X τ` for all `X ≥ 1` and all `τ ≥ T₁ X`. -/
theorem not_exists_eventually_atTop_PX_power_saving {θ : ℝ} (hθ : θ < 1) :
    ¬ ∃ (C : ℝ) (T₁ : ℝ → ℝ), ∀ X : ℝ, 1 ≤ X → ∀ τ : ℝ, T₁ X ≤ τ →
      -C * X ^ (θ / 2) ≤ PX X τ := by
  rintro ⟨C, T₁, hC⟩
  have hev1 := FreeLagTrace.tendsto_sum_vonMangoldt_div_sqrt.eventually
    (Ioi_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  have hpos_exp : 0 < (1 - θ) / 2 := by linarith
  have hev2 : ∀ᶠ X : ℝ in atTop, π * |C| + 1 < X ^ ((1 - θ) / 2) :=
    (tendsto_rpow_atTop hpos_exp).eventually (eventually_gt_atTop _)
  have hev3 : ∀ᶠ X : ℝ in atTop, π * |C| + 1 < Real.sqrt X :=
    Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨X, hX1, hX2, hX3, hX_ge1⟩ :=
    (hev1.and (hev2.and (hev3.and (eventually_ge_atTop (1 : ℝ))))).exists
  have hX0 : 0 < X := by linarith
  obtain ⟨L, _, hdense⟩ := exists_relDense_abs_PX_sub_PX_zero_le X
    (show (0 : ℝ) < 1 / (2 * π) by positivity)
  obtain ⟨τ, hτmem, hτ⟩ := hdense (T₁ X)
  have hbound := hC X hX_ge1 τ hτmem.1
  have hclose : PX X τ ≤ PX X 0 + 1 / (2 * π) := by linarith [(abs_le.mp hτ).2]
  have hge := (lt_div_iff₀ (Real.sqrt_pos.mpr hX0)).mp hX1
  rw [sum_Icc_zero_eq_sum_Ioc_vonMangoldt_div_sqrt, one_mul] at hge
  have hPX0 : PX X 0 < -Real.sqrt X / π := by
    rw [PX_zero, one_div, neg_mul, ← div_eq_inv_mul, neg_div]
    exact neg_lt_neg ((div_lt_div_iff_of_pos_right Real.pi_pos).mpr hge)
  have hsqrt_split : Real.sqrt X = X ^ (θ / 2) * X ^ ((1 - θ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0]
    congr 1
    ring
  have hXr_pos : 0 < X ^ (θ / 2) := Real.rpow_pos_of_pos hX0 _
  have hprod_gt : π * |C| * X ^ (θ / 2) + 1 / 2 < Real.sqrt X := by
    rcases le_or_gt 1 (X ^ (θ / 2)) with hge1 | hlt1
    · have hmul : (π * |C| + 1) * X ^ (θ / 2) < Real.sqrt X := by
        rw [hsqrt_split, mul_comm (X ^ (θ / 2)) (X ^ ((1 - θ) / 2))]
        exact mul_lt_mul_of_pos_right hX2 hXr_pos
      nlinarith
    · nlinarith [Real.pi_pos, abs_nonneg C]
  have hgap : -Real.sqrt X / π + 1 / (2 * π) < -C * X ^ (θ / 2) := by
    have hpi2 : (0 : ℝ) < 2 * π := Real.two_pi_pos
    rw [show -Real.sqrt X / π + 1 / (2 * π) = (-2 * Real.sqrt X + 1) / (2 * π) by
        field_simp; ring,
      div_lt_iff₀ hpi2]
    have hCle : -|C| ≤ C := neg_abs_le C
    have hCX : -|C| * X ^ (θ / 2) ≤ C * X ^ (θ / 2) :=
      mul_le_mul_of_nonneg_right hCle hXr_pos.le
    nlinarith [Real.pi_pos]
  linarith

/-! ### Explicit Polynomial Composite Prime-Power Tail Bound and Smooth `C²` Saturation -/

/-- **Explicit Composite Prime-Power `n^{-1/2}` Sum Bound.** By Abel summation and
`Chebyshev.psi_sub_theta_le`, for every `x ≥ 1`,
`∑_{n ∈ compIndices ⌊x⌋₊} Λ(n) / √n ≤ 2 log x + (log x)²`. -/
theorem sum_compIndices_vonMangoldt_div_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ compIndices ⌊x⌋₊, (Λ n : ℝ) / Real.sqrt n ≤ 2 * Real.log x + (Real.log x) ^ 2 := by
  have hx0 : 0 < x := by linarith
  let Λc : ℕ → ℝ := fun n => if ¬ Nat.Prime n then (Λ n : ℝ) else 0
  have hsum_t : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Λc k = Chebyshev.psi t - Chebyshev.theta t := by
    intro t
    rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : Nat.Prime k
    · simp [Λc, hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
    · simp [Λc, hk]
  have hcomp_eq : ∑ n ∈ compIndices ⌊x⌋₊, (Λ n : ℝ) / Real.sqrt n =
      ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (k : ℝ) ^ (-(1 / 2 : ℝ)) * Λc k := by
    unfold compIndices
    rw [Finset.sum_filter]
    have hsub : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (if ¬ Nat.Prime n then (Λ n : ℝ) / Real.sqrt n else 0) =
        ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (if ¬ Nat.Prime n then (Λ n : ℝ) / Real.sqrt n else 0) := by
      refine Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)
      · rw [Finset.mem_Icc] at hn ⊢; omega
      · rw [Finset.mem_Icc] at hn hn'
        have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp
    rw [hsub]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hrpow : (k : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt k)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg k)]
    by_cases hk : Nat.Prime k
    · simp [Λc, hk]
    · simp [Λc, hk, hrpow, div_eq_mul_inv, mul_comm]
  have hf_diff : ∀ t ∈ Icc (1 : ℝ) x,
      DifferentiableAt ℝ (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) t := fun t ht =>
    Real.differentiableAt_rpow_const_of_ne _ (by linarith [ht.1] : t ≠ 0)
  have hderiv : deriv (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) =
      fun t : ℝ => -(1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ) - 1) := Real.deriv_rpow_const' _
  have hf_int : IntegrableOn (deriv fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Icc 1 x) := by
    rw [hderiv]
    refine (ContinuousOn.mul continuousOn_const ?_).integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t _ (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousWithinAt
  have habel := sum_mul_eq_sub_integral_mul₀ Λc (by simp [Λc]) x hf_diff hf_int
  have hI : (∫ t in Ioc 1 x, deriv (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Λc k) =
      -(1 / 2 : ℝ) * ∫ t in Ioc 1 x,
        t ^ (-(1 / 2 : ℝ) - 1) * (Chebyshev.psi t - Chebyshev.theta t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [hderiv, hsum_t t]
    ring
  rw [hsum_t x, hI] at habel
  have hab_eq : ∑ n ∈ compIndices ⌊x⌋₊, (Λ n : ℝ) / Real.sqrt n =
      x ^ (-(1 / 2 : ℝ)) * (Chebyshev.psi x - Chebyshev.theta x) +
        (1 / 2) * ∫ t in Ioc 1 x,
          t ^ (-(1 / 2 : ℝ) - 1) * (Chebyshev.psi t - Chebyshev.theta t) := by
    rw [hcomp_eq, habel]
    ring
  rw [hab_eq]
  have hdiff_nn : ∀ t : ℝ, 0 ≤ Chebyshev.psi t - Chebyshev.theta t := fun t => by
    rw [← hsum_t t]
    exact Finset.sum_nonneg fun k _ => by
      by_cases hk : Nat.Prime k <;> simp [Λc, hk, ArithmeticFunction.vonMangoldt_nonneg]
  have hfirst : x ^ (-(1 / 2 : ℝ)) * (Chebyshev.psi x - Chebyshev.theta x) ≤ 2 * Real.log x := by
    have hnn : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    have hmul : x ^ (-(1 / 2 : ℝ)) * Real.sqrt x = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
      norm_num
    calc x ^ (-(1 / 2 : ℝ)) * (Chebyshev.psi x - Chebyshev.theta x)
        ≤ x ^ (-(1 / 2 : ℝ)) * (2 * Real.sqrt x * Real.log x) :=
          mul_le_mul_of_nonneg_left (Chebyshev.psi_sub_theta_le hx) hnn
      _ = 2 * (x ^ (-(1 / 2 : ℝ)) * Real.sqrt x) * Real.log x := by ring
      _ = 2 * Real.log x := by rw [hmul]; ring
  have hcont_rpow : ContinuousOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ) - 1)) (Icc 1 x) := fun t ht =>
    (Real.continuousAt_rpow_const t _ (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousWithinAt
  have hint_lhs : IntegrableOn
      (fun t : ℝ => t ^ (-(1 / 2 : ℝ) - 1) * (Chebyshev.psi t - Chebyshev.theta t))
      (Ioc 1 x) := by
    refine Integrable.mono' (g := fun _ => Chebyshev.psi x) (integrableOn_const (by simp))
      ((hcont_rpow.aestronglyMeasurable measurableSet_Icc).mono_set Ioc_subset_Icc_self |>.mul
        ((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).aestronglyMeasurable.restrict))
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : t ^ (-(1 / 2 : ℝ) - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht.1.le (by norm_num)
    have hrnn : 0 ≤ t ^ (-(1 / 2 : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    have hle_psi : Chebyshev.psi t - Chebyshev.theta t ≤ Chebyshev.psi x := by
      linarith [Chebyshev.theta_nonneg t, Chebyshev.psi_mono ht.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrnn (hdiff_nn t))]
    calc t ^ (-(1 / 2 : ℝ) - 1) * (Chebyshev.psi t - Chebyshev.theta t)
        ≤ 1 * (Chebyshev.psi t - Chebyshev.theta t) :=
          mul_le_mul_of_nonneg_right h1 (hdiff_nn t)
      _ ≤ Chebyshev.psi x := by linarith
  have hcont_inv : ContinuousOn (fun t : ℝ => t⁻¹) (Icc 1 x) :=
    continuousOn_id.inv₀ fun t ht => by linarith [ht.1]
  have hint_rhs : IntegrableOn (fun t : ℝ => (2 * Real.log x) * t⁻¹) (Ioc 1 x) :=
    ((continuousOn_const.mul hcont_inv).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint_le : ∫ t in Ioc 1 x,
        t ^ (-(1 / 2 : ℝ) - 1) * (Chebyshev.psi t - Chebyshev.theta t) ≤
      ∫ t in Ioc 1 x, (2 * Real.log x) * t⁻¹ := by
    refine setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    have hrnn : 0 ≤ t ^ (-(1 / 2 : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    have hlog_le : Real.log t ≤ Real.log x := Real.log_le_log ht0 ht.2
    have hmul : t ^ (-(1 / 2 : ℝ) - 1) * Real.sqrt t = t⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]
      norm_num
      exact Real.rpow_neg_one t
    calc t ^ (-(1 / 2 : ℝ) - 1) * (Chebyshev.psi t - Chebyshev.theta t)
        ≤ t ^ (-(1 / 2 : ℝ) - 1) * (2 * Real.sqrt t * Real.log t) :=
          mul_le_mul_of_nonneg_left (Chebyshev.psi_sub_theta_le ht.1.le) hrnn
      _ = 2 * (t ^ (-(1 / 2 : ℝ) - 1) * Real.sqrt t) * Real.log t := by ring
      _ = 2 * t⁻¹ * Real.log t := by rw [hmul]
      _ ≤ 2 * t⁻¹ * Real.log x :=
          mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ = (2 * Real.log x) * t⁻¹ := by ring
  have heval_inv : ∫ t in Ioc 1 x, (2 * Real.log x) * t⁻¹ = 2 * (Real.log x) ^ 2 := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hx]
    have hd : ∀ t ∈ uIcc 1 x, HasDerivAt Real.log t⁻¹ t := fun t ht => by
      rw [uIcc_of_le hx] at ht
      exact Real.hasDerivAt_log (by linarith [ht.1])
    have hint_iv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 x :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
        (hcont_inv.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint_iv, Real.log_one, sub_zero]
    ring
  linarith

/-- **Explicit Polynomial Bound on `primePowerTailEnvelope`.** For every continuous compactly
supported profile `f : ℝ → ℂ` and `a ≥ 0`, the composite prime-power `ℓ¹` envelope up to `⌊e^{2a}⌋₊`
is at most `2 (∫ ‖f‖²) (4a + 4a²) = O(a² ‖f‖₂²)`. -/
theorem primePowerTailEnvelope_exp_le {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊ ≤
      2 * (∫ t, ‖f t‖ ^ 2) * (4 * a + 4 * a ^ 2) := by
  have hx1 : 1 ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
  have hcomp := sum_compIndices_vonMangoldt_div_sqrt_le hx1
  rw [Real.log_exp] at hcomp
  unfold primePowerTailEnvelope
  rw [Finset.sum_product]
  have hterm : ∀ n ∈ compIndices ⌊Real.exp (2 * a)⌋₊,
      ∑ b : Bool, ‖primeCoeff f (n, b)‖ ≤
        2 * (∫ t, ‖f t‖ ^ 2) * ((Λ n : ℝ) / Real.sqrt n) := by
    intro n _
    rw [Fintype.sum_bool]
    have hb1 := norm_weilTest_self_le hf hfc (primeFreq (n, true))
    have hb2 := norm_weilTest_self_le hf hfc (primeFreq (n, false))
    have hw : 0 ≤ (Λ n : ℝ) / Real.sqrt n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    simp only [primeCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    nlinarith
  calc ∑ n ∈ compIndices ⌊Real.exp (2 * a)⌋₊, ∑ b : Bool, ‖primeCoeff f (n, b)‖
      ≤ ∑ n ∈ compIndices ⌊Real.exp (2 * a)⌋₊,
          2 * (∫ t, ‖f t‖ ^ 2) * ((Λ n : ℝ) / Real.sqrt n) := Finset.sum_le_sum hterm
    _ = 2 * (∫ t, ‖f t‖ ^ 2) * ∑ n ∈ compIndices ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / Real.sqrt n := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * (∫ t, ‖f t‖ ^ 2) * (2 * (2 * a) + (2 * a) ^ 2) :=
        mul_le_mul_of_nonneg_left hcomp
          (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
    _ = 2 * (∫ t, ‖f t‖ ^ 2) * (4 * a + 4 * a ^ 2) := by ring

/-- The unit `C²` bell `(1 - u²)₊^{5/2}` (`sinhTestWeight 1 u`). -/
def unitBell (u : ℝ) : ℝ := sinhTestWeight 1 u

/-- Second derivative of `unitBell`. -/
def unitBellDeriv2 (u : ℝ) : ℝ :=
  -5 * (1 ^ 2 - u ^ 2) ^ (3 / 2 : ℝ) + 15 * u ^ 2 * (1 ^ 2 - u ^ 2) ^ (1 / 2 : ℝ)

private theorem unitBell_contDiff : ContDiff ℝ 2 unitBell := by
  have h52 : ContDiff ℝ 2 (fun x : ℝ => x ^ (5 / 2 : ℝ)) := by
    have := Real.contDiff_rpow_const_of_le (n := 2) (p := 5 / 2) (by norm_num)
    exact_mod_cast this
  exact h52.comp (contDiff_const.sub (contDiff_id.pow 2))

private theorem unitBell_nonneg (u : ℝ) : 0 ≤ unitBell u := sinhTestWeight_nonneg 1 u

private theorem unitBell_eq_zero {u : ℝ} (hu : 1 < |u|) : unitBell u = 0 := by
  have h : 1 ^ 2 - u ^ 2 < 0 := by nlinarith [abs_nonneg u, sq_abs u]
  simp only [unitBell, sinhTestWeight, rpow_five_halves_of_neg h]

private theorem unitBell_le_one (u : ℝ) : unitBell u ≤ 1 := by
  rcases le_or_gt |u| 1 with hu | hu
  · obtain ⟨_, hle⟩ := rpow_sub_sq_le (a := 1) zero_le_one hu (show (0 : ℝ) ≤ 5 / 2 by norm_num)
    simpa [unitBell, sinhTestWeight] using hle
  · rw [unitBell_eq_zero hu]; norm_num

private theorem unitBell_ge_of_abs_le_half {u : ℝ} (hu : |u| ≤ 1 / 2) :
    (1 / 32 : ℝ) ≤ unitBell u := by
  have h1 : (1 / 4 : ℝ) ≤ 1 ^ 2 - u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  have h2 : ((1 / 4 : ℝ) ^ (5 / 2 : ℝ)) ≤ (1 ^ 2 - u ^ 2) ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  have hval : ((1 / 4 : ℝ) ^ (5 / 2 : ℝ)) = 1 / 32 := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ (2 : ℕ) by norm_num, Real.rpow_natCast_mul (by norm_num)]
    norm_num
  simpa only [unitBell, sinhTestWeight, hval] using h2

private theorem hasDerivAt_unitBell (u : ℝ) :
    HasDerivAt unitBell (-(5 * u) * (1 ^ 2 - u ^ 2) ^ (3 / 2 : ℝ)) u := by
  have h := hasDerivAt_sub_sq_rpow 1 (5 / 2) (by norm_num) u
  rw [show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num] at h
  exact h.congr_deriv (by ring)

private theorem deriv_unitBell :
    deriv unitBell = fun u => -(5 * u) * (1 ^ 2 - u ^ 2) ^ (3 / 2 : ℝ) :=
  funext fun u => (hasDerivAt_unitBell u).deriv

private theorem hasDerivAt_deriv_unitBell (u : ℝ) :
    HasDerivAt (deriv unitBell) (unitBellDeriv2 u) u := by
  rw [deriv_unitBell]
  have hq : HasDerivAt (fun u : ℝ => -(5 * u)) (-5) u := by
    simpa using ((hasDerivAt_id u).const_mul 5).neg
  have h3 := hasDerivAt_sub_sq_rpow 1 (3 / 2) (by norm_num) u
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at h3
  refine (hq.mul h3).congr_deriv ?_
  simp only [unitBellDeriv2]
  ring

private theorem abs_unitBellDeriv2_le {u : ℝ} (hu : |u| ≤ 1) : |unitBellDeriv2 u| ≤ 20 := by
  obtain ⟨p3a, p3b⟩ := rpow_sub_sq_le (a := 1) zero_le_one hu (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  obtain ⟨p1a, p1b⟩ := rpow_sub_sq_le (a := 1) zero_le_one hu (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  simp only [Real.one_rpow] at p3b p1b
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
  unfold unitBellDeriv2
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul hu2 p1b p1a (sq_nonneg u)]

private theorem unitBellDeriv2_eq_zero {u : ℝ} (hu : 1 < |u|) : unitBellDeriv2 u = 0 := by
  have hopen : IsOpen {v : ℝ | 1 < |v|} := isOpen_lt continuous_const continuous_abs
  have hev : unitBell =ᶠ[nhds u] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hu) fun v hv => unitBell_eq_zero hv
  have hdd : deriv (deriv unitBell) u = unitBellDeriv2 u := (hasDerivAt_deriv_unitBell u).deriv
  rw [← hdd, hev.deriv.deriv_eq]
  simp

private theorem integral_unitBell_le : ∫ u, unitBell u ≤ 2 := by
  have h := integral_le_of_bound_on_Icc (a := 1) (M := 1) zero_le_one unitBell_nonneg
    (fun u _ => unitBell_le_one u) (fun u hu => unitBell_eq_zero hu)
  linarith

private theorem integrable_unitBell : Integrable unitBell := by
  refine unitBell_contDiff.continuous.integrable_of_hasCompactSupport ?_
  refine hasCompactSupport_of_support_subset_abs fun u hu => ?_
  by_contra h
  exact hu (unitBell_eq_zero (lt_of_not_ge h))

private theorem continuous_unitBellDeriv2 : Continuous unitBellDeriv2 := by
  unfold unitBellDeriv2
  have h3 : Continuous (fun u : ℝ => (1 ^ 2 - u ^ 2) ^ (3 / 2 : ℝ)) := by
    have hr : ContDiff ℝ 1 (fun x : ℝ => x ^ (3 / 2 : ℝ)) := by
      have := Real.contDiff_rpow_const_of_le (n := 1) (p := 3 / 2) (by norm_num)
      exact_mod_cast this
    exact hr.continuous.comp (by fun_prop)
  have h1 : Continuous (fun u : ℝ => (1 ^ 2 - u ^ 2) ^ (1 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)
  exact (continuous_const.mul h3).add ((continuous_const.mul (continuous_id.pow 2)).mul h1)

private theorem integrable_abs_unitBellDeriv2 : Integrable (fun u => |unitBellDeriv2 u|) := by
  refine continuous_unitBellDeriv2.abs.integrable_of_hasCompactSupport ?_
  refine hasCompactSupport_of_support_subset_abs fun u hu => ?_
  by_contra h
  exact hu (by rw [unitBellDeriv2_eq_zero (lt_of_not_ge h), abs_zero])

private theorem integral_abs_unitBellDeriv2_le : ∫ u, |unitBellDeriv2 u| ≤ 40 := by
  have h := integral_le_of_bound_on_Icc (a := 1) (M := 20) zero_le_one (fun _ => abs_nonneg _)
    (fun u hu => abs_unitBellDeriv2_le hu)
    (fun u hu => by rw [unitBellDeriv2_eq_zero hu, abs_zero])
  linarith

/-- Real endpoint-pair interferometer `φ(u + (a - 1)) + φ(u - (a - 1))`, supported in `[-a, a]`
with fixed-width bumps concentrated near `-a + 1` and `a - 1`. -/
def endpointPairReal (a u : ℝ) : ℝ :=
  unitBell (u + (a - 1)) + unitBell (u - (a - 1))

/-- Complex-valued `C²` endpoint-pair interferometer `endpointPairProfile a : ℝ → ℂ`. -/
def endpointPairProfile (a : ℝ) (u : ℝ) : ℂ := ((endpointPairReal a u : ℝ) : ℂ)

theorem endpointPairProfile_contDiff (a : ℝ) : ContDiff ℝ 2 (endpointPairProfile a) := by
  have hr : ContDiff ℝ 2 (endpointPairReal a) :=
    (unitBell_contDiff.comp (contDiff_id.add contDiff_const)).add
      (unitBell_contDiff.comp (contDiff_id.sub contDiff_const))
  exact Complex.ofRealCLM.contDiff.comp hr

theorem endpointPairReal_nonneg (a u : ℝ) : 0 ≤ endpointPairReal a u :=
  add_nonneg (unitBell_nonneg _) (unitBell_nonneg _)

theorem endpointPairReal_eq_zero {a u : ℝ} (ha : 2 ≤ a) (hu : a < |u|) :
    endpointPairReal a u = 0 := by
  unfold endpointPairReal
  rcases lt_abs.mp hu with h | h
  · rw [unitBell_eq_zero (by rw [abs_of_pos (by linarith)]; linarith),
      unitBell_eq_zero (by rw [abs_of_pos (by linarith)]; linarith), add_zero]
  · rw [unitBell_eq_zero (by rw [abs_of_neg (by linarith)]; linarith),
      unitBell_eq_zero (by rw [abs_of_neg (by linarith)]; linarith), add_zero]

theorem tsupport_endpointPairProfile_subset {a : ℝ} (ha : 2 ≤ a) :
    tsupport (endpointPairProfile a) ⊆ Icc (-a) a := by
  refine tsupport_subset_of_support_subset_abs fun u hu => ?_
  by_contra h
  exact hu (by simp [endpointPairProfile, endpointPairReal_eq_zero ha (lt_of_not_ge h)])

private theorem deriv_deriv_endpointPairProfile (a : ℝ) :
    deriv (deriv (endpointPairProfile a)) =
      fun u => (((unitBellDeriv2 (u + (a - 1)) + unitBellDeriv2 (u - (a - 1))) : ℝ) : ℂ) := by
  have hd1 : ∀ u : ℝ, HasDerivAt (endpointPairReal a)
      (deriv unitBell (u + (a - 1)) + deriv unitBell (u - (a - 1))) u := fun u => by
    have hL := ((hasDerivAt_unitBell (u + (a - 1))).comp u
      ((hasDerivAt_id u).add_const (a - 1))).congr_deriv
      (by rw [(hasDerivAt_unitBell _).deriv, mul_one])
    have hR := ((hasDerivAt_unitBell (u - (a - 1))).comp u
      ((hasDerivAt_id u).sub_const (a - 1))).congr_deriv
      (by rw [(hasDerivAt_unitBell _).deriv, mul_one])
    exact hL.add hR
  have hd1_eq : deriv (endpointPairReal a) =
      fun u => deriv unitBell (u + (a - 1)) + deriv unitBell (u - (a - 1)) :=
    funext fun u => (hd1 u).deriv
  have hd2 : ∀ u : ℝ, HasDerivAt (deriv (endpointPairReal a))
      (unitBellDeriv2 (u + (a - 1)) + unitBellDeriv2 (u - (a - 1))) u := fun u => by
    rw [hd1_eq]
    have hL := ((hasDerivAt_deriv_unitBell (u + (a - 1))).comp u
      ((hasDerivAt_id u).add_const (a - 1))).congr_deriv (mul_one _)
    have hR := ((hasDerivAt_deriv_unitBell (u - (a - 1))).comp u
      ((hasDerivAt_id u).sub_const (a - 1))).congr_deriv (mul_one _)
    exact hL.add hR
  have hc1 : deriv (endpointPairProfile a) =
      fun u => ((deriv (endpointPairReal a) u : ℝ) : ℂ) :=
    funext fun u => ((hd1 u).ofReal_comp).deriv.trans (by rw [(hd1 u).deriv])
  rw [hc1]
  exact funext fun u => ((hd2 u).ofReal_comp).deriv

/-- **Uniform `L²` and `C²` Norm Bounds for `endpointPairProfile a` (Independent of `a`).**
For every `a ≥ 2`:
1. `1 / 2048 ≤ ∫ t, ‖endpointPairProfile a t‖ ^ 2 ≤ 8`;
2. `4 * ((∫ u, ‖endpointPairProfile a u‖) + ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖) ≤ 336`. -/
theorem endpointPairProfile_norm_bounds {a : ℝ} (ha : 2 ≤ a) :
    (1 / 2048 ≤ ∫ t, ‖endpointPairProfile a t‖ ^ 2) ∧
      (∫ t, ‖endpointPairProfile a t‖ ^ 2 ≤ 8) ∧
      4 * ((∫ u, ‖endpointPairProfile a u‖) +
        ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖) ≤ 336 := by
  have hiL : Integrable (fun u => unitBell (u + (a - 1))) :=
    integrable_unitBell.comp_add_right (a - 1)
  have hiR : Integrable (fun u => unitBell (u - (a - 1))) :=
    integrable_unitBell.comp_sub_right (a - 1)
  have hsq_int : Integrable (fun t => ‖endpointPairProfile a t‖ ^ 2) :=
    ((endpointPairProfile_contDiff a).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun t ht => by
        simp [eq_zero_of_not_mem_Icc (tsupport_endpointPairProfile_subset ha) ht])
  have hint1 : ∫ u, ‖endpointPairProfile a u‖ ≤ 4 := by
    have heq : (fun u => ‖endpointPairProfile a u‖) = endpointPairReal a := by
      funext u
      rw [endpointPairProfile, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (endpointPairReal_nonneg a u)]
    rw [heq]
    unfold endpointPairReal
    rw [integral_add hiL hiR, integral_add_right_eq_self unitBell (a - 1),
      integral_sub_right_eq_self unitBell (a - 1)]
    linarith [integral_unitBell_le]
  have hint2_upper : ∫ t, ‖endpointPairProfile a t‖ ^ 2 ≤ 8 := by
    have hpt : ∀ t : ℝ, ‖endpointPairProfile a t‖ ^ 2 ≤
        2 * unitBell (t + (a - 1)) + 2 * unitBell (t - (a - 1)) := fun t => by
      rw [endpointPairProfile, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      unfold endpointPairReal
      have u0 := unitBell_nonneg (t + (a - 1))
      have u1 := unitBell_le_one (t + (a - 1))
      have v0 := unitBell_nonneg (t - (a - 1))
      have v1 := unitBell_le_one (t - (a - 1))
      nlinarith
    have hmono := integral_mono hsq_int ((hiL.const_mul 2).add (hiR.const_mul 2)) hpt
    rw [integral_add (hiL.const_mul 2) (hiR.const_mul 2), integral_const_mul, integral_const_mul,
      integral_add_right_eq_self unitBell (a - 1),
      integral_sub_right_eq_self unitBell (a - 1)] at hmono
    linarith [integral_unitBell_le]
  have hint2_lower : (1 / 2048 : ℝ) ≤ ∫ t, ‖endpointPairProfile a t‖ ^ 2 := by
    have hset : ∫ t in Icc (a - 5 / 4) (a - 3 / 4), (1 / 1024 : ℝ) ≤
        ∫ t in Icc (a - 5 / 4) (a - 3 / 4), ‖endpointPairProfile a t‖ ^ 2 := by
      refine setIntegral_mono_on (integrableOn_const (by simp))
        hsq_int.integrableOn measurableSet_Icc fun t ht => ?_
      have habs : |t - (a - 1)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hge : (1 / 32 : ℝ) ≤ endpointPairReal a t := by
        unfold endpointPairReal
        linarith [unitBell_nonneg (t + (a - 1)), unitBell_ge_of_abs_le_half habs]
      rw [endpointPairProfile, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      nlinarith
    have hle := setIntegral_le_integral hsq_int (Eventually.of_forall fun _ => sq_nonneg _)
    rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
      max_eq_left (by linarith)] at hset
    linarith
  have hd2_le : ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖ ≤ 80 := by
    rw [deriv_deriv_endpointPairProfile]
    have hdL : Integrable (fun u => |unitBellDeriv2 (u + (a - 1))|) :=
      integrable_abs_unitBellDeriv2.comp_add_right (a - 1)
    have hdR : Integrable (fun u => |unitBellDeriv2 (u - (a - 1))|) :=
      integrable_abs_unitBellDeriv2.comp_sub_right (a - 1)
    have hcont_sum : Continuous (fun u =>
        |unitBellDeriv2 (u + (a - 1)) + unitBellDeriv2 (u - (a - 1))|) :=
      ((continuous_unitBellDeriv2.comp (continuous_id.add continuous_const)).add
        (continuous_unitBellDeriv2.comp (continuous_id.sub continuous_const))).abs
    have hd_int : Integrable (fun u =>
        |unitBellDeriv2 (u + (a - 1)) + unitBellDeriv2 (u - (a - 1))|) := by
      refine (hdL.add hdR).mono' hcont_sum.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_add_le _ _
    have heq : (fun u => ‖(((unitBellDeriv2 (u + (a - 1)) +
        unitBellDeriv2 (u - (a - 1))) : ℝ) : ℂ)‖) =
        fun u => |unitBellDeriv2 (u + (a - 1)) + unitBellDeriv2 (u - (a - 1))| := by
      funext u
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [heq]
    have hmono := integral_mono hd_int (hdL.add hdR) fun u => abs_add_le _ _
    rw [integral_add hdL hdR,
      integral_add_right_eq_self (fun u => |unitBellDeriv2 u|) (a - 1),
      integral_sub_right_eq_self (fun u => |unitBellDeriv2 u|) (a - 1)] at hmono
    linarith [integral_abs_unitBellDeriv2_le]
  exact ⟨hint2_lower, hint2_upper, by linarith⟩

/-- Uniform autocorrelation plateau near the endpoint lag `2a - 2`: for every `a ≥ 2` and every
`v ∈ [2a - 9/4, 2a - 7/4]`, `1 / 2048 ≤ ‖EF.weilTest (endpointPairProfile a) (endpointPairProfile a) v‖`. -/
theorem norm_weilTest_endpointPairProfile_ge {a v : ℝ} (ha : 2 ≤ a)
    (hv : v ∈ Icc (2 * a - 9 / 4) (2 * a - 7 / 4)) :
    (1 / 2048 : ℝ) ≤ ‖EF.weilTest (endpointPairProfile a) (endpointPairProfile a) v‖ := by
  have hr_cont : Continuous (endpointPairReal a) :=
    (unitBell_contDiff.continuous.comp (continuous_id.add continuous_const)).add
      (unitBell_contDiff.continuous.comp (continuous_id.sub continuous_const))
  have hprod_int : Integrable (fun t => endpointPairReal a t * endpointPairReal a (t - v)) := by
    refine (hr_cont.mul (hr_cont.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun t ht => ?_
    have habs : a < |t| := by
      by_contra h
      exact ht (abs_le.mp (not_lt.mp h))
    simp [endpointPairReal_eq_zero ha habs]
  have hset : ∫ t in Icc (a - 5 / 4) (a - 3 / 4), (1 / 1024 : ℝ) ≤
      ∫ t in Icc (a - 5 / 4) (a - 3 / 4), endpointPairReal a t * endpointPairReal a (t - v) := by
    refine setIntegral_mono_on (integrableOn_const (by simp))
      hprod_int.integrableOn measurableSet_Icc fun t ht => ?_
    have habs1 : |t - (a - 1)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have habs2 : |(t - v) + (a - 1)| ≤ 1 / 2 :=
      abs_le.mpr ⟨by linarith [ht.1, hv.2], by linarith [ht.2, hv.1]⟩
    have hge1 : (1 / 32 : ℝ) ≤ endpointPairReal a t := by
      unfold endpointPairReal
      linarith [unitBell_nonneg (t + (a - 1)), unitBell_ge_of_abs_le_half habs1]
    have hge2 : (1 / 32 : ℝ) ≤ endpointPairReal a (t - v) := by
      unfold endpointPairReal
      linarith [unitBell_ge_of_abs_le_half habs2, unitBell_nonneg ((t - v) - (a - 1))]
    nlinarith
  have hle := setIntegral_le_integral hprod_int
    (Eventually.of_forall fun t => mul_nonneg (endpointPairReal_nonneg a t)
      (endpointPairReal_nonneg a (t - v)))
  rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul, max_eq_left (by linarith)] at hset
  have hreal_ge : (1 / 2048 : ℝ) ≤ ∫ t, endpointPairReal a t * endpointPairReal a (t - v) := by
    linarith
  rw [weilTest_apply]
  have hfun : (fun t => endpointPairProfile a t * conj (endpointPairProfile a (t - v))) =
      fun t => ((endpointPairReal a t * endpointPairReal a (t - v) : ℝ) : ℂ) := by
    funext t
    simp [endpointPairProfile, Complex.ofReal_mul]
  rw [hfun, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]
  exact hreal_ge

/-- **Smooth `C²` Endpoint-Interferometer `√X` Prime Saturation.** There exist `a₀ ≥ 2` and
`κ₀ > 0` such that for all `a ≥ a₀`, the `C²` profile `endpointPairProfile a` (supported in
`[-a, a]` with `B_f ≤ 336` independent of `a`) satisfies
`κ₀ e^a ∫ ‖endpointPairProfile a‖² < primeOnlyEnvelope - primePowerTailEnvelope`. -/
theorem exists_endpointPairProfile_saturation :
    ∃ a₀ κ₀ : ℝ, 2 ≤ a₀ ∧ 0 < κ₀ ∧ ∀ a : ℝ, a₀ ≤ a →
      κ₀ * Real.exp a * (∫ t, ‖endpointPairProfile a t‖ ^ 2) <
        primeOnlyEnvelope (endpointPairProfile a) ⌊Real.exp (2 * a)⌋₊ -
          primePowerTailEnvelope (endpointPairProfile a) ⌊Real.exp (2 * a)⌋₊ := by
  set δ₀ : ℝ := Real.exp (-7 / 8) - Real.exp (-9 / 8) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num))
  set κ₀ : ℝ := δ₀ / 16384 with hκ₀_def
  have hκ₀_pos : 0 < κ₀ := by positivity
  have ht_shift : ∀ c : ℝ, Tendsto (fun a : ℝ => FreeLagTrace.primeMass (a - c) / Real.exp a)
      atTop (𝓝 (2 * Real.exp (-c))) := fun c => by
    have hsub : Tendsto (fun a : ℝ => a + -c) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-c) tendsto_id
    have hm := (FreeLagTrace.tendsto_primeMass_div_exp.comp hsub).mul_const (Real.exp (-c))
    refine hm.congr fun a => ?_
    simp only [Function.comp_apply, ← sub_eq_add_neg]
    rw [sub_eq_add_neg, Real.exp_add, div_mul_eq_mul_div,
      mul_div_mul_right _ _ (Real.exp_pos (-c)).ne']
  have hdiff_tendsto : Tendsto
      (fun a : ℝ => FreeLagTrace.primeMass (a - 7 / 8) / Real.exp a -
        FreeLagTrace.primeMass (a - 9 / 8) / Real.exp a)
      atTop (𝓝 (2 * δ₀)) := by
    have h := (ht_shift (7 / 8)).sub (ht_shift (9 / 8))
    simpa [hδ₀_def, show -(7 / 8 : ℝ) = -7 / 8 by ring,
      show -(9 / 8 : ℝ) = -9 / 8 by ring, mul_sub] using h
  have hev := hdiff_tendsto.eventually (Ioi_mem_nhds (show δ₀ < 2 * δ₀ by linarith))
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.mp hev
  set a₀ : ℝ := max 2 (max a₁ (6 * 136 / (δ₀ / 2048) + 1))
  refine ⟨a₀, κ₀, le_max_left _ _, hκ₀_pos, fun a ha => ?_⟩
  have ha2 : 2 ≤ a := le_trans (le_max_left _ _) ha
  have ha_ge_a1 : a₁ ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ha
  have ha_poly : 6 * 136 / (δ₀ / 2048) + 1 ≤ a :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha
  have hshell_gt : δ₀ * Real.exp a <
      FreeLagTrace.primeMass (a - 7 / 8) - FreeLagTrace.primeMass (a - 9 / 8) := by
    have h1 : δ₀ < FreeLagTrace.primeMass (a - 7 / 8) / Real.exp a -
        FreeLagTrace.primeMass (a - 9 / 8) / Real.exp a := ha₁ a ha_ge_a1
    rw [← sub_div] at h1
    exact (lt_div_iff₀ (Real.exp_pos a)).mp h1
  set N := ⌊Real.exp (2 * a)⌋₊
  set N₁ := ⌊Real.exp (2 * a - 9 / 4)⌋₊
  set N₂ := ⌊Real.exp (2 * a - 7 / 4)⌋₊
  set S := Finset.Icc 2 N₂ \ Finset.Icc 2 N₁
  have hN₁_le_N₂ : N₁ ≤ N₂ := Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hN₂_le_N : N₂ ≤ N := Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hIcc_sub : Finset.Icc 2 N₁ ⊆ Finset.Icc 2 N₂ :=
    Finset.Icc_subset_Icc_right hN₁_le_N₂
  have hS_sum : ∑ n ∈ S, (Λ n : ℝ) / Real.sqrt n =
      FreeLagTrace.primeMass (a - 7 / 8) - FreeLagTrace.primeMass (a - 9 / 8) := by
    have hsd := Finset.sum_sdiff hIcc_sub (f := fun n => (Λ n : ℝ) / Real.sqrt n)
    have hm1 : FreeLagTrace.primeMass (a - 9 / 8) =
        ∑ n ∈ Finset.Icc 2 N₁, (Λ n : ℝ) / Real.sqrt n := by
      simp only [FreeLagTrace.primeMass, FreeLagTrace.primeCutoff, N₁,
        show 2 * (a - 9 / 8) = 2 * a - 9 / 4 by ring]
    have hm2 : FreeLagTrace.primeMass (a - 7 / 8) =
        ∑ n ∈ Finset.Icc 2 N₂, (Λ n : ℝ) / Real.sqrt n := by
      simp only [FreeLagTrace.primeMass, FreeLagTrace.primeCutoff, N₂,
        show 2 * (a - 7 / 8) = 2 * a - 7 / 4 by ring]
    linarith
  have hS_split := (Finset.sum_filter_add_sum_filter_not S Nat.Prime
    (fun n => (Λ n : ℝ) / Real.sqrt n)).symm
  have hS_comp_le : ∑ n ∈ S.filter (fun n => ¬ Nat.Prime n), (Λ n : ℝ) / Real.sqrt n ≤
      4 * a + 4 * a ^ 2 := by
    have hsub_comp : S.filter (fun n => ¬ Nat.Prime n) ⊆ compIndices N := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc] at hn
      rw [compIndices, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hn.1.1.1, hn.1.1.2.trans hN₂_le_N⟩, hn.2⟩
    have hle1 : ∑ n ∈ S.filter (fun n => ¬ Nat.Prime n), (Λ n : ℝ) / Real.sqrt n ≤
        ∑ n ∈ compIndices N, (Λ n : ℝ) / Real.sqrt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub_comp fun _ _ _ =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    have hc := sum_compIndices_vonMangoldt_div_sqrt_le
      (Real.one_le_exp (show 0 ≤ 2 * a by linarith))
    rw [Real.log_exp] at hc
    calc ∑ n ∈ S.filter (fun n => ¬ Nat.Prime n), (Λ n : ℝ) / Real.sqrt n
        ≤ 2 * (2 * a) + (2 * a) ^ 2 := hle1.trans hc
      _ = 4 * a + 4 * a ^ 2 := by ring
  have hprime_env_ge : (1 / 1024 : ℝ) *
        (FreeLagTrace.primeMass (a - 7 / 8) - FreeLagTrace.primeMass (a - 9 / 8) -
          (4 * a + 4 * a ^ 2)) ≤
      primeOnlyEnvelope (endpointPairProfile a) N := by
    rw [primeOnlyEnvelope_eq_sum_two_mul_norm_true]
    have hsub_pr : S.filter Nat.Prime ⊆ primeIndices N := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc] at hp
      rw [primeIndices, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp.1.1.1, hp.1.1.2.trans hN₂_le_N⟩, hp.2⟩
    have h1 : ∑ p ∈ S.filter Nat.Prime, 2 * ‖primeCoeff (endpointPairProfile a) (p, true)‖ ≤
        ∑ p ∈ primeIndices N, 2 * ‖primeCoeff (endpointPairProfile a) (p, true)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub_pr fun _ _ _ => by positivity
    have h2 : (1 / 1024 : ℝ) * ∑ p ∈ S.filter Nat.Prime, (Λ p : ℝ) / Real.sqrt p ≤
        ∑ p ∈ S.filter Nat.Prime, 2 * ‖primeCoeff (endpointPairProfile a) (p, true)‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hp
      have hp2 : 2 ≤ p := hp.1.1.1
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hp_gt : ¬ p ≤ N₁ := fun hle => hp.1.2 ⟨hp2, hle⟩
      have hexp_lt : Real.exp (2 * a - 9 / 4) < (p : ℝ) := by
        by_contra hle
        exact hp_gt (Nat.le_floor (not_lt.mp hle))
      have hlog_ge : 2 * a - 9 / 4 ≤ Real.log p := by
        rw [← Real.log_exp (2 * a - 9 / 4)]
        exact (Real.log_lt_log (Real.exp_pos _) hexp_lt).le
      have hlog_le : Real.log p ≤ 2 * a - 7 / 4 := by
        have hp_le : (p : ℝ) ≤ Real.exp (2 * a - 7 / 4) :=
          (by exact_mod_cast hp.1.1.2 : (p : ℝ) ≤ N₂).trans
            (Nat.floor_le (Real.exp_pos _).le)
        rw [← Real.log_exp (2 * a - 7 / 4)]
        exact Real.log_le_log hp_pos hp_le
      have hwt := norm_weilTest_endpointPairProfile_ge ha2 ⟨hlog_ge, hlog_le⟩
      have hw0 : 0 ≤ (Λ p : ℝ) / Real.sqrt p :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
      simp only [primeCoeff, primeFreq, ↓reduceIte, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hw0]
      nlinarith
    have h3 : FreeLagTrace.primeMass (a - 7 / 8) - FreeLagTrace.primeMass (a - 9 / 8) -
          (4 * a + 4 * a ^ 2) ≤
        ∑ p ∈ S.filter Nat.Prime, (Λ p : ℝ) / Real.sqrt p := by
      linarith [hS_sum, hS_split, hS_comp_le]
    linarith [mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1 / 1024)]
  obtain ⟨_, hL2_le, _⟩ := endpointPairProfile_norm_bounds ha2
  have hfc := hasCompactSupport_of_tsupport_subset_Icc (tsupport_endpointPairProfile_subset ha2)
  have htail_le : primePowerTailEnvelope (endpointPairProfile a) N ≤
      16 * (4 * a + 4 * a ^ 2) := by
    have ht := primePowerTailEnvelope_exp_le (by linarith : (0 : ℝ) ≤ a)
      (endpointPairProfile_contDiff a).continuous hfc
    have h4a : 0 ≤ 4 * a + 4 * a ^ 2 := by positivity
    nlinarith
  have hexp_cube : a ^ 3 / 6 ≤ Real.exp a := by
    have hsum := Real.sum_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ a) 4
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      Nat.factorial, Nat.cast_one, Nat.cast_ofNat] at hsum
    linarith [sq_nonneg a]
  have hpoly_lt : 17 * (4 * a + 4 * a ^ 2) < (δ₀ / 2048) * Real.exp a := by
    have hquad : 17 * (4 * a + 4 * a ^ 2) ≤ 136 * a ^ 2 := by nlinarith
    have ha_gt : 6 * 136 / (δ₀ / 2048) < a := by linarith
    have hmul : 6 * 136 < (δ₀ / 2048) * a := (div_lt_iff₀ (by positivity)).mp ha_gt
    have hcube_gt : 136 * a ^ 2 < (δ₀ / 2048) * (a ^ 3 / 6) := by
      have ha2_pos : 0 < a ^ 2 := by positivity
      have := mul_lt_mul_of_pos_right hmul ha2_pos
      linarith
    have hcube_exp : (δ₀ / 2048) * (a ^ 3 / 6) ≤ (δ₀ / 2048) * Real.exp a :=
      mul_le_mul_of_nonneg_left hexp_cube (by positivity)
    linarith
  have hL2_nn : 0 ≤ ∫ t, ‖endpointPairProfile a t‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hκ_le : κ₀ * Real.exp a * (∫ t, ‖endpointPairProfile a t‖ ^ 2) ≤
      (δ₀ / 2048) * Real.exp a := by
    rw [hκ₀_def]
    have hexp_pos : 0 < Real.exp a := Real.exp_pos a
    nlinarith
  linarith

/-- **Eventual-in-Height Power-Saving Impossibility for Smooth `C²` Profiles.** Even for the smooth
`C²` family `endpointPairProfile a` (with `B_f ≤ 336` independent of `a`), no power saving
`(primePolynomial (endpointPairProfile a) ⌊e^{2a}⌋₊ ξ).re ≤ C e^{θ a} ∫ ‖endpointPairProfile a‖²`
with `θ < 1` can hold eventually in height `ξ ≥ T₁ a`. -/
theorem not_exists_eventually_atTop_endpointPair_power_saving {θ : ℝ} (hθ : θ < 1) :
    ¬ ∃ (C : ℝ) (T₁ : ℝ → ℝ), ∀ a : ℝ, 2 ≤ a → ∀ ξ : ℝ, T₁ a ≤ ξ →
      (primePolynomial (endpointPairProfile a) ⌊Real.exp (2 * a)⌋₊ ξ).re ≤
        C * Real.exp (θ * a) * ∫ t, ‖endpointPairProfile a t‖ ^ 2 := by
  rintro ⟨C, T₁, hC⟩
  obtain ⟨a₀, κ₀, ha₀2, hκ₀, hsat⟩ := exists_endpointPairProfile_saturation
  have hgrow : Tendsto (fun a : ℝ => Real.exp ((1 - θ) * a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hθ))
  have hev := (hgrow.eventually (eventually_gt_atTop ((|C| + 1) / κ₀))).and
    (eventually_ge_atTop a₀)
  obtain ⟨a, ha_exp, ha_ge⟩ := hev.exists
  have ha2 : 2 ≤ a := ha₀2.trans ha_ge
  obtain ⟨hL2_pos, _, _⟩ := endpointPairProfile_norm_bounds ha2
  have hN_pos : 0 < ∫ t, ‖endpointPairProfile a t‖ ^ 2 := by linarith
  have hexp_split : Real.exp a = Real.exp (θ * a) * Real.exp ((1 - θ) * a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hC_lt : C * Real.exp (θ * a) * (∫ t, ‖endpointPairProfile a t‖ ^ 2) <
      κ₀ * Real.exp a * (∫ t, ‖endpointPairProfile a t‖ ^ 2) := by
    have h1 : |C| + 1 < κ₀ * Real.exp ((1 - θ) * a) := by
      have := (div_lt_iff₀ hκ₀).mp ha_exp
      linarith
    have h2 : C < κ₀ * Real.exp ((1 - θ) * a) := lt_of_le_of_lt (le_abs_self C) (by linarith)
    have h3 : C * Real.exp (θ * a) < κ₀ * Real.exp a := by
      rw [hexp_split]
      have := mul_lt_mul_of_pos_right h2 (Real.exp_pos (θ * a))
      linarith
    exact mul_lt_mul_of_pos_right h3 hN_pos
  have hB := lt_trans hC_lt (hsat a ha_ge)
  obtain ⟨L, _, hdense⟩ := exists_relDense_re_primePolynomial_gt_and_lt
    (endpointPairProfile a) ⌊Real.exp (2 * a)⌋₊ hB
  obtain ⟨⟨ξ, hξmem, hξgt⟩, -⟩ := hdense (T₁ a)
  linarith [hC a ha2 ξ hξmem.1]

/-! ## §2. Two-Sided `(1 + 2π|ξ|)⁻⁴` High-Height Pole Decay, Forbidden Desert, and Height Escape -/

/-- **Two-Sided `(1 + 2π|ξ|)⁻⁴` High-Height Decay of the Shifted Pole Terms.**
Shifting `paperFT (heightShift ξ f) (±I/2) = paperFT f (±I/2 + 2πξ)` before applying `C²`
transform decay eliminates both the height-independent `-2 S(a)` lower barrier and the
`2 e^a (∫ ‖f‖)²` upper barrier:
`|Re(h_k(i/2) + h_k(-i/2))| ≤ 2 e^a B_f² / (1 + 2π|ξ|)⁴`. -/
theorem abs_re_pole_terms_heightShift_le_decay {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    |(paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (I / 2) +
      paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (-I / 2)).re| ≤
      2 * Real.exp a *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 := by
  set g := heightShift ξ f
  have hg : ContDiff ℝ 2 g := heightShift_contDiff hf ξ
  have hgs : tsupport g ⊆ Icc (-a) a := (tsupport_heightShift_subset ξ f).trans hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hfa : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => by
    by_contra h
    exact hu (eq_zero_of_not_mem_Icc hfs fun hm => h (abs_le.mpr ⟨hm.1, hm.2⟩))
  have hc1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [EF.paperFT_weilTest hg.continuous hg.continuous hgc hgc,
    EF.paperFT_weilTest hg.continuous hg.continuous hgc hgc, hc1, hc2,
    paperFT_heightShift, paperFT_heightShift]
  set B := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)
  have him1 : |(I / 2 + 2 * π * (ξ : ℂ)).im| ≤ 1 / 2 := by simp
  have him2 : |(-I / 2 + 2 * π * (ξ : ℂ)).im| ≤ 1 / 2 := by simp; norm_num
  have hre1 : |(I / 2 + 2 * π * (ξ : ℂ)).re| = 2 * π * |ξ| := by
    simp [abs_mul, abs_of_pos Real.two_pi_pos]
  have hre2 : |(-I / 2 + 2 * π * (ξ : ℂ)).re| = 2 * π * |ξ| := by
    simp [abs_mul, abs_of_pos Real.two_pi_pos]
  have hb1 := norm_paperFT_le_of_abs_im_le hf ha hfa him1
  have hb2 := norm_paperFT_le_of_abs_im_le hf ha hfa him2
  rw [hre1] at hb1
  rw [hre2] at hb2
  have habs : |(paperFT f (I / 2 + 2 * π * ξ) * conj (paperFT f (-I / 2 + 2 * π * ξ)) +
      paperFT f (-I / 2 + 2 * π * ξ) * conj (paperFT f (I / 2 + 2 * π * ξ))).re| ≤
      2 * (‖paperFT f (I / 2 + 2 * π * ξ)‖ * ‖paperFT f (-I / 2 + 2 * π * ξ)‖) := by
    refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    linarith
  have hprod : ‖paperFT f (I / 2 + 2 * π * ξ)‖ * ‖paperFT f (-I / 2 + 2 * π * ξ)‖ ≤
      (Real.exp (a / 2) * B / (1 + 2 * π * |ξ|) ^ 2) *
        (Real.exp (a / 2) * B / (1 + 2 * π * |ξ|) ^ 2) := by
    have hB0 : 0 ≤ B := by
      have : 0 ≤ (∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖ :=
        add_nonneg (integral_nonneg fun _ => norm_nonneg _)
          (integral_nonneg fun _ => norm_nonneg _)
      positivity
    exact mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
  have hsq : 2 * ((Real.exp (a / 2) * B / (1 + 2 * π * |ξ|) ^ 2) *
      (Real.exp (a / 2) * B / (1 + 2 * π * |ξ|) ^ 2)) =
      2 * Real.exp a * B ^ 2 / (1 + 2 * π * |ξ|) ^ 4 := by
    have hexp : Real.exp (a / 2) * Real.exp (a / 2) = Real.exp a := by
      rw [← Real.exp_add, show a / 2 + a / 2 = a by ring]
    calc 2 * ((Real.exp (a / 2) * B / (1 + 2 * π * |ξ|) ^ 2) *
          (Real.exp (a / 2) * B / (1 + 2 * π * |ξ|) ^ 2))
        = 2 * (Real.exp (a / 2) * Real.exp (a / 2)) * B ^ 2 / (1 + 2 * π * |ξ|) ^ 4 := by ring
      _ = 2 * Real.exp a * B ^ 2 / (1 + 2 * π * |ξ|) ^ 4 := by rw [hexp]
  linarith

/-- Pure shifted-symbol integral lower bound (free of pole terms): if
`w(τ) ≥ (log(1 + |τ|/4) - E) / (2π)`, then
`∫ ‖h_f(τ + 2πξ)‖² w(τ) dτ ≥ (log(1 + π|ξ|/4) - E) ‖f‖₂² - B_f² / (8(1 + π|ξ|))`. -/
theorem integral_symbol_heightShift_ge {a E : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) {w : ℝ → ℝ}
    (hw : ∀ τ, (Real.log (1 + |τ| / 4) - E) / (2 * π) ≤ w τ)
    (hwi : Integrable fun τ : ℝ => ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * w τ) :
    (Real.log (1 + π * |ξ| / 4) - E) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
      ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * w τ := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkdf : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkcf : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  set y : ℝ := 2 * π * ξ with hy
  set N := ∫ t, ‖f t‖ ^ 2 with hN
  set B := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hB
  set F : ℝ → ℝ := fun σ => ‖paperFT f σ‖ ^ 2 with hFdef
  set ℓ := Real.log (1 + |y| / 8) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith [abs_nonneg y])
  have hπ : 0 < 2 * π := Real.two_pi_pos
  have hFi : Integrable F := by
    refine (EF.integrable_paperFT_ofReal
      (EF.integrable_fourier_of_contDiff_two hkdf hkcf)).re.congr (Eventually.of_forall fun σ => ?_)
    simp only [paperFT_weilTest_self_ofReal hf.continuous hfc σ, RCLike.re_to_complex,
      Complex.ofReal_re, hFdef]
  have hFyi : Integrable fun τ : ℝ => F (τ + y) := hFi.comp_add_right y
  set Cu : ℝ := B ^ 2 / (1 + |y| / 2) ^ 2 with hCu
  have hui : Integrable fun τ : ℝ => Cu * (1 + (τ + y) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.const_mul Cu).comp_add_right y
  set c₁ := (ℓ - E) / (2 * π) with hc₁
  set c₂ := ℓ / (2 * π) with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hsf : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => by
    by_contra h
    exact hu (eq_zero_of_not_mem_Icc hfs fun hm => h (abs_le.mpr ⟨hm.1, hm.2⟩))
  have hptw : ∀ τ : ℝ, c₁ * F (τ + y) - c₂ * (Cu * (1 + (τ + y) ^ 2)⁻¹) ≤ F (τ + y) * w τ := by
    intro τ
    have hmu := hw τ
    have hF0 : 0 ≤ F (τ + y) := sq_nonneg _
    have hu0 : 0 ≤ Cu * (1 + (τ + y) ^ 2)⁻¹ := by positivity
    by_cases hσ : |τ + y| ≤ |y| / 2
    · have hτ : |y| / 2 ≤ |τ| := by
        have := abs_sub_abs_le_abs_sub y (τ + y)
        rw [show y - (τ + y) = -τ by ring, abs_neg] at this
        linarith
      have hlog : ℓ ≤ Real.log (1 + |τ| / 4) :=
        Real.log_le_log (by linarith [abs_nonneg y]) (by linarith)
      have hμ : c₁ ≤ w τ :=
        le_trans (by rw [hc₁]; exact div_le_div_of_nonneg_right (by linarith) hπ.le) hmu
      nlinarith [mul_le_mul_of_nonneg_left hμ hF0]
    · rw [not_le] at hσ
      have hlog0 : 0 ≤ Real.log (1 + |τ| / 4) := Real.log_nonneg (by linarith [abs_nonneg τ])
      have hμ : c₁ - c₂ ≤ w τ :=
        le_trans (by rw [hc₁, hc₂, ← sub_div]; exact div_le_div_of_nonneg_right (by linarith) hπ.le)
          hmu
      have hdec : F (τ + y) ≤ Cu * (1 + (τ + y) ^ 2)⁻¹ := by
        have h := norm_paperFT_le_decay hf hsf (((τ + y : ℝ)) : ℂ)
        simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
          Complex.ofReal_re] at h
        have hsq : F (τ + y) ≤ (B / (1 + |τ + y|) ^ 2) ^ 2 := by
          rw [hFdef]
          exact pow_le_pow_left₀ (norm_nonneg _) h 2
        refine hsq.trans ?_
        rw [div_pow, hCu]
        calc B ^ 2 / ((1 + |τ + y|) ^ 2) ^ 2 = B ^ 2 * (1 / ((1 + |τ + y|) ^ 2) ^ 2) := by ring
          _ ≤ B ^ 2 * (1 / (1 + |y| / 2) ^ 2 * (1 + (τ + y) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left (inv_one_add_abs_pow_four_le hσ) (sq_nonneg B)
          _ = B ^ 2 / (1 + |y| / 2) ^ 2 * (1 + (τ + y) ^ 2)⁻¹ := by ring
      nlinarith [mul_le_mul_of_nonneg_left hμ hF0, mul_le_mul_of_nonneg_left hdec hc₂0]
  have hlow : Integrable fun τ : ℝ => c₁ * F (τ + y) - c₂ * (Cu * (1 + (τ + y) ^ 2)⁻¹) :=
    (hFyi.const_mul c₁).sub (hui.const_mul c₂)
  have hmono := integral_mono hlow hwi hptw
  have hFint : ∫ τ : ℝ, F (τ + y) = 2 * π * N := by
    rw [integral_add_right_eq_self (fun σ => F σ) y, hFdef]
    exact integral_norm_sq_paperFT_eq hf hfs
  have huint : ∫ τ : ℝ, Cu * (1 + (τ + y) ^ 2)⁻¹ = Cu * π := by
    rw [integral_add_right_eq_self (fun σ => Cu * (1 + σ ^ 2)⁻¹) y, integral_const_mul,
      integral_univ_inv_one_add_sq]
  rw [integral_sub (hFyi.const_mul c₁) (hui.const_mul c₂), integral_const_mul,
    integral_const_mul, hFint, huint] at hmono
  have hyabs : |y| = 2 * π * |ξ| := by rw [hy, abs_mul, abs_of_pos hπ]
  have hℓy : ℓ ≤ |y| / 8 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + |y| / 8)
    linarith
  have htail : c₂ * (Cu * π) ≤ B ^ 2 / (8 * (1 + π * |ξ|)) := by
    have hy2 : 1 + |y| / 2 = 1 + π * |ξ| := by rw [hyabs]; ring
    rw [hc₂, hCu, hy2]
    have hℓ' : ℓ ≤ π * |ξ| / 4 := by rw [hyabs] at hℓy; linarith
    set p := 1 + π * |ξ|
    have hrw : ℓ / (2 * π) * (B ^ 2 / p ^ 2 * π) = ℓ * B ^ 2 / (2 * p ^ 2) := by field_simp
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    have h8 : 8 * ℓ ≤ 2 * p := by
      have : 0 ≤ π * |ξ| := by positivity
      linarith
    have := mul_le_mul_of_nonneg_left h8 (by positivity : 0 ≤ B ^ 2 * p)
    nlinarith [this]
  have hlogeq : Real.log (1 + π * |ξ| / 4) = ℓ := by
    rw [hℓ, hyabs]
    congr 1
    ring
  rw [hlogeq]
  have hc₁N : c₁ * (2 * π * N) = (ℓ - E) * N := by rw [hc₁]; field_simp
  linarith

/-- **Barrier-Free Lower Bound on `Re A_f(ξ)` (No `-2 S(a)` Loss).**
Replacing `-2 S(a)` by high-height pole decay gives
`Re A_f(ξ) ≥ (log(1 + π|ξ|/4) - 10) ‖f‖₂² - B_f²/(8(1 + π|ξ|)) - 2 e^a B_f²/(1 + 2π|ξ|)⁴`. -/
theorem re_archPart_ge_decay {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (Real.log (1 + π * |ξ| / 4) - 10) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) -
      2 * Real.exp a *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 ≤
      (archPart f ξ).re := by
  have hg : ContDiff ℝ 2 (heightShift ξ f) := heightShift_contDiff hf ξ
  have hgs : tsupport (heightShift ξ f) ⊆ Icc (-a) a :=
    (tsupport_heightShift_subset ξ f).trans hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd := EF.weilTest_contDiff hg hg.continuous hgc
  have hkc := EF.weilTest_hasCompactSupport hgc hgc
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  have hwi : Integrable fun τ : ℝ => ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    refine (EF.integrable_paperFT_mul_mu hkd hkc gammaFacts).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have hint := integral_symbol_heightShift_ge (E := 10) hf hfs ξ mu_ge_log hwi
  have hpole := (abs_le.mp (abs_re_pole_terms_heightShift_le_decay ha hf hfs ξ)).1
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
      (mu τ : ℂ)).re = ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    have hfun : (fun τ : ℝ => paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
        (mu τ : ℂ)) = fun τ : ℝ =>
        ((‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ : ℝ) : ℂ) := by
      funext τ
      rw [hval, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  rw [archPart, Complex.add_re, hμre]
  linarith

/-- **Barrier-Free Upper Bound on `Re A_f(ξ)` (No `2 e^a ‖f‖₁²` Loss).**
Replacing `re_pole_terms_heightShift_le` by `abs_re_pole_terms_heightShift_le_decay` yields
`Re A_f(ξ) ≤ 2 e^a B_f²/(1 + 2π|ξ|)⁴ + B_f²(1/2 + πC) + ‖f‖₂² log(1 + 2π|ξ|)`. -/
theorem re_archPart_le_decay {C a : ℝ} (ha : 0 ≤ a) (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (archPart f ξ).re ≤
      2 * Real.exp a *
          (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 +
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) +
        (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|) := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
      (mu τ : ℂ)).re = ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    have hfun : (fun τ : ℝ => paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
        (mu τ : ℂ)) = fun τ : ℝ =>
        ((‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ : ℝ) : ℂ) := by
      funext τ
      rw [hval, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  rw [archPart, Complex.add_re, hμre]
  have hpole := (abs_le.mp (abs_re_pole_terms_heightShift_le_decay ha hf hfs ξ)).2
  have harch := integral_norm_sq_paperFT_shift_mul_mu_le hC0 hC hf hfs ξ
  linarith

/-- Single-height lower bound on `Re W_ζ(S_ξ f, S_ξ f)` from a symbol bound, with `(1 + 2π|ξ|)⁻⁴`
pole decay instead of `-2 S(a)`. -/
theorem zetaZeroConfig_re_W_heightShift_ge_of_symbol_decay {a E : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ)
    (hE : ∀ τ, (Real.log (1 + |τ| / 4) - E) / (2 * π) ≤ mu τ + PX (Real.exp (2 * a)) τ) :
    (Real.log (1 + π * |ξ| / 4) - E) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) -
      2 * Real.exp a *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 ≤
      (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  have hg : ContDiff ℝ 2 (heightShift ξ f) := heightShift_contDiff hf ξ
  have hgs : tsupport (heightShift ξ f) ⊆ Icc (-a) a :=
    (tsupport_heightShift_subset ξ f).trans hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd := EF.weilTest_contDiff hg hg.continuous hgc
  have hkc := EF.weilTest_hasCompactSupport hgc hgc
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  have hsym : Integrable fun τ : ℝ => ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 *
      (mu τ + PX (Real.exp (2 * a)) τ) := by
    refine (integrable_paperFT_mul_mu_add_PX hkd hkc (2 * a)).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have hint := integral_symbol_heightShift_ge hf hfs ξ hE hsym
  have hpole := (abs_le.mp (abs_re_pole_terms_heightShift_le_decay ha hf hfs ξ)).1
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
      ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ)).re =
      ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * (mu τ + PX (Real.exp (2 * a)) τ) := by
    have hfun : (fun τ : ℝ => paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
        ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ)) = fun τ : ℝ =>
        ((‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * (mu τ + PX (Real.exp (2 * a)) τ) : ℝ) : ℂ) := by
      funext τ
      rw [hval, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  rw [zetaZeroConfig_W_eq_pole_add_integral hg hgs, Complex.add_re, hμre]
  linarith

/-- **Unconditional Single-Height Positivity at the Optimal `(4 + ε) e^a` Horizon Coefficient.**
Eliminates the `2 S(a)` pole term from `zetaZeroConfig_re_W_heightShift_nonneg_of_horizon`:
for every `ε > 0`, there is `C ≥ 0` such that `Re W_ζ(S_ξ f, S_ξ f) ≥ 0` whenever
`C + (4 + ε) e^a + 2 ≤ log(1 + π|ξ|/4)` and both high-height tail terms are bounded by `‖f‖₂²`. -/
theorem zetaZeroConfig_re_W_heightShift_nonneg_of_sharp_horizon {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ}, 0 ≤ a → ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f →
      tsupport f ⊆ Icc (-a) a → ∀ ξ : ℝ,
        C + (4 + ε) * Real.exp a + 2 ≤ Real.log (1 + π * |ξ| / 4) →
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
          ∫ t, ‖f t‖ ^ 2 →
        2 * Real.exp a *
            (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 ≤
          ∫ t, ‖f t‖ ^ 2 →
        0 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  obtain ⟨C, hC0, hC⟩ := exists_mu_add_PX_ge hε
  refine ⟨C, hC0, fun {a} ha {f} hf hfs ξ hlog htail hpole => ?_⟩
  have hsq : Real.sqrt (Real.exp (2 * a)) = Real.exp a := by
    rw [show 2 * a = a + a by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos a).le]
  have hbound := zetaZeroConfig_re_W_heightShift_ge_of_symbol_decay ha hf hfs ξ fun τ => by
    simpa [hsq] using hC _ (Real.exp_pos (2 * a)).le τ
  have hN0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Forbidden Post-Pole Desert.** Once `2 e^a B_f² ≤ (1 + 2π|ξ|)⁴`, nonnegativity
`Re W_ζ(S_ξ f, S_ξ f) ≥ 0` forbids `(primePolynomial f ⌊e^{2a}⌋₊ ξ).re > B` throughout the
intermediate height desert where `‖f‖₂² log(1 + 2π|ξ|) ≤ B - 1 - B_f²(1/2 + πC)`. -/
theorem re_primePolynomial_le_in_post_pole_desert_of_re_W_nonneg {C a B : ℝ}
    (ha : 0 ≤ a) (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) {ξ : ℝ}
    (hpole : 2 * Real.exp a *
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 ≤ (1 + 2 * π * |ξ|) ^ 4)
    (hdesert : (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|) ≤
      B - 1 - (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C))
    (hW : 0 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re) :
    (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ B := by
  rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re] at hW
  have harch := re_archPart_le_decay ha hC0 hC hf hfs ξ
  have hp1 : 2 * Real.exp a *
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 ≤ 1 :=
    (div_le_one (by positivity)).mpr hpole
  linarith

private theorem post_pole_bound_of_ge {a B : ℝ} (ha : 0 ≤ a) {ξ : ℝ}
    (hξ : Real.exp a + B ^ 2 ≤ ξ) :
    2 * Real.exp a * B ^ 2 ≤ (1 + 2 * π * |ξ|) ^ 4 := by
  have he1 : 1 ≤ Real.exp a := Real.one_le_exp ha
  set U := Real.exp a + B ^ 2
  have hU1 : 1 ≤ U := by linarith [sq_nonneg B]
  have hξ0 : 0 ≤ ξ := by linarith
  have habs : |ξ| = ξ := abs_of_nonneg hξ0
  rw [habs]
  have hbase : U ≤ 1 + 2 * π * ξ := by nlinarith [Real.pi_gt_three]
  have hU2 : 2 * Real.exp a * B ^ 2 ≤ U ^ 2 := by
    have : 0 ≤ (Real.exp a - B ^ 2) ^ 2 := sq_nonneg _
    nlinarith
  have hpow2 : U ^ 2 ≤ (1 + 2 * π * ξ) ^ 2 := pow_le_pow_left₀ (by linarith) hbase 2
  have hp1 : 1 ≤ (1 + 2 * π * ξ) ^ 2 := by nlinarith
  have hpow4 : (1 + 2 * π * ξ) ^ 2 ≤ (1 + 2 * π * ξ) ^ 4 := by nlinarith
  linarith

/-- **Barrier-Free Post-Pole Exponential Height Escape Dichotomy.**
Sampling syndetic Bohr–Kronecker peaks past `Real.exp a + B_f²` removes the `2 e^a (∫ ‖f‖)²`
deduction of `exists_re_W_neg_or_height_escape`: for every `T_min : ℝ` and
`B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ - primePowerTailEnvelope f ⌊e^{2a}⌋₊`, there exists
`ξ > max T_min 0` at which `(primePolynomial f ⌊e^{2a}⌋₊ ξ).re > B` and either
`Re W_ζ(S_ξ f, S_ξ f) < 0` or `B - 1 - B_f²(1/2 + πC) < ‖f‖₂² log(1 + 2πξ)`. -/
theorem exists_gt_height_re_W_neg_or_sharp_escape {C a B : ℝ} (ha : 0 ≤ a) (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊)
    (T_min : ℝ) :
    ∃ ξ : ℝ, max T_min 0 < ξ ∧ B < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ∧
      ((zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re < 0 ∨
        B - 1 - (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) <
          (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * ξ)) := by
  set Bf := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)
  set T₀ := max (max T_min 0 + 1) (Real.exp a + Bf ^ 2)
  obtain ⟨L, _, hdense⟩ := exists_relDense_re_primePolynomial_gt_and_lt f ⌊Real.exp (2 * a)⌋₊ hB
  obtain ⟨⟨ξ, hξmem, hξB⟩, -⟩ := hdense T₀
  have hξ_gt : max T_min 0 < ξ := by
    have : max T_min 0 + 1 ≤ T₀ := le_max_left _ _
    linarith [hξmem.1]
  have hξ_pole : Real.exp a + Bf ^ 2 ≤ ξ := le_trans (le_max_right _ _) hξmem.1
  refine ⟨ξ, hξ_gt, hξB, ?_⟩
  by_cases hW : (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re < 0
  · exact Or.inl hW
  · refine Or.inr ?_
    by_contra hle
    have hξ0 : 0 ≤ ξ := le_trans (le_max_right T_min 0) hξ_gt.le
    have hdesert : (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|) ≤
        B - 1 - Bf ^ 2 * (1 / 2 + π * C) := by
      rw [abs_of_nonneg hξ0]
      exact not_lt.mp hle
    have hp := post_pole_bound_of_ge ha hξ_pole
    have hpub := re_primePolynomial_le_in_post_pole_desert_of_re_W_nonneg ha hC0 hC hf hfs hp
      hdesert (not_lt.mp hW)
    linarith

/-- Under `RiemannHypothesis`, for every `T_min : ℝ` and
`B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ - primePowerTailEnvelope f ⌊e^{2a}⌋₊`, there exists
`ξ > max T_min 0` with `B - 1 - B_f²(1/2 + πC) < ‖f‖₂² log(1 + 2πξ)`. -/
theorem exists_gt_height_sharp_escape_of_riemannHypothesis (hRH : RiemannHypothesis)
    {C a B : ℝ} (ha : 0 ≤ a) (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊)
    (T_min : ℝ) :
    ∃ ξ : ℝ, max T_min 0 < ξ ∧ B < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ∧
      B - 1 - (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) <
        (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * ξ) := by
  obtain ⟨ξ, hξgt, hξB, hW | hesc⟩ :=
    exists_gt_height_re_W_neg_or_sharp_escape ha hC0 hC hf hfs hB T_min
  · exfalso
    have hle := riemannHypothesis_iff_primePolynomial_le_archPart.mp hRH a f hf hfs ξ
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re] at hW
    linarith
  · exact ⟨ξ, hξgt, hξB, hesc⟩

/-- **Exponential Lower Bound on Bohr Recurrence Gaps under `RiemannHypothesis`.**
If `L > 0` is any syndetic recurrence gap for `(primePolynomial f ⌊e^{2a}⌋₊ ·).re > B`, then
`RiemannHypothesis` forces `B - 1 - B_f²(1/2 + πC) < ‖f‖₂² log(1 + 2π(e^a + B_f² + L))`. -/
theorem bohr_recurrence_length_exp_lower_bound_of_riemannHypothesis (hRH : RiemannHypothesis)
    {C a B L : ℝ} (ha : 0 ≤ a) (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hdense : ∀ T₀ : ℝ, ∃ ξ ∈ Icc T₀ (T₀ + L), B < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re) :
    B - 1 - (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) <
      (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π *
        (Real.exp a + (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 + L)) := by
  set Bf := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)
  set T₀ := Real.exp a + Bf ^ 2
  obtain ⟨ξ, hξmem, hξB⟩ := hdense T₀
  have hle := riemannHypothesis_iff_primePolynomial_le_archPart.mp hRH a f hf hfs ξ
  have hW : 0 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re]
    linarith
  have hp := post_pole_bound_of_ge ha hξmem.1
  have hT₀_pos : 0 < T₀ := by linarith [Real.exp_pos a, sq_nonneg Bf]
  have hξ0 : 0 ≤ ξ := by linarith [hξmem.1]
  have hgt_ξ : B - 1 - Bf ^ 2 * (1 / 2 + π * C) < (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * ξ) := by
    by_contra hnot
    have hdesert : (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|) ≤
        B - 1 - Bf ^ 2 * (1 / 2 + π * C) := by
      rw [abs_of_nonneg hξ0]
      exact not_lt.mp hnot
    linarith [re_primePolynomial_le_in_post_pole_desert_of_re_W_nonneg ha hC0 hC hf hfs hp
      hdesert hW]
  have hN0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hlog_mono : Real.log (1 + 2 * π * ξ) ≤ Real.log (1 + 2 * π * (T₀ + L)) :=
    Real.log_le_log (by positivity) (by nlinarith [Real.pi_pos, hξmem.2])
  exact lt_of_lt_of_le hgt_ξ (mul_le_mul_of_nonneg_left hlog_mono hN0)

/-- **Non-Vacuous Pure Superexponential Height Escape and Doubly-Exponential Bohr Recurrence Gaps
on `endpointPairProfile a`.** Under `RiemannHypothesis`, there exist `a₁ ≥ 2` and `c₀ > 0` such
that for every `a ≥ a₁`:
1. For every `T_min : ℝ`, there exists `ξ > max T_min 0` with `e^{c₀ e^a} < 1 + 2πξ`;
2. Every Bohr recurrence gap `L > 0` for coherent peaks of `endpointPairProfile a` at level
   `2 c₀ e^a ‖endpointPairProfile a‖₂²` satisfies `e^{c₀ e^a} < 1 + 2π(e^a + 336² + L)`. -/
theorem exists_endpointPair_sharp_escape_and_recurrence_lower_bound (hRH : RiemannHypothesis) :
    ∃ a₁ c₀ : ℝ, 2 ≤ a₁ ∧ 0 < c₀ ∧ ∀ a : ℝ, a₁ ≤ a →
      (∀ T_min : ℝ, ∃ ξ : ℝ, max T_min 0 < ξ ∧ Real.exp (c₀ * Real.exp a) < 1 + 2 * π * ξ) ∧
      (∀ L : ℝ,
        (∀ T₀ : ℝ, ∃ ξ ∈ Icc T₀ (T₀ + L),
          2 * c₀ * Real.exp a * (∫ t, ‖endpointPairProfile a t‖ ^ 2) <
            (primePolynomial (endpointPairProfile a) ⌊Real.exp (2 * a)⌋₊ ξ).re) →
        Real.exp (c₀ * Real.exp a) < 1 + 2 * π * (Real.exp a + 336 ^ 2 + L)) := by
  obtain ⟨C, hC0, hC⟩ := exists_mu_le
  obtain ⟨a₀, κ₀, ha₀2, hκ₀, hsat⟩ := exists_endpointPairProfile_saturation
  set c₀ := κ₀ / 4
  have hc₀ : 0 < c₀ := by positivity
  set K := 1 + (336 : ℝ) ^ 2 * (1 / 2 + π * C)
  have hev := (Real.tendsto_exp_atTop.eventually
    (eventually_gt_atTop (2048 * K / c₀))).and (eventually_ge_atTop a₀)
  obtain ⟨a₁, ha₁_exp, ha₁_ge⟩ := hev.exists
  refine ⟨a₁, c₀, ha₀2.trans ha₁_ge, hc₀, fun a ha => ?_⟩
  have ha_ge_a0 : a₀ ≤ a := ha₁_ge.trans ha
  have ha2 : 2 ≤ a := ha₀2.trans ha_ge_a0
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨hN_lb, hN_ub, hBf_ub⟩ := endpointPairProfile_norm_bounds ha2
  have hN_pos : 0 < ∫ t, ‖endpointPairProfile a t‖ ^ 2 := by linarith
  have hBf0 : 0 ≤ 4 * ((∫ u, ‖endpointPairProfile a u‖) +
      ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖) := by
    have : 0 ≤ (∫ u, ‖endpointPairProfile a u‖) +
        ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖ :=
      add_nonneg (integral_nonneg fun _ => norm_nonneg _)
        (integral_nonneg fun _ => norm_nonneg _)
    positivity
  have hBf_sq : (4 * ((∫ u, ‖endpointPairProfile a u‖) +
      ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖)) ^ 2 ≤ 336 ^ 2 :=
    pow_le_pow_left₀ hBf0 hBf_ub 2
  have hK_le : 1 + (4 * ((∫ u, ‖endpointPairProfile a u‖) +
      ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖)) ^ 2 * (1 / 2 + π * C) ≤ K := by
    have hpos : 0 ≤ 1 / 2 + π * C := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hBf_sq hpos]
  have hK_small : K < c₀ * Real.exp a * (∫ t, ‖endpointPairProfile a t‖ ^ 2) := by
    have hexp_mono : Real.exp a₁ ≤ Real.exp a := Real.exp_le_exp.mpr ha
    have h1 : 2048 * K < c₀ * Real.exp a := by
      have := (div_lt_iff₀ hc₀).mp ha₁_exp
      nlinarith
    nlinarith
  set B := 2 * c₀ * Real.exp a * (∫ t, ‖endpointPairProfile a t‖ ^ 2)
  have hB_lt : B < primeOnlyEnvelope (endpointPairProfile a) ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope (endpointPairProfile a) ⌊Real.exp (2 * a)⌋₊ := by
    have h1 : B < κ₀ * Real.exp a * (∫ t, ‖endpointPairProfile a t‖ ^ 2) := by
      simp only [B, c₀]
      have hexp_pos : 0 < Real.exp a := Real.exp_pos a
      nlinarith
    exact lt_trans h1 (hsat a ha_ge_a0)
  constructor
  · intro T_min
    obtain ⟨ξ, hξgt, _, hesc⟩ := exists_gt_height_sharp_escape_of_riemannHypothesis hRH ha0 hC0
      hC (endpointPairProfile_contDiff a) (tsupport_endpointPairProfile_subset ha2) hB_lt T_min
    have hξ0 : 0 < ξ := lt_of_le_of_lt (le_max_right T_min 0) hξgt
    have hlog_gt : c₀ * Real.exp a < Real.log (1 + 2 * π * ξ) := by
      have : c₀ * Real.exp a * (∫ t, ‖endpointPairProfile a t‖ ^ 2) <
          (∫ t, ‖endpointPairProfile a t‖ ^ 2) * Real.log (1 + 2 * π * ξ) := by
        simp only [B] at hesc
        linarith
      nlinarith
    refine ⟨ξ, hξgt, ?_⟩
    rw [← Real.log_lt_log_iff (Real.exp_pos _) (by positivity), Real.log_exp]
    exact hlog_gt
  · intro L hdense
    have hesc := bohr_recurrence_length_exp_lower_bound_of_riemannHypothesis hRH ha0 hC0 hC
      (endpointPairProfile_contDiff a) (tsupport_endpointPairProfile_subset ha2) hdense
    obtain ⟨ξ₀, hξ₀_mem, _⟩ := hdense (Real.exp a + 336 ^ 2)
    have harg_pos : 0 < 1 + 2 * π * (Real.exp a + 336 ^ 2 + L) := by
      have hTL : 0 < Real.exp a + 336 ^ 2 + L := by linarith [Real.exp_pos a, hξ₀_mem.1, hξ₀_mem.2]
      positivity
    have harg_pos' : 0 < 1 + 2 * π * (Real.exp a +
        (4 * ((∫ u, ‖endpointPairProfile a u‖) +
          ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖)) ^ 2 + L) := by
      obtain ⟨ξ₁, hξ₁_mem, _⟩ := hdense (Real.exp a +
        (4 * ((∫ u, ‖endpointPairProfile a u‖) +
          ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖)) ^ 2)
      have hTL : 0 < Real.exp a +
          (4 * ((∫ u, ‖endpointPairProfile a u‖) +
            ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖)) ^ 2 + L := by
        linarith [Real.exp_pos a, sq_nonneg (4 * ((∫ u, ‖endpointPairProfile a u‖) +
          ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖)), hξ₁_mem.1, hξ₁_mem.2]
      positivity
    have hlog_mono : Real.log (1 + 2 * π * (Real.exp a +
          (4 * ((∫ u, ‖endpointPairProfile a u‖) +
            ∫ u, ‖deriv (deriv (endpointPairProfile a)) u‖)) ^ 2 + L)) ≤
        Real.log (1 + 2 * π * (Real.exp a + 336 ^ 2 + L)) :=
      Real.log_le_log harg_pos' (by nlinarith [Real.pi_pos, hBf_sq])
    have hlog_gt : c₀ * Real.exp a < Real.log (1 + 2 * π * (Real.exp a + 336 ^ 2 + L)) := by
      have h1 : c₀ * Real.exp a * (∫ t, ‖endpointPairProfile a t‖ ^ 2) <
          (∫ t, ‖endpointPairProfile a t‖ ^ 2) *
            Real.log (1 + 2 * π * (Real.exp a + 336 ^ 2 + L)) := by
        have hmul := mul_le_mul_of_nonneg_left hlog_mono hN_pos.le
        simp only [B] at hesc
        linarith
      nlinarith
    rw [← Real.log_lt_log_iff (Real.exp_pos _) harg_pos, Real.log_exp]
    exact hlog_gt

/-! ## §3. Barrier-Free Trans-Horizon Graded Power-Saving Single-Height Positivity -/

/-- Exact lower bound on `Re W_ζ(S_ξ f, S_ξ f)` in terms of `-(primePolynomial f ⌊e^{2a}⌋₊ ξ).re`
with high-height pole decay (no `-2 S(a)` loss). -/
theorem zetaZeroConfig_re_W_heightShift_ge_sub_re_primePolynomial_decay {a : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (Real.log (1 + π * |ξ| / 4) - 10) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) -
      2 * Real.exp a *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 -
      (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤
      (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re]
  linarith [re_archPart_ge_decay ha hf hfs ξ]

/-- **Phase-Selective Single-Height Positivity Law.** At any single height `ξ` where
`(primePolynomial f ⌊e^{2a}⌋₊ ξ).re ≤ M ‖f‖₂²`, we have `Re W_ζ(S_ξ f, S_ξ f) ≥ 0` provided
`12 + M ≤ log(1 + π|ξ|/4)` and both high-height tail terms are bounded by `‖f‖₂²`. -/
theorem zetaZeroConfig_re_W_heightShift_nonneg_of_phase_bound_decay {a M : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) {ξ : ℝ}
    (hprime : (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ M * ∫ t, ‖f t‖ ^ 2)
    (hlog : 12 + M ≤ Real.log (1 + π * |ξ| / 4))
    (htail : (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
      ∫ t, ‖f t‖ ^ 2)
    (hpole : 2 * Real.exp a *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 ≤
      ∫ t, ‖f t‖ ^ 2) :
    0 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  have h := zetaZeroConfig_re_W_heightShift_ge_sub_re_primePolynomial_decay ha hf hfs ξ
  have hN0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Graded Power-Saving Trans-Horizon Single-Height Positivity.**
If at height `ξ` a profile `f` achieves a power-saving prime bound
`(primePolynomial f ⌊e^{2a}⌋₊ ξ).re ≤ c e^{θ a} ‖f‖₂²`, then `Re W_ζ(S_ξ f, S_ξ f) ≥ 0` up to the
trans-horizon aperture `12 + c e^{θ a} ≤ log(1 + π|ξ|/4)` (`X ≍ (log |ξ|)^{2/θ}` for `θ ∈ (0, 1)`),
completely free of the `2 S(a)` barrier that previously capped `a` at `log |ξ|` even when `Π_f ≤ 0`. -/
theorem zetaZeroConfig_re_W_heightShift_nonneg_of_power_saving {a c θ : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) {ξ : ℝ}
    (hprime : (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤
      c * Real.exp (θ * a) * ∫ t, ‖f t‖ ^ 2)
    (hlog : 12 + c * Real.exp (θ * a) ≤ Real.log (1 + π * |ξ| / 4))
    (htail : (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
      ∫ t, ‖f t‖ ^ 2)
    (hpole : 2 * Real.exp a *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 ≤
      ∫ t, ‖f t‖ ^ 2) :
    0 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re :=
  zetaZeroConfig_re_W_heightShift_nonneg_of_phase_bound_decay ha hf hfs hprime hlog htail hpole

/-- **Polynomial-Scale Single-Height Positivity on the Destructive Prime Cone (`Re Π_f ≤ 0`).**
Whenever `(primePolynomial f ⌊e^{2a}⌋₊ ξ).re ≤ 0` and `12 ≤ log(1 + π|ξ|/4)`, single-height
positivity holds all the way to the polynomial pole-decay scale
`2 e^a B_f² ≤ (1 + 2π|ξ|)⁴ ‖f‖₂²` (`X = e^{2a} ≲ |ξ|^8`). -/
theorem zetaZeroConfig_re_W_heightShift_nonneg_of_destructive_cone {a : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) {ξ : ℝ}
    (hprime : (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ 0)
    (hlog : 12 ≤ Real.log (1 + π * |ξ| / 4))
    (htail : (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
      ∫ t, ‖f t‖ ^ 2)
    (hpole : 2 * Real.exp a *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 ≤
      ∫ t, ‖f t‖ ^ 2) :
    0 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re :=
  zetaZeroConfig_re_W_heightShift_nonneg_of_phase_bound_decay (M := 0) ha hf hfs
    (by simpa using hprime) (by linarith) htail hpole

/-! ## §4. Single-Height Power Saving Excludes Isolated Depth-`δ` Off-Line Zeros -/

/-- Exact bridge between `RHTower.modulatedTest` at ordinate `γ₀` and `SquareRootThreshold.heightShift`
at frequency `-γ₀ / (2π)`. -/
theorem modulatedTest_eq_heightShift (γ₀ : ℝ) (s : ℝ → ℝ) :
    modulatedTest γ₀ s = heightShift (-γ₀ / (2 * π)) (fun u => (s u : ℂ)) := by
  funext u
  simp only [modulatedTest, heightShift]
  congr 2
  have h2pi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  push_cast
  field_simp [h2pi]
  ring

/-- **Single-Height Nonnegativity on `sinhTest a δ` Forces Off-Line Companions.**
Strengthens `exists_offLine_companion_of_weil_positive` from global level-`a` Weil positivity to
positivity at the *single* test `heightShift (-ρ₀.im / (2π)) (sinhTest a δ)`. -/
theorem exists_offLine_companion_of_single_height_nonneg (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ a R w : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    (hR : 0 ≤ R) (hw : 0 < w) (hwa : w ≤ a / 4)
    (hsingle : 0 ≤ (Z.W
      (heightShift (-ρ₀.im / (2 * π)) (fun u => ((sinhTest a δ u : ℝ) : ℂ)))
      (heightShift (-ρ₀.im / (2 * π)) (fun u => ((sinhTest a δ u : ℝ) : ℂ)))).re)
    (hbig : 384 * A₀ * Real.log (|ρ₀.im| + 3) *
        (2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (1 + Real.exp a / (1 + R)) <
      2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2) :
    ∃ ρ ∈ Z.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧ |ρ.im - ρ₀.im| ≤ R ∧ ρ.re ≠ 1 / 2 := by
  have ha : 0 < a := by linarith
  by_contra hiso
  simp only [not_exists, not_and, not_not] at hiso
  have hmaster := re_W_modulatedTest_le_of_isolated Z hA₀ hloc hρ₀ hδ hre ha.le hR hiso
    (sinhTest_contDiff a δ) (sinhTest_odd a δ) (sinhTest_supp ha.le)
  rw [modulatedTest_eq_heightShift] at hmaster
  have hP := sinhTest_energy_ge (a := a) hδ hw hwa
  have hN := testNorm_sinhTest_le ha.le hδ.le
  have hN0 := testNorm_nonneg (sinhTest a δ)
  have hm : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  have hPl0 : 0 ≤ w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2 := by positivity
  have hL : 0 ≤ 384 * A₀ * Real.log (|ρ₀.im| + 3) := by
    have := one_le_log_abs_add_three ρ₀.im
    positivity
  have hK : 0 ≤ 1 + Real.exp a / (1 + R) := by positivity
  have hP2 := pow_le_pow_left₀ hPl0 hP 2
  have hN2 := pow_le_pow_left₀ hN0 hN 2
  have h1 : -2 * (Z.mult ρ₀ : ℝ) * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 ≤
      -2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (∫ u, sinhTest a δ u * Real.sinh (δ * u))]
  have h2 : 384 * A₀ * Real.log (|ρ₀.im| + 3) * testNorm (sinhTest a δ) ^ 2 *
        (1 + Real.exp a / (1 + R)) ≤
      384 * A₀ * Real.log (|ρ₀.im| + 3) *
        (2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (1 + Real.exp a / (1 + R)) := by
    gcongr
  linarith

/-- **Single-Height Power Saving Forces Off-Line Companions for `ζ`.**
There is an unconditional Riemann–von Mangoldt constant `A₀ ≥ 1` such that if `ρ₀ = ½ + δ + iγ₀`
is an off-line zero of `ζ` and at the *single* height `ξ₀ = -γ₀ / (2π)` the profile `sinhTest a δ`
satisfies a `θ`-power-saving prime bound within the trans-horizon aperture
`12 + c e^{θ a} ≤ log(1 + |γ₀|/8)`, then `ρ₀` cannot be isolated at radius `R` once the depth-`δ`
signal exceeds the local zero-density background (`a ≳ (1/(2δ)) log log |γ₀|`, compatible with
`12 + c e^{θ a} ≤ log(1 + |γ₀|/8)` whenever `θ < 2δ`). -/
theorem zeta_single_height_power_saving_forces_offLine_companion :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier →
      ∀ {δ a R w c θ : ℝ}, 0 < δ → ρ₀.re = 1 / 2 + δ →
        0 ≤ R → 0 < w → w ≤ a / 4 →
        (primePolynomial (fun u => ((sinhTest a δ u : ℝ) : ℂ)) ⌊Real.exp (2 * a)⌋₊
            (-ρ₀.im / (2 * π))).re ≤
          c * Real.exp (θ * a) * ∫ t, ‖((sinhTest a δ t : ℝ) : ℂ)‖ ^ 2 →
        12 + c * Real.exp (θ * a) ≤ Real.log (1 + |ρ₀.im| / 8) →
        (4 * testNorm (sinhTest a δ)) ^ 2 / (8 * (1 + |ρ₀.im| / 2)) ≤
          ∫ t, ‖((sinhTest a δ t : ℝ) : ℂ)‖ ^ 2 →
        2 * Real.exp a * (4 * testNorm (sinhTest a δ)) ^ 2 / (1 + |ρ₀.im|) ^ 4 ≤
          ∫ t, ‖((sinhTest a δ t : ℝ) : ℂ)‖ ^ 2 →
        384 * A₀ * Real.log (|ρ₀.im| + 3) *
            (2 * a * Real.cosh (δ * a) *
              (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
            (1 + Real.exp a / (1 + R)) <
          2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 →
        ∃ ρ ∈ zetaZeroConfig.carrier,
          ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧ |ρ.im - ρ₀.im| ≤ R ∧ ρ.re ≠ 1 / 2 := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, fun {ρ₀} hρ₀ {δ a R w c θ} hδ hre hR hw hwa hprime hlog htail hpole hbig => ?_⟩
  have ha : 0 ≤ a := by linarith
  set ξ₀ : ℝ := -ρ₀.im / (2 * π)
  have habs_ξ₀ : |ξ₀| = |ρ₀.im| / (2 * π) := by
    simp only [ξ₀, abs_div, abs_neg, abs_of_pos Real.two_pi_pos]
  have h1 : π * |ξ₀| / 4 = |ρ₀.im| / 8 := by
    rw [habs_ξ₀]
    field_simp [Real.pi_pos.ne']
    ring
  have h2 : π * |ξ₀| = |ρ₀.im| / 2 := by
    rw [habs_ξ₀]
    field_simp [Real.pi_pos.ne']
  have h3 : 2 * π * |ξ₀| = |ρ₀.im| := by
    rw [habs_ξ₀]
    field_simp [Real.two_pi_pos.ne']
  have hnonneg := zetaZeroConfig_re_W_heightShift_nonneg_of_power_saving ha
    (sinhTest_ofReal_contDiff a δ) (sinhTest_tsupport_subset ha) hprime
    (by rwa [h1]) (by rwa [h2]) (by rwa [h3])
  exact exists_offLine_companion_of_single_height_nonneg zetaZeroConfig hA₀ hloc hρ₀ hδ hre
    hR hw hwa hnonneg hbig

/-! ## §5. Syndetic Kronecker Troughs, Barrier-Free Bad-Height Measure, and Power-Saving Measure -/

/-- **Syndetic High-Height Kronecker Troughs Free of `-2 S(a)`.**
For every `B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ - primePowerTailEnvelope f ⌊e^{2a}⌋₊`, there exists
`L > 0` such that *every* height interval `[T₀, T₀ + L]` contains `ξ` at which `(primePolynomial f ⌊e^{2a}⌋₊ ξ).re < -B`
and `Re W_ζ(S_ξ f, S_ξ f)` exceeds `(log(1 + π|ξ|/4) - 10) ‖f‖₂² + B` minus high-height tails. -/
theorem exists_relDense_kronecker_trough_re_W_ge_decay {a B : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊) :
    ∃ L : ℝ, 0 < L ∧ ∀ T₀ : ℝ, ∃ ξ ∈ Icc T₀ (T₀ + L),
      (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re < -B ∧
      (Real.log (1 + π * |ξ| / 4) - 10) * (∫ t, ‖f t‖ ^ 2) + B -
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) -
        2 * Real.exp a *
          (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ|) ^ 4 <
        (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  obtain ⟨L, hL, hdense⟩ := exists_relDense_re_primePolynomial_gt_and_lt f ⌊Real.exp (2 * a)⌋₊ hB
  refine ⟨L, hL, fun T₀ => ?_⟩
  obtain ⟨-, ⟨ξ, hξmem, hξlt⟩⟩ := hdense T₀
  refine ⟨ξ, hξmem, hξlt, ?_⟩
  have h := zetaZeroConfig_re_W_heightShift_ge_sub_re_primePolynomial_decay ha hf hfs ξ
  linarith

/-- **Barrier-Free Bad-Height Measure Bound Across Polynomial Sub-Threshold Scales.**
Upgrades `lintegral_bad_heights_le_of_height` by replacing `-2 S(a)` in `A₀` with
`-2 e^a B_f² / (1 + 2πΞ)⁴`, making `A₀ > 0` (and hence the `O((log X / log Ξ)²)` bad-height
proportion) non-vacuous throughout `(log Ξ)² ≤ X ≤ Ξ^{1-ε}`. -/
theorem lintegral_bad_heights_le_of_height_decay {a r Ξ : ℝ} (ha : 0 ≤ a) {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) (hX : 2 * r * Real.exp (2 * a) ≤ 1) (ξ₀ : ℝ) (hΞ : 0 ≤ Ξ)
    (hA₀ : 0 < (Real.log (1 + π * Ξ / 4) - 10) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * Ξ)) -
      2 * Real.exp a *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * Ξ) ^ 4) :
    ∫⁻ ξ, ({ξ | Ξ ≤ |ξ + ξ₀|} ∩ {ξ | (zetaZeroConfig.W (heightShift (ξ + ξ₀) f)
        (heightShift (ξ + ξ₀) f)).re < 0}).indicator
        (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
      ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ /
        ((Real.log (1 + π * Ξ / 4) - 10) * (∫ t, ‖f t‖ ^ 2) -
          (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * Ξ)) -
          2 * Real.exp a *
            (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * Ξ) ^ 4) ^ 2) := by
  refine lintegral_bad_heights_le ha hf hfs hη hηs hX ξ₀ hA₀ fun ξ hξ => ?_
  simp only [Set.mem_setOf_eq] at hξ
  refine le_trans ?_ (re_archPart_ge_decay ha hf hfs (ξ + ξ₀))
  have hN0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hlog : Real.log (1 + π * Ξ / 4) ≤ Real.log (1 + π * |ξ + ξ₀| / 4) :=
    Real.log_le_log (by positivity) (by gcongr)
  have htail : (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ + ξ₀|)) ≤
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * Ξ)) := by
    gcongr
  have hpole : 2 * Real.exp a *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * |ξ + ξ₀|) ^ 4 ≤
      2 * Real.exp a *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + 2 * π * Ξ) ^ 4 := by
    gcongr
  have hmul := mul_le_mul_of_nonneg_right (sub_le_sub_right hlog 10) hN0
  linarith

/-- Windowed Chebyshev bound for large prime-polynomial excursions below the square-root threshold:
for `2r e^{2a} ≤ 1` and `M > 0`, the heights `ξ + ξ₀` with `|(primePolynomial f ⌊e^{2a}⌋₊ (ξ + ξ₀)).re| ≥ M`
carry window weight at most `‖η‖₂² V_f / M²`. -/
theorem lintegral_abs_re_primePolynomial_ge_le_of_separated {a r M : ℝ} (ha : 0 ≤ a)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r)
    (hX : 2 * r * Real.exp (2 * a) ≤ 1) (ξ₀ : ℝ) (hM : 0 < M) :
    ∫⁻ ξ, {ξ | M ≤ |(primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re|}.indicator
        (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
      ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ / M ^ 2) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set N := ⌊Real.exp (2 * a)⌋₊
  set Q : ℝ → ℂ := fun ξ => primePolynomial f N (ξ + ξ₀) with hQ
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP
  have hPi : Integrable P := by
    refine (integrable_pairTransform hη hηc).re.congr (Eventually.of_forall fun ξ => ?_)
    simp only [pairTransform_ofReal hη hηc ξ, RCLike.re_to_complex, Complex.ofReal_re, hP]
  have hPc : Continuous P := by
    have h := Complex.continuous_re.comp ((differentiable_pairTransform hη hηc).continuous.comp
      Complex.continuous_ofReal)
    refine h.congr fun ξ => ?_
    simp only [Function.comp_apply, pairTransform_ofReal hη hηc ξ, Complex.ofReal_re, hP]
  have hQc : Continuous Q := by
    simp only [hQ, primePolynomial]
    exact (continuous_expSum _ _ _).comp (continuous_id.add continuous_const)
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖
  have hQb : ∀ ξ, ‖Q ξ‖ ≤ C := fun ξ => norm_expSum_le _ _ _ _
  set G : ℝ → ℝ := fun ξ => P ξ * ‖Q ξ‖ ^ 2 / M ^ 2 with hG
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun _ => by positivity
  have hGi : Integrable G := by
    refine (hPi.mul_const (C ^ 2 / M ^ 2)).mono'
      ((hPc.mul (hQc.norm.pow 2)).div_const _).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (hG0 ξ), mul_div_assoc]
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    have hQ2 : ‖Q ξ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hQb ξ) 2
    gcongr
  have hGint : ∫ ξ, G ξ = (∫ t, ‖η t‖ ^ 2) * primeVariance f N / M ^ 2 := by
    have hvar := integral_windowed_sq_deviation_eq ha hf hfs hη hηs hX ξ₀
    have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
        archPart f (ξ + ξ₀)‖ = ‖Q ξ‖ := fun ξ => by
      rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
    simp_rw [hdev] at hvar
    simp only [hG, integral_div]
    rw [hvar]
  rw [← hGint, ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hG0)]
  refine lintegral_mono fun ξ => ?_
  by_cases hξ : ξ ∈ {ξ | M ≤ |(Q ξ).re|}
  · rw [Set.indicator_of_mem hξ]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Set.mem_setOf_eq] at hξ
    have hQn : M ≤ ‖Q ξ‖ := hξ.trans (Complex.abs_re_le_norm _)
    have hratio : 1 ≤ ‖Q ξ‖ ^ 2 / M ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hM.le hQn 2
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    calc ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 = P ξ * 1 := by rw [mul_one]
      _ ≤ P ξ * (‖Q ξ‖ ^ 2 / M ^ 2) := mul_le_mul_of_nonneg_left hratio hP0
      _ = G ξ := by rw [hG]; ring
  · rw [Set.indicator_of_notMem hξ]
    exact bot_le

/-- **Universal `O(a² e^{-2θ a})` Windowed Measure of Power-Saving Violation Heights.**
There exists an absolute constant `C ≥ 0` such that for *every* `C²` profile `f` supported in
`[-a, a]` (`a ≥ 0`), *every* sub-threshold window `η` (`2r e^{2a} ≤ 1`), *every* centre `ξ₀`,
`c > 0`, and `θ ∈ ℝ`, the heights violating `|(primePolynomial f ⌊e^{2a}⌋₊ (ξ + ξ₀)).re| ≤ c e^{θ a} ‖f‖₂²`
carry window weight at most `‖η‖₂² · 2(2a(2a + C)) / (c² e^{2θ a})`, completely independent of `f`! -/
theorem exists_lintegral_power_saving_violation_heights_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {a r c θ : ℝ}, 0 ≤ a → 0 < c →
      ∀ {f η : ℝ → ℂ}, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        ContDiff ℝ 2 η → tsupport η ⊆ Icc (-r) r → 2 * r * Real.exp (2 * a) ≤ 1 →
      ∀ ξ₀ : ℝ,
        ∫⁻ ξ, {ξ | c * Real.exp (θ * a) * (∫ t, ‖f t‖ ^ 2) <
            |(primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re|}.indicator
            (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
          ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) * (2 * (2 * a * (2 * a + C))) /
            (c ^ 2 * Real.exp (2 * θ * a))) := by
  obtain ⟨C, hC0, hV⟩ := exists_primeVariance_le
  refine ⟨C, hC0, fun {a r c θ} ha hc {f η} hf hfs hη hηs hX ξ₀ => ?_⟩
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  set Nf := ∫ t, ‖f t‖ ^ 2
  have hNf0 : 0 ≤ Nf := integral_nonneg fun _ => sq_nonneg _
  rcases hNf0.lt_or_eq with hNf_pos | hNf_zero
  · set M := c * Real.exp (θ * a) * Nf
    have hM : 0 < M := by positivity
    have hsub : ∫⁻ ξ, {ξ | M < |(primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re|}.indicator
          (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
        ∫⁻ ξ, {ξ | M ≤ |(primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re|}.indicator
          (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ :=
      lintegral_mono fun ξ =>
        Set.indicator_le_indicator_of_subset (fun _ h => h.le) (fun _ => zero_le _) ξ
    refine hsub.trans ((lintegral_abs_re_primePolynomial_ge_le_of_separated ha hf hfs hη hηs hX
      ξ₀ hM).trans (ENNReal.ofReal_le_ofReal ?_))
    have hNη0 : 0 ≤ ∫ t, ‖η t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hvar := hV a ha f hf.continuous hfc
    have hM2 : M ^ 2 = c ^ 2 * Real.exp (2 * θ * a) * Nf ^ 2 := by
      simp only [M]
      have hexp2 : (Real.exp (θ * a)) ^ 2 = Real.exp (2 * θ * a) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      calc (c * Real.exp (θ * a) * Nf) ^ 2
          = c ^ 2 * (Real.exp (θ * a)) ^ 2 * Nf ^ 2 := by ring
        _ = c ^ 2 * Real.exp (2 * θ * a) * Nf ^ 2 := by rw [hexp2]
    rw [hM2]
    have hnum : (∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ ≤
        (∫ t, ‖η t‖ ^ 2) * (2 * Nf ^ 2 * (2 * a * (2 * a + C))) :=
      mul_le_mul_of_nonneg_left hvar hNη0
    have hNf2_ne : Nf ^ 2 ≠ 0 := pow_ne_zero 2 hNf_pos.ne'
    calc (∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ /
          (c ^ 2 * Real.exp (2 * θ * a) * Nf ^ 2)
        ≤ (∫ t, ‖η t‖ ^ 2) * (2 * Nf ^ 2 * (2 * a * (2 * a + C))) /
          (c ^ 2 * Real.exp (2 * θ * a) * Nf ^ 2) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = ((∫ t, ‖η t‖ ^ 2) * (2 * (2 * a * (2 * a + C))) * Nf ^ 2) /
          ((c ^ 2 * Real.exp (2 * θ * a)) * Nf ^ 2) := by ring
      _ = (∫ t, ‖η t‖ ^ 2) * (2 * (2 * a * (2 * a + C))) /
          (c ^ 2 * Real.exp (2 * θ * a)) := mul_div_mul_right _ _ hNf2_ne
  · have hwt0 : ∀ v : ℝ, EF.weilTest f f v = 0 := fun v => by
      have hb := norm_weilTest_self_le hf.continuous hfc v
      rw [← hNf_zero] at hb
      exact norm_le_zero_iff.mp hb
    have hP0 : ∀ ξ : ℝ, primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀) = 0 := fun ξ => by
      unfold primePolynomial expSum
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [primeCoeff, hwt0]
    have hempty : {ξ : ℝ | c * Real.exp (θ * a) * Nf <
        |(primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re|} = ∅ := by
      ext ξ
      simp [← hNf_zero, hP0 ξ]
    rw [hempty]
    simp

end GaloisForLFunctions.ArithmeticPositivityTheory
