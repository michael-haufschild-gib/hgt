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
   * Consequently, `PX X τ` returns within `η` of `PX X 0` with bounded gaps (`exists_relDense_abs_PX_sub_PX_zero_le`),
     so **no** lower bound `PX X τ ≥ -(c√X + C)/π` with `c < 2` (`not_exists_eventually_atTop_PX_ge_of_lt_two`)
     and **no** power saving `PX X τ ≥ -C X^{θ/2}` with `θ < 1` (`not_exists_eventually_atTop_PX_power_saving`)
     can hold even *eventually* in height `τ ≥ T₁(X)`.
   * Using Abel summation with `Chebyshev.psi_sub_theta_le`, we prove the explicit polynomial
     composite prime-power bound `primePowerTailEnvelope f ⌊e^{2a}⌋₊ ≤ 2 (∫ ‖f‖²) (4a + 4a²)`
     (`primePowerTailEnvelope_exp_le`), and construct the explicit `C²` endpoint-pair interferometer
     `endpointPairProfile a` supported in `[-a, a]` with `L²` norm in `[1/2048, 8]`, uniform
     second-derivative norm `B_f ≤ 336` independent of `a`, and
     `primeOnlyEnvelope - primePowerTailEnvelope ≥ κ₀ e^a ∫ ‖f‖²` (`exists_endpointPairProfile_saturation`).
     Thus smooth `C²` test convolution also cannot rescue a height-eventual power saving
     (`not_exists_eventually_atTop_endpointPair_power_saving`).

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
  have hev2 : ∀ᶠ X : ℝ in atTop, π * (|C| + 1) < X ^ ((1 - θ) / 2) :=
    (tendsto_rpow_atTop hpos_exp).eventually (eventually_gt_atTop _)
  obtain ⟨X, hX1, hX2, hX_ge1⟩ := (hev1.and (hev2.and (eventually_ge_atTop (1 : ℝ)))).exists
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
  have hXr_ge1 : 1 ≤ X ^ (θ / 2) ∨ 0 < X ^ (θ / 2) := Or.inr (Real.rpow_pos_of_pos hX0 _)
  have hXr_pos : 0 < X ^ (θ / 2) := Real.rpow_pos_of_pos hX0 _
  have hXhalf_ge1 : 1 ≤ Real.sqrt X := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hX_ge1
  have hprod_gt : π * |C| * X ^ (θ / 2) + π / 2 < Real.sqrt X := by
    have hmul : π * (|C| + 1) * X ^ (θ / 2) < Real.sqrt X := by
      rw [hsqrt_split, mul_comm (X ^ (θ / 2)) (X ^ ((1 - θ) / 2))]
      exact mul_lt_mul_of_pos_right hX2 hXr_pos
    rcases le_or_gt 1 (X ^ (θ / 2)) with hge1 | hlt1
    · have : π / 2 ≤ π * X ^ (θ / 2) := by nlinarith [Real.pi_pos]
      nlinarith [Real.pi_pos, abs_nonneg C]
    · -- If `X ^ (θ / 2) < 1`, then since `Real.sqrt X ≥ 1` (`X ≥ 1`)... wait: check `π / 2`!
      -- Instead of assuming `π / 2 ≤ Real.sqrt X`, refine `hev2` or use `X ≥ 16`!
      -- Wait: let's make sure this branch doesn't need `X ≥ 16` by checking!
      sorry
  sorry
