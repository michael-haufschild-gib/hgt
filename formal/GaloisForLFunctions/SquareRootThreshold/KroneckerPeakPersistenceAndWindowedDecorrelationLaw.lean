import GaloisForLFunctions.SquareRootThreshold.KroneckerBohrPrimePhaseRealizationAndExponentialHeightEscape
import GaloisForLFunctions.SquareRootThreshold.WindowedOffDiagonalBeyondThreshold

/-!
# Kronecker Peak Persistence and the Windowed Decorrelation Law

This module connects three mechanisms across the Lean corpus:
1. **Kronecker–Bohr Prime-Phase Realization and Exponential Height Escape**
   (`SquareRootThreshold.KroneckerBohrPrimePhaseRealizationAndExponentialHeightEscape`), derived
   from `HTGeometry.PrimeTorusKroneckerDensity`;
2. **Global Lipschitz Phase-Stability of Trigonometric Sums** (`norm_expSum_sub_le`), controlling
   how fast `expSum` and `primePolynomial` can vary across height intervals; and
3. **Windowed Mean-Square Variance Laws Below and Beyond the Square-Root Threshold**
   (`SquareRootThreshold.ZetaLocalizedFormWindowedVarianceLaw` and
   `SquareRootThreshold.WindowedOffDiagonalBeyondThreshold`).

## Main results

1. **Global Lipschitz Phase-Stability and Deterministic Peak Persistence (§1–§2):**
   * `norm_expSum_sub_le` and `abs_re_expSum_sub_le`: global Lipschitz bounds for `expSum s c ν`
     with frequency-weighted `ℓ¹` constant `2π ∑_{j ∈ s} |ν_j| ‖c_j‖`.
   * `norm_primePolynomial_sub_le` and `abs_re_primePolynomial_sub_le`: global Lipschitz bounds for
     `primePolynomial f N` with constant `2π primeLipschitzEnvelope f N`.
   * `exists_interval_gt_and_lt_re_primePolynomial`: upgrades single-height Kronecker alignment to
     full intervals `Icc (-δ) δ` of explicit positive radius
     `δ = primePersistenceRadius f N (B - B₁) > 0` on which `Re Π_f(N, ξ + ξ₊) > B₁` and
     `Re Π_f(N, ξ + ξ₋) < -B₁`.
   * `exists_interval_re_W_neg_or_height_escape` and
     `exists_interval_height_escape_of_riemannHypothesis`: upgrades the sub-horizon negativity vs.
     exponential height-escape dichotomy (and its `RiemannHypothesis` specialization) from single
     heights to closed intervals of positive length `2δ > 0`.

2. **Windowed Chebyshev Rarity and Mean-Square Decorrelation (§3):**
   * `integral_normSq_paperFT_neg_two_pi_eq`: Plancherel identity
     `∫ ξ, ‖h_η(-2πξ)‖² dξ = ∫ t, ‖η t‖² dt` for the Fejér-type height weight.
   * `lintegral_re_primePolynomial_ge_le_of_separated` and
     `lintegral_re_primePolynomial_ge_le_beyond_threshold`: windowed Chebyshev superlevel bounds for
     `Re Π_f(⌊e^{2a}⌋₊, ξ + ξ₀) ≥ β` below (`2r e^{2a} ≤ 1`) and beyond (`0 ≤ r ≤ log 2`) the
     square-root threshold.
   * `lintegral_bad_heights_le_beyond_threshold`: extends the Chebyshev measure bound for negative
     localized Weil forms `Re W_ζ(S_{ξ+ξ₀} f, S_{ξ+ξ₀} f) < 0` beyond the square-root threshold.
   * `exists_norm_primePolynomial_lt_of_primeVariance_lt`: proves that whenever `V_f(⌊e^{2a}⌋₊) < β²`,
     coherent alignment cannot be sustained across a threshold window, forcing the existence of a
     decorrelated height `ξ` with `‖Π_f(⌊e^{2a}⌋₊, ξ + ξ₀)‖ < β`.

3. **The Envelope–Variance–Lipschitz Uncertainty Inequality & Joint Peak Decorrelation (§4):**
   * `setIntegral_persistence_mul_sq_le_primeVariance` and
     `setIntegral_persistence_mul_sq_le_beyond_threshold`: universal uncertainty inequalities
     bounding the local window energy `B₁² ∫_{[-δ, δ]} ‖h_η(-2πξ)‖² dξ` on the deterministic
     Kronecker persistence interval by `(∫ ‖η‖²) V_f(⌊e^{2a}⌋₊)` below the threshold and by
     `(∫ ‖η‖²)(1 + e^{2a}(e^{2r} - e^{-2r})) V_f(⌊e^{2a}⌋₊)` beyond the threshold.
   * `exists_kronecker_peak_persistence_and_windowed_decorrelation`: joint existence of a Kronecker
     peak center `ξ₀` exhibiting both deterministic persistence on `[-δ, δ]` and `O(V_f / β²)`
     windowed Chebyshev rarity in the surrounding height window.
-/

open MeasureTheory Complex Set Filter Topology Finset
open scoped Real ComplexConjugate BigOperators

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular GaloisForLFunctions

/-! ## §1. Global Lipschitz Phase-Stability of `expSum` and `primePolynomial` -/

/-- `‖e^{iθ} - 1‖ ≤ |θ|` for real `θ`. -/
theorem norm_cexp_I_mul_sub_one_le (θ : ℝ) :
    ‖cexp (I * (θ : ℂ)) - 1‖ ≤ |θ| := by
  have h := @Real.norm_exp_I_mul_ofReal_sub_one_le θ
  rwa [Real.norm_eq_abs] at h

/-- `‖e^{2πiξν} - e^{2πiξ₀ν}‖ ≤ 2π |ν| |ξ - ξ₀|`. -/
theorem norm_cexp_two_pi_I_mul_sub_le (ν ξ ξ₀ : ℝ) :
    ‖cexp (2 * π * I * ξ * ν) - cexp (2 * π * I * ξ₀ * ν)‖ ≤
      2 * π * |ν| * |ξ - ξ₀| := by
  have hfac : cexp (2 * π * I * ξ * ν) - cexp (2 * π * I * ξ₀ * ν) =
      cexp (2 * π * I * ξ₀ * ν) *
        (cexp (I * ((2 * π * ν * (ξ - ξ₀) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfac, norm_mul, norm_cexp_two_pi_I_mul, one_mul]
  have h1 := norm_cexp_I_mul_sub_one_le (2 * π * ν * (ξ - ξ₀))
  have habs : |2 * π * ν * (ξ - ξ₀)| = 2 * π * |ν| * |ξ - ξ₀| := by
    rw [abs_mul, abs_mul, abs_of_pos Real.two_pi_pos]
  rwa [habs] at h1

/-- Global Lipschitz bound for any finite exponential sum `expSum s c ν`:
`‖expSum s c ν ξ - expSum s c ν ξ₀‖ ≤ 2π (∑_{j ∈ s} |ν_j| ‖c_j‖) |ξ - ξ₀|`. -/
theorem norm_expSum_sub_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (ξ ξ₀ : ℝ) :
    ‖expSum s c ν ξ - expSum s c ν ξ₀‖ ≤
      2 * π * (∑ j ∈ s, |ν j| * ‖c j‖) * |ξ - ξ₀| := by
  unfold expSum
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, norm_mul]
  have h := norm_cexp_two_pi_I_mul_sub_le (ν j) ξ ξ₀
  calc ‖c j‖ * ‖cexp (2 * π * I * ξ * ν j) - cexp (2 * π * I * ξ₀ * ν j)‖
      ≤ ‖c j‖ * (2 * π * |ν j| * |ξ - ξ₀|) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = 2 * π * (|ν j| * ‖c j‖) * |ξ - ξ₀| := by ring

/-- Global Lipschitz bound for the real part of `expSum s c ν`. -/
theorem abs_re_expSum_sub_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (ξ ξ₀ : ℝ) :
    |(expSum s c ν ξ).re - (expSum s c ν ξ₀).re| ≤
      2 * π * (∑ j ∈ s, |ν j| * ‖c j‖) * |ξ - ξ₀| := by
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (norm_expSum_sub_le s c ν ξ ξ₀)

/-- The frequency-weighted `ℓ¹` Lipschitz envelope of `primePolynomial f N`:
`L_f(N) = ∑_{j ∈ [2, N] × Bool} |primeFreq j| ‖primeCoeff f j‖`. -/
def primeLipschitzEnvelope (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), |primeFreq j| * ‖primeCoeff f j‖

theorem primeLipschitzEnvelope_nonneg (f : ℝ → ℂ) (N : ℕ) :
    0 ≤ primeLipschitzEnvelope f N :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)

/-- Explicit expansion of `primeLipschitzEnvelope f N` over `n ∈ [2, N]`. -/
theorem primeLipschitzEnvelope_eq_sum (f : ℝ → ℂ) (N : ℕ) :
    primeLipschitzEnvelope f N =
      ∑ n ∈ Finset.Icc 2 N,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * Real.log n *
          (‖EF.weilTest f f (Real.log n)‖ + ‖EF.weilTest f f (-Real.log n)‖) := by
  unfold primeLipschitzEnvelope
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hvm : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n := by positivity
  rw [Fintype.sum_bool]
  simp only [primeFreq, primeCoeff, ↓reduceIte, Bool.false_eq_true, abs_neg,
    abs_of_nonneg hlog, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hvm]
  ring

/-- Global Lipschitz bound for `primePolynomial f N`. -/
theorem norm_primePolynomial_sub_le (f : ℝ → ℂ) (N : ℕ) (ξ ξ₀ : ℝ) :
    ‖primePolynomial f N ξ - primePolynomial f N ξ₀‖ ≤
      2 * π * primeLipschitzEnvelope f N * |ξ - ξ₀| :=
  norm_expSum_sub_le _ _ _ ξ ξ₀

/-- Global Lipschitz bound for `(primePolynomial f N ξ).re`. -/
theorem abs_re_primePolynomial_sub_le (f : ℝ → ℂ) (N : ℕ) (ξ ξ₀ : ℝ) :
    |(primePolynomial f N ξ).re - (primePolynomial f N ξ₀).re| ≤
      2 * π * primeLipschitzEnvelope f N * |ξ - ξ₀| :=
  abs_re_expSum_sub_le _ _ _ ξ ξ₀

/-- Deterministic persistence of a positive peak `(primePolynomial f N ξ₀).re > B`. -/
theorem re_primePolynomial_gt_of_abs_sub_le {f : ℝ → ℂ} {N : ℕ} {B B₁ ξ ξ₀ : ℝ}
    (hξ₀ : B < (primePolynomial f N ξ₀).re)
    (hstep : 2 * π * primeLipschitzEnvelope f N * |ξ - ξ₀| ≤ B - B₁) :
    B₁ < (primePolynomial f N ξ).re := by
  have hlip := (abs_le.mp (abs_re_primePolynomial_sub_le f N ξ ξ₀)).1
  linarith

/-- Deterministic persistence of a negative trough `(primePolynomial f N ξ₀).re < -B`. -/
theorem re_primePolynomial_lt_of_abs_sub_le {f : ℝ → ℂ} {N : ℕ} {B B₁ ξ ξ₀ : ℝ}
    (hξ₀ : (primePolynomial f N ξ₀).re < -B)
    (hstep : 2 * π * primeLipschitzEnvelope f N * |ξ - ξ₀| ≤ B - B₁) :
    (primePolynomial f N ξ).re < -B₁ := by
  have hlip := (abs_le.mp (abs_re_primePolynomial_sub_le f N ξ ξ₀)).2
  linarith

/-! ## §2. Deterministic Persistence Intervals & Interval Height Escape -/

/-- The explicit deterministic persistence radius
`δ_f(N, Δ) = Δ / (2π (primeLipschitzEnvelope f N + 1))`. -/
def primePersistenceRadius (f : ℝ → ℂ) (N : ℕ) (Δ : ℝ) : ℝ :=
  Δ / (2 * π * (primeLipschitzEnvelope f N + 1))

theorem primePersistenceRadius_pos (f : ℝ → ℂ) (N : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
    0 < primePersistenceRadius f N Δ := by
  unfold primePersistenceRadius
  have hL : 0 ≤ primeLipschitzEnvelope f N := primeLipschitzEnvelope_nonneg f N
  positivity

theorem primePersistenceRadius_nonneg (f : ℝ → ℂ) (N : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    0 ≤ primePersistenceRadius f N Δ := by
  unfold primePersistenceRadius
  have hL : 0 ≤ primeLipschitzEnvelope f N := primeLipschitzEnvelope_nonneg f N
  positivity

theorem two_pi_mul_primeLipschitzEnvelope_mul_le (f : ℝ → ℂ) (N : ℕ) {Δ d : ℝ}
    (_hΔ : 0 ≤ Δ) (hd : |d| ≤ primePersistenceRadius f N Δ) :
    2 * π * primeLipschitzEnvelope f N * |d| ≤ Δ := by
  have hL : 0 ≤ primeLipschitzEnvelope f N := primeLipschitzEnvelope_nonneg f N
  have hL1 : 0 < 2 * π * (primeLipschitzEnvelope f N + 1) := by positivity
  calc 2 * π * primeLipschitzEnvelope f N * |d|
      ≤ 2 * π * (primeLipschitzEnvelope f N + 1) * |d| := by
        nlinarith [abs_nonneg d, Real.two_pi_pos]
    _ ≤ 2 * π * (primeLipschitzEnvelope f N + 1) * primePersistenceRadius f N Δ :=
        mul_le_mul_of_nonneg_left hd hL1.le
    _ = Δ := by
        unfold primePersistenceRadius
        exact mul_div_cancel₀ Δ hL1.ne'

/-- **Kronecker peak and trough persistence intervals.** For every
`B₁ < B < primeOnlyEnvelope f N - primePowerTailEnvelope f N`, there exist centers `ξ₊, ξ₋ ∈ ℝ`
such that `(primePolynomial f N (ξ + ξ₊)).re > B₁` and `(primePolynomial f N (ξ + ξ₋)).re < -B₁`
for every `ξ ∈ Icc (-δ) δ` with `δ = primePersistenceRadius f N (B - B₁) > 0`. -/
theorem exists_interval_gt_and_lt_re_primePolynomial (f : ℝ → ℂ) (N : ℕ) {B₁ B : ℝ}
    (hB₁ : B₁ < B) (hB : B < primeOnlyEnvelope f N - primePowerTailEnvelope f N) :
    (∃ ξ₀ : ℝ, B < (primePolynomial f N ξ₀).re ∧
      ∀ ξ ∈ Icc (-primePersistenceRadius f N (B - B₁))
          (primePersistenceRadius f N (B - B₁)),
        B₁ < (primePolynomial f N (ξ + ξ₀)).re) ∧
    (∃ ξ₀ : ℝ, (primePolynomial f N ξ₀).re < -B ∧
      ∀ ξ ∈ Icc (-primePersistenceRadius f N (B - B₁))
          (primePersistenceRadius f N (B - B₁)),
        (primePolynomial f N (ξ + ξ₀)).re < -B₁) := by
  have hΔ : 0 ≤ B - B₁ := sub_nonneg.mpr hB₁.le
  obtain ⟨⟨ξ₁, hξ₁⟩, ⟨ξ₂, hξ₂⟩⟩ :=
    exists_gt_and_lt_re_primePolynomial_of_lt_primeSubCompEnvelope f N hB
  refine ⟨⟨ξ₁, hξ₁, fun ξ hξ => ?_⟩, ⟨ξ₂, hξ₂, fun ξ hξ => ?_⟩⟩
  · refine re_primePolynomial_gt_of_abs_sub_le hξ₁ ?_
    rw [add_sub_cancel_right]
    exact two_pi_mul_primeLipschitzEnvelope_mul_le f N hΔ (abs_le.mpr hξ)
  · refine re_primePolynomial_lt_of_abs_sub_le hξ₂ ?_
    rw [add_sub_cancel_right]
    exact two_pi_mul_primeLipschitzEnvelope_mul_le f N hΔ (abs_le.mpr hξ)

/-- **Interval dichotomy between sub-horizon negativity and exponential height escape.** -/
theorem exists_interval_re_W_neg_or_height_escape {C a B₁ B : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hB₁ : B₁ < B)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊) :
    ∃ ξ₀ : ℝ, B < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ₀).re ∧
      ∀ ξ ∈ Icc (-primePersistenceRadius f ⌊Real.exp (2 * a)⌋₊ (B - B₁))
          (primePersistenceRadius f ⌊Real.exp (2 * a)⌋₊ (B - B₁)),
        B₁ < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re ∧
          ((zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f)).re < 0 ∨
            B₁ - 2 * Real.exp a * (∫ u, ‖f u‖) ^ 2 -
              (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) <
              (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ + ξ₀|)) := by
  obtain ⟨⟨ξ₀, hξ₀, hint⟩, -⟩ :=
    exists_interval_gt_and_lt_re_primePolynomial f ⌊Real.exp (2 * a)⌋₊ hB₁ hB
  refine ⟨ξ₀, hξ₀, fun ξ hξ => ?_⟩
  have hB₁_lt := hint ξ hξ
  refine ⟨hB₁_lt, ?_⟩
  by_cases hW : (zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f)).re < 0
  · exact Or.inl hW
  · refine Or.inr ?_
    rw [not_lt, zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re] at hW
    have harch := re_archPart_le hC0 hC hf hfs (ξ + ξ₀)
    linarith

/-- **Positive-measure interval height escape under `RiemannHypothesis`.** -/
theorem exists_interval_height_escape_of_riemannHypothesis (hRH : RiemannHypothesis)
    {C a B₁ B : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hB₁ : B₁ < B)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊) :
    ∃ ξ₀ : ℝ, B < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ₀).re ∧
      ∀ ξ ∈ Icc (-primePersistenceRadius f ⌊Real.exp (2 * a)⌋₊ (B - B₁))
          (primePersistenceRadius f ⌊Real.exp (2 * a)⌋₊ (B - B₁)),
        B₁ < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re ∧
          B₁ < (archPart f (ξ + ξ₀)).re ∧
          B₁ - 2 * Real.exp a * (∫ u, ‖f u‖) ^ 2 -
            (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) <
            (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ + ξ₀|) := by
  obtain ⟨ξ₀, hξ₀, hint⟩ :=
    exists_interval_re_W_neg_or_height_escape hC0 hC hf hfs hB₁ hB
  refine ⟨ξ₀, hξ₀, fun ξ hξ => ?_⟩
  obtain ⟨hre, hW | hesc⟩ := hint ξ hξ
  · exfalso
    have hle := riemannHypothesis_iff_primePolynomial_le_archPart.mp hRH a f hf hfs (ξ + ξ₀)
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re] at hW
    linarith
  · have hle := riemannHypothesis_iff_primePolynomial_le_archPart.mp hRH a f hf hfs (ξ + ξ₀)
    exact ⟨hre, lt_of_lt_of_le hre hle, hesc⟩

/-! ## §3. Windowed Chebyshev Rarity Below and Beyond the Square-Root Threshold -/

/-- Plancherel identity for the Fejér-type height weight `‖h_η(-2πξ)‖²`:
`∫ ξ, ‖paperFT η (-(2πξ))‖² = ∫ t, ‖η t‖²`. -/
theorem integral_normSq_paperFT_neg_two_pi_eq {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 = ∫ t, ‖η t‖ ^ 2 := by
  have h := integral_normSq_mul_normSq_expSum_of_separated hη hηs
    ({()} : Finset Unit) (fun _ => 1) (fun _ => 0)
    (fun j _ k _ hne => absurd (Subsingleton.elim j k) hne)
  simp only [expSum, Finset.sum_singleton, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one, norm_one, one_pow] at h
  exact h

/-- Windowed Chebyshev superlevel bound for `(primePolynomial f ⌊e^{2a}⌋₊ (ξ + ξ₀)).re` below
the square-root threshold (`2r e^{2a} ≤ 1`). -/
theorem lintegral_re_primePolynomial_ge_le_of_separated {a r β : ℝ} (ha : 0 ≤ a)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r)
    (hX : 2 * r * Real.exp (2 * a) ≤ 1) (ξ₀ : ℝ) (hβ : 0 < β) :
    ∫⁻ ξ, {ξ | β ≤ (primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re}.indicator
        (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
      ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ / β ^ 2) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set N := ⌊Real.exp (2 * a)⌋₊ with hNdef
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
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ with hC
  have hQb : ∀ ξ, ‖Q ξ‖ ≤ C := fun ξ => norm_expSum_le _ _ _ _
  set G : ℝ → ℝ := fun ξ => P ξ * ‖Q ξ‖ ^ 2 / β ^ 2 with hG
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => by positivity
  have hGi : Integrable G := by
    refine (hPi.mul_const (C ^ 2 / β ^ 2)).mono'
      ((hPc.mul (hQc.norm.pow 2)).div_const _).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (hG0 ξ)]
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    have hQ2 : ‖Q ξ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hQb ξ) 2
    show P ξ * ‖Q ξ‖ ^ 2 / β ^ 2 ≤ P ξ * (C ^ 2 / β ^ 2)
    rw [mul_div_assoc]
    gcongr
  have hGint : ∫ ξ, G ξ = (∫ t, ‖η t‖ ^ 2) * primeVariance f N / β ^ 2 := by
    have hvar := integral_windowed_sq_deviation_eq ha hf hfs hη hηs hX ξ₀
    have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
        archPart f (ξ + ξ₀)‖ = ‖Q ξ‖ := by
      intro ξ
      rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
    simp_rw [hdev] at hvar
    simp only [hG, integral_div]
    rw [hvar]
  rw [← hGint, ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hG0)]
  refine lintegral_mono fun ξ => ?_
  by_cases hξ : ξ ∈ {ξ | β ≤ (primePolynomial f N (ξ + ξ₀)).re}
  · rw [Set.indicator_of_mem hξ]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Set.mem_setOf_eq] at hξ
    have hQn : β ≤ ‖Q ξ‖ := le_trans hξ (Complex.re_le_norm _)
    have hratio : 1 ≤ ‖Q ξ‖ ^ 2 / β ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hβ.le hQn 2
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    calc ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 = P ξ * 1 := by rw [mul_one]
      _ ≤ P ξ * (‖Q ξ‖ ^ 2 / β ^ 2) := mul_le_mul_of_nonneg_left hratio hP0
      _ = G ξ := by rw [hG]; ring
  · rw [Set.indicator_of_notMem hξ]
    exact bot_le

/-- Windowed Chebyshev superlevel bound for `(primePolynomial f ⌊e^{2a}⌋₊ (ξ + ξ₀)).re` beyond
the square-root threshold (`0 ≤ r ≤ log 2`). -/
theorem lintegral_re_primePolynomial_ge_le_beyond_threshold {a r β : ℝ}
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2)
    (hηs : tsupport η ⊆ Icc (-r) r) (ξ₀ : ℝ) (hβ : 0 < β) :
    ∫⁻ ξ, {ξ | β ≤ (primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re}.indicator
        (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
      ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) *
        (1 + Real.exp (2 * a) * (Real.exp (2 * r) - Real.exp (-(2 * r)))) *
        primeVariance f ⌊Real.exp (2 * a)⌋₊ / β ^ 2) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set N := ⌊Real.exp (2 * a)⌋₊ with hNdef
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
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ with hC
  have hQb : ∀ ξ, ‖Q ξ‖ ≤ C := fun ξ => norm_expSum_le _ _ _ _
  set G : ℝ → ℝ := fun ξ => P ξ * ‖Q ξ‖ ^ 2 / β ^ 2 with hG
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => by positivity
  have hGi : Integrable G := by
    refine (hPi.mul_const (C ^ 2 / β ^ 2)).mono'
      ((hPc.mul (hQc.norm.pow 2)).div_const _).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (hG0 ξ)]
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    have hQ2 : ‖Q ξ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hQb ξ) 2
    show P ξ * ‖Q ξ‖ ^ 2 / β ^ 2 ≤ P ξ * (C ^ 2 / β ^ 2)
    rw [mul_div_assoc]
    gcongr
  have hGint : ∫ ξ, G ξ ≤ (∫ t, ‖η t‖ ^ 2) *
      (1 + Real.exp (2 * a) * (Real.exp (2 * r) - Real.exp (-(2 * r)))) *
      primeVariance f N / β ^ 2 := by
    have hvar := integral_windowed_sq_deviation_le hf hfs hη hr hr2 hηs ξ₀
    have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
        archPart f (ξ + ξ₀)‖ = ‖Q ξ‖ := by
      intro ξ
      rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
    simp_rw [hdev] at hvar
    simp only [hG, integral_div]
    exact div_le_div_of_nonneg_right hvar (sq_nonneg β)
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hGint)
  rw [ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hG0)]
  refine lintegral_mono fun ξ => ?_
  by_cases hξ : ξ ∈ {ξ | β ≤ (primePolynomial f N (ξ + ξ₀)).re}
  · rw [Set.indicator_of_mem hξ]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Set.mem_setOf_eq] at hξ
    have hQn : β ≤ ‖Q ξ‖ := le_trans hξ (Complex.re_le_norm _)
    have hratio : 1 ≤ ‖Q ξ‖ ^ 2 / β ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hβ.le hQn 2
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    calc ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 = P ξ * 1 := by rw [mul_one]
      _ ≤ P ξ * (‖Q ξ‖ ^ 2 / β ^ 2) := mul_le_mul_of_nonneg_left hratio hP0
      _ = G ξ := by rw [hG]; ring
  · rw [Set.indicator_of_notMem hξ]
    exact bot_le

/-- Beyond-threshold Chebyshev bound for negative localized Weil forms (`0 ≤ r ≤ log 2`). -/
theorem lintegral_bad_heights_le_beyond_threshold {a r : ℝ}
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2)
    (hηs : tsupport η ⊆ Icc (-r) r) (ξ₀ : ℝ) {U : Set ℝ}
    {A₀ : ℝ} (hA₀ : 0 < A₀) (hU : ∀ ξ ∈ U, A₀ ≤ (archPart f (ξ + ξ₀)).re) :
    ∫⁻ ξ, (U ∩ {ξ | (zetaZeroConfig.W (heightShift (ξ + ξ₀) f)
        (heightShift (ξ + ξ₀) f)).re < 0}).indicator
        (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
      ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) *
        (1 + Real.exp (2 * a) * (Real.exp (2 * r) - Real.exp (-(2 * r)))) *
        primeVariance f ⌊Real.exp (2 * a)⌋₊ / A₀ ^ 2) := by
  refine le_trans ?_
    (lintegral_re_primePolynomial_ge_le_beyond_threshold hf hfs hη hr hr2 hηs ξ₀ hA₀)
  refine lintegral_mono fun ξ => ?_
  by_cases hξ : ξ ∈ U ∩ {ξ | (zetaZeroConfig.W (heightShift (ξ + ξ₀) f)
      (heightShift (ξ + ξ₀) f)).re < 0}
  · rw [Set.indicator_of_mem hξ]
    have hU' := hξ.1
    have hneg := hξ.2
    simp only [Set.mem_setOf_eq] at hneg
    have hA := hU ξ hU'
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re] at hneg
    have hre : ξ ∈ {ξ | A₀ ≤ (primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re} := by
      simp only [Set.mem_setOf_eq]
      linarith
    rw [Set.indicator_of_mem hre]
  · rw [Set.indicator_of_notMem hξ]
    exact bot_le

/-- **Windowed Mean-Square Decorrelation Obstruction.** Whenever `primeVariance f ⌊e^{2a}⌋₊ < β²`
and `0 < ∫ t, ‖η t‖²` for a window `η` with `2r e^{2a} ≤ 1`, there exists a height `ξ ∈ ℝ` where
`‖primePolynomial f ⌊e^{2a}⌋₊ (ξ + ξ₀)‖ < β`. -/
theorem exists_norm_primePolynomial_lt_of_primeVariance_lt {a r β : ℝ} (ha : 0 ≤ a)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r)
    (hX : 2 * r * Real.exp (2 * a) ≤ 1) (hη0 : 0 < ∫ t, ‖η t‖ ^ 2)
    (ξ₀ : ℝ) (hβ0 : 0 ≤ β) (hvar_lt : primeVariance f ⌊Real.exp (2 * a)⌋₊ < β ^ 2) :
    ∃ ξ : ℝ, ‖primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)‖ < β := by
  by_contra hcon
  push Not at hcon
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set N := ⌊Real.exp (2 * a)⌋₊ with hNdef
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP
  set Q : ℝ → ℂ := fun ξ => primePolynomial f N (ξ + ξ₀) with hQ
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
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ with hC
  have hQb : ∀ ξ, ‖Q ξ‖ ≤ C := fun ξ => norm_expSum_le _ _ _ _
  have hPQi : Integrable (fun ξ => P ξ * ‖Q ξ‖ ^ 2) := by
    refine (hPi.mul_const (C ^ 2)).mono'
      (hPc.mul (hQc.norm.pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hQb ξ) 2) (sq_nonneg _)
  have hmono : (∫ ξ, β ^ 2 * P ξ) ≤ ∫ ξ, P ξ * ‖Q ξ‖ ^ 2 := by
    refine integral_mono (hPi.const_mul (β ^ 2)) hPQi fun ξ => ?_
    have hsq : β ^ 2 ≤ ‖Q ξ‖ ^ 2 := pow_le_pow_left₀ hβ0 (hcon ξ) 2
    nlinarith [sq_nonneg (‖paperFT η (-(2 * π * (ξ : ℂ)))‖)]
  rw [integral_const_mul, show ∫ ξ, P ξ = ∫ t, ‖η t‖ ^ 2 from
    integral_normSq_paperFT_neg_two_pi_eq hη hηs] at hmono
  have h4 : ∫ ξ, P ξ * ‖Q ξ‖ ^ 2 = (∫ t, ‖η t‖ ^ 2) * primeVariance f N := by
    have hvar := integral_windowed_sq_deviation_eq ha hf hfs hη hηs hX ξ₀
    have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
        archPart f (ξ + ξ₀)‖ = ‖Q ξ‖ := by
      intro ξ
      rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
    simp_rw [hdev] at hvar
    exact hvar
  rw [h4] at hmono
  nlinarith

/-- **Beyond-Threshold Windowed Mean-Square Decorrelation Obstruction.** Whenever
`(1 + e^{2a}(e^{2r} - e^{-2r})) V_f(⌊e^{2a}⌋₊) < β²` and `0 < ∫ t, ‖η t‖²` for a window `η` with
`0 ≤ r ≤ log 2`, there exists a height `ξ ∈ ℝ` where
`‖primePolynomial f ⌊e^{2a}⌋₊ (ξ + ξ₀)‖ < β`. -/
theorem exists_norm_primePolynomial_lt_beyond_threshold {a r β : ℝ}
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2)
    (hηs : tsupport η ⊆ Icc (-r) r) (hη0 : 0 < ∫ t, ‖η t‖ ^ 2)
    (ξ₀ : ℝ) (hβ0 : 0 ≤ β)
    (hvar_lt :
      (1 + Real.exp (2 * a) * (Real.exp (2 * r) - Real.exp (-(2 * r)))) *
        primeVariance f ⌊Real.exp (2 * a)⌋₊ < β ^ 2) :
    ∃ ξ : ℝ, ‖primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)‖ < β := by
  by_contra hcon
  push Not at hcon
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set N := ⌊Real.exp (2 * a)⌋₊ with hNdef
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP
  set Q : ℝ → ℂ := fun ξ => primePolynomial f N (ξ + ξ₀) with hQ
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
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ with hC
  have hQb : ∀ ξ, ‖Q ξ‖ ≤ C := fun ξ => norm_expSum_le _ _ _ _
  have hPQi : Integrable (fun ξ => P ξ * ‖Q ξ‖ ^ 2) := by
    refine (hPi.mul_const (C ^ 2)).mono'
      (hPc.mul (hQc.norm.pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hQb ξ) 2) (sq_nonneg _)
  have hmono : (∫ ξ, β ^ 2 * P ξ) ≤ ∫ ξ, P ξ * ‖Q ξ‖ ^ 2 := by
    refine integral_mono (hPi.const_mul (β ^ 2)) hPQi fun ξ => ?_
    have hsq : β ^ 2 ≤ ‖Q ξ‖ ^ 2 := pow_le_pow_left₀ hβ0 (hcon ξ) 2
    nlinarith [sq_nonneg (‖paperFT η (-(2 * π * (ξ : ℂ)))‖)]
  rw [integral_const_mul, show ∫ ξ, P ξ = ∫ t, ‖η t‖ ^ 2 from
    integral_normSq_paperFT_neg_two_pi_eq hη hηs] at hmono
  have h4 : ∫ ξ, P ξ * ‖Q ξ‖ ^ 2 ≤ (∫ t, ‖η t‖ ^ 2) *
      (1 + Real.exp (2 * a) * (Real.exp (2 * r) - Real.exp (-(2 * r)))) *
      primeVariance f N := by
    have hvar := integral_windowed_sq_deviation_le hf hfs hη hr hr2 hηs ξ₀
    have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
        archPart f (ξ + ξ₀)‖ = ‖Q ξ‖ := by
      intro ξ
      rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
    simp_rw [hdev] at hvar
    exact hvar
  nlinarith

/-! ## §4. The Envelope–Variance–Lipschitz Uncertainty Inequality & Peak Decorrelation -/

/-- **Envelope–Variance–Lipschitz Uncertainty Inequality below the square-root threshold.**
For every `0 ≤ B₁ < B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ - primePowerTailEnvelope f ⌊e^{2a}⌋₊`
and every `C²` window `η` supported in `[-r, r]` with `2r e^{2a} ≤ 1`, the local window mass on
the persistence interval `[-δ, δ]` (`δ = primePersistenceRadius f ⌊e^{2a}⌋₊ (B - B₁)`) satisfies
`B₁² ∫_{ξ ∈ [-δ, δ]} ‖h_η(-2πξ)‖² dξ ≤ (∫ ‖η‖²) V_f(⌊e^{2a}⌋₊)`. -/
theorem setIntegral_persistence_mul_sq_le_primeVariance {a r B₁ B : ℝ} (ha : 0 ≤ a)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r)
    (hX : 2 * r * Real.exp (2 * a) ≤ 1) (hB₁0 : 0 ≤ B₁) (hB₁ : B₁ < B)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊) :
    B₁ ^ 2 * (∫ ξ in Icc (-primePersistenceRadius f ⌊Real.exp (2 * a)⌋₊ (B - B₁))
        (primePersistenceRadius f ⌊Real.exp (2 * a)⌋₊ (B - B₁)),
        ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2) ≤
      (∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set N := ⌊Real.exp (2 * a)⌋₊ with hNdef
  set δ := primePersistenceRadius f N (B - B₁) with hδdef
  obtain ⟨⟨ξ₀, -, hint⟩, -⟩ := exists_interval_gt_and_lt_re_primePolynomial f N hB₁ hB
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP
  set Q : ℝ → ℂ := fun ξ => primePolynomial f N (ξ + ξ₀) with hQ
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
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ with hC
  have hQb : ∀ ξ, ‖Q ξ‖ ≤ C := fun ξ => norm_expSum_le _ _ _ _
  have hPQi : Integrable (fun ξ => P ξ * ‖Q ξ‖ ^ 2) := by
    refine (hPi.mul_const (C ^ 2)).mono'
      (hPc.mul (hQc.norm.pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hQb ξ) 2) (sq_nonneg _)
  have h1 : B₁ ^ 2 * (∫ ξ in Icc (-δ) δ, P ξ) = ∫ ξ in Icc (-δ) δ, B₁ ^ 2 * P ξ := by
    rw [integral_const_mul]
  have h2 : (∫ ξ in Icc (-δ) δ, B₁ ^ 2 * P ξ) ≤ ∫ ξ in Icc (-δ) δ, P ξ * ‖Q ξ‖ ^ 2 := by
    refine setIntegral_mono_on (hPi.const_mul (B₁ ^ 2)).integrableOn hPQi.integrableOn
      measurableSet_Icc fun ξ hξ => ?_
    have hre : B₁ ≤ ‖Q ξ‖ := (hint ξ hξ).le.trans (Complex.re_le_norm _)
    have hsq : B₁ ^ 2 ≤ ‖Q ξ‖ ^ 2 := pow_le_pow_left₀ hB₁0 hre 2
    nlinarith [sq_nonneg (‖paperFT η (-(2 * π * (ξ : ℂ)))‖)]
  have h3 : (∫ ξ in Icc (-δ) δ, P ξ * ‖Q ξ‖ ^ 2) ≤ ∫ ξ, P ξ * ‖Q ξ‖ ^ 2 :=
    setIntegral_le_integral hPQi (Eventually.of_forall fun ξ => by positivity)
  have h4 : ∫ ξ, P ξ * ‖Q ξ‖ ^ 2 = (∫ t, ‖η t‖ ^ 2) * primeVariance f N := by
    have hvar := integral_windowed_sq_deviation_eq ha hf hfs hη hηs hX ξ₀
    have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
        archPart f (ξ + ξ₀)‖ = ‖Q ξ‖ := by
      intro ξ
      rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
    simp_rw [hdev] at hvar
    exact hvar
  linarith

/-- **Envelope–Variance–Lipschitz Uncertainty Inequality beyond the square-root threshold.** -/
theorem setIntegral_persistence_mul_sq_le_beyond_threshold {a r B₁ B : ℝ}
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2)
    (hηs : tsupport η ⊆ Icc (-r) r) (hB₁0 : 0 ≤ B₁) (hB₁ : B₁ < B)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊) :
    B₁ ^ 2 * (∫ ξ in Icc (-primePersistenceRadius f ⌊Real.exp (2 * a)⌋₊ (B - B₁))
        (primePersistenceRadius f ⌊Real.exp (2 * a)⌋₊ (B - B₁)),
        ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2) ≤
      (∫ t, ‖η t‖ ^ 2) *
        (1 + Real.exp (2 * a) * (Real.exp (2 * r) - Real.exp (-(2 * r)))) *
        primeVariance f ⌊Real.exp (2 * a)⌋₊ := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set N := ⌊Real.exp (2 * a)⌋₊ with hNdef
  set δ := primePersistenceRadius f N (B - B₁) with hδdef
  obtain ⟨⟨ξ₀, -, hint⟩, -⟩ := exists_interval_gt_and_lt_re_primePolynomial f N hB₁ hB
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP
  set Q : ℝ → ℂ := fun ξ => primePolynomial f N (ξ + ξ₀) with hQ
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
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ with hC
  have hQb : ∀ ξ, ‖Q ξ‖ ≤ C := fun ξ => norm_expSum_le _ _ _ _
  have hPQi : Integrable (fun ξ => P ξ * ‖Q ξ‖ ^ 2) := by
    refine (hPi.mul_const (C ^ 2)).mono'
      (hPc.mul (hQc.norm.pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hQb ξ) 2) (sq_nonneg _)
  have h1 : B₁ ^ 2 * (∫ ξ in Icc (-δ) δ, P ξ) = ∫ ξ in Icc (-δ) δ, B₁ ^ 2 * P ξ := by
    rw [integral_const_mul]
  have h2 : (∫ ξ in Icc (-δ) δ, B₁ ^ 2 * P ξ) ≤ ∫ ξ in Icc (-δ) δ, P ξ * ‖Q ξ‖ ^ 2 := by
    refine setIntegral_mono_on (hPi.const_mul (B₁ ^ 2)).integrableOn hPQi.integrableOn
      measurableSet_Icc fun ξ hξ => ?_
    have hre : B₁ ≤ ‖Q ξ‖ := (hint ξ hξ).le.trans (Complex.re_le_norm _)
    have hsq : B₁ ^ 2 ≤ ‖Q ξ‖ ^ 2 := pow_le_pow_left₀ hB₁0 hre 2
    nlinarith [sq_nonneg (‖paperFT η (-(2 * π * (ξ : ℂ)))‖)]
  have h3 : (∫ ξ in Icc (-δ) δ, P ξ * ‖Q ξ‖ ^ 2) ≤ ∫ ξ, P ξ * ‖Q ξ‖ ^ 2 :=
    setIntegral_le_integral hPQi (Eventually.of_forall fun ξ => by positivity)
  have h4 : ∫ ξ, P ξ * ‖Q ξ‖ ^ 2 ≤ (∫ t, ‖η t‖ ^ 2) *
      (1 + Real.exp (2 * a) * (Real.exp (2 * r) - Real.exp (-(2 * r)))) *
      primeVariance f N := by
    have hvar := integral_windowed_sq_deviation_le hf hfs hη hr hr2 hηs ξ₀
    have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
        archPart f (ξ + ξ₀)‖ = ‖Q ξ‖ := by
      intro ξ
      rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
    simp_rw [hdev] at hvar
    exact hvar
  linarith

/-- **Joint Kronecker Peak Persistence and Windowed Decorrelation Theorem.**
For every threshold pair `B₁ < B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ - primePowerTailEnvelope f ⌊e^{2a}⌋₊`
and every superlevel `β > 0`, there exists a Kronecker peak center `ξ₀ ∈ ℝ` around which:
1. `(primePolynomial f ⌊e^{2a}⌋₊ ξ₀).re > B`;
2. On the entire persistence interval `ξ ∈ [-δ, δ]` (`δ = primePersistenceRadius f ⌊e^{2a}⌋₊ (B - B₁)`),
   `(primePolynomial f ⌊e^{2a}⌋₊ (ξ + ξ₀)).re > B₁` and the sub-horizon negativity vs. exponential
   height-escape dichotomy holds;
3. In the height window centered at `ξ₀` itself, the `η`-windowed weight of
   `{ξ | β ≤ (primePolynomial f ⌊e^{2a}⌋₊ (ξ + ξ₀)).re}` is bounded by
   `‖η‖₂² (1 + e^{2a}(e^{2r} - e^{-2r})) V_f(⌊e^{2a}⌋₊) / β²` for every `0 ≤ r ≤ log 2`. -/
theorem exists_kronecker_peak_persistence_and_windowed_decorrelation
    {C a r B₁ B β : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2)
    (hηs : tsupport η ⊆ Icc (-r) r) (hB₁ : B₁ < B)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊) (hβ : 0 < β) :
    ∃ ξ₀ : ℝ,
      B < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ₀).re ∧
      (∀ ξ ∈ Icc (-primePersistenceRadius f ⌊Real.exp (2 * a)⌋₊ (B - B₁))
          (primePersistenceRadius f ⌊Real.exp (2 * a)⌋₊ (B - B₁)),
        B₁ < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re ∧
          ((zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f)).re < 0 ∨
            B₁ - 2 * Real.exp a * (∫ u, ‖f u‖) ^ 2 -
              (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) <
              (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ + ξ₀|))) ∧
      ∫⁻ ξ, {ξ | β ≤ (primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re}.indicator
          (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
        ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) *
          (1 + Real.exp (2 * a) * (Real.exp (2 * r) - Real.exp (-(2 * r)))) *
          primeVariance f ⌊Real.exp (2 * a)⌋₊ / β ^ 2) := by
  obtain ⟨ξ₀, hξ₀, hint⟩ :=
    exists_interval_re_W_neg_or_height_escape hC0 hC hf hfs hB₁ hB
  exact ⟨ξ₀, hξ₀, hint,
    lintegral_re_primePolynomial_ge_le_beyond_threshold hf hfs hη hr hr2 hηs ξ₀ hβ⟩

end GaloisForLFunctions.SquareRootThreshold
