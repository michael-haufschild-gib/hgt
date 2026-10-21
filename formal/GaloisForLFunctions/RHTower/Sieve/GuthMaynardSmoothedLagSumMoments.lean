import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSmoothedLagSum
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSumL4
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 8.3 for `R̃`: the fourth moment of the smoothed lag sum

For a smoothing pair `ψ₁, ψ₂` (`IsSmoothingPair`: continuous, compactly supported, values in
`[0, 1]`) with `ψ₂` supported in `[A⁻¹, A]`, and `NM > 0`,

`∫_ℝ R̃(u)⁴ du ≤ (∫ψ₁)² ∫_{A⁻¹}^{A} |R|⁴ ≤ (∫ψ₁)² · (5π/2) A max(1, log A) · E(W)`.

This is the `R̃`-half of Lemma 8.3 of Guth–Maynard (`∫_{v ≍ 1} |R̃(v)|⁴ dv ⪅ E(W)`), over the whole
line and with the explicit factor `(∫ψ₁)²` (which is `⪅ 1` for the bumps of Proposition 7.2).

Proof. `R̃² = k ⋆ g` with the kernel `k(y) = NM ψ₁(NMy)` of mass `∫ψ₁` and `g = ψ₂ |R|²`. Young's
inequality `‖k ⋆ g‖₂ ≤ ‖k‖₁ ‖g‖₂` (corpus `lintegral_enorm_sq_le_of_convolution_bound`) and
`0 ≤ ψ₂ ≤ 1` give the first inequality; the fourth-moment bound of `GuthMaynardLagSumL4` gives the
second.
-/

open MeasureTheory Set
open scoped ENNReal

namespace RHTower.GuthMaynard

noncomputable section

variable {ψ₁ ψ₂ : ℝ → ℝ} {N M A : ℝ}

/-- The smoothing kernel `k(y) = NM ψ₁(NMy)` has the mass of `ψ₁`. -/
theorem lintegral_enorm_smoothingKernel (h : IsSmoothingPair ψ₁ ψ₂) (hNM : 0 < N * M) :
    ∫⁻ y, ‖N * M * ψ₁ (N * M * y)‖ₑ = ENNReal.ofReal (∫ x, ψ₁ x) := by
  have hψ₁ : Integrable ψ₁ := h.continuous₁.integrable_of_hasCompactSupport h.compactSupport₁
  have hk : Integrable fun y => N * M * ψ₁ (N * M * y) :=
    (hψ₁.comp_mul_left' hNM.ne').const_mul _
  rw [← ofReal_integral_norm_eq_lintegral_enorm hk]
  congr 1
  have hnorm : ∀ y, ‖N * M * ψ₁ (N * M * y)‖ = N * M * ψ₁ (N * M * y) := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hNM.le (h.nonneg₁ _))]
  simp_rw [hnorm]
  rw [integral_const_mul, Measure.integral_comp_mul_left, abs_inv, abs_of_pos hNM, smul_eq_mul,
    mul_inv_cancel_left₀ hNM.ne']

/-- `∫ (ψ₂ |R|²)² ≤ ∫_{A⁻¹}^{A} |R|⁴` when `0 ≤ ψ₂ ≤ 1` vanishes off `[A⁻¹, A]`. -/
theorem lintegral_enorm_sq_density_le (h : IsSmoothingPair ψ₁ ψ₂)
    (hsupp : ∀ x, x ∉ Icc A⁻¹ A → ψ₂ x = 0) (W : Finset ℝ) :
    ∫⁻ x, ‖ψ₂ x * ‖lagSum W x‖ ^ 2‖ₑ ^ 2
      ≤ ENNReal.ofReal (∫ x in Icc A⁻¹ A, ‖lagSum W x‖ ^ 4) := by
  have hint : IntegrableOn (fun x => ‖lagSum W x‖ ^ 4) (Icc A⁻¹ A) :=
    Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
      ((measurable_lagSum W).norm.pow_const 4).aestronglyMeasurable (M := (W.card : ℝ) ^ 4)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 4)
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => by positivity), ← lintegral_indicator measurableSet_Icc]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ Icc A⁻¹ A
  · rw [indicator_of_mem hx, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 := h.nonneg₂ x
    have h1 := h.le_one₂ x
    have hR : 0 ≤ ‖lagSum W x‖ ^ 4 := by positivity
    calc |ψ₂ x * ‖lagSum W x‖ ^ 2| ^ 2 = ψ₂ x ^ 2 * ‖lagSum W x‖ ^ 4 := by
          rw [sq_abs]; ring
      _ ≤ 1 * ‖lagSum W x‖ ^ 4 := by
          gcongr
          nlinarith
      _ = ‖lagSum W x‖ ^ 4 := one_mul _
  · rw [hsupp x hx]
    simp

/-- **Young's inequality for `R̃`**, in `ℝ≥0∞`: `∫ R̃⁴ ≤ (∫ψ₁)² ∫_{A⁻¹}^{A} |R|⁴`. -/
theorem lintegral_smoothedLagSum_pow_four_le (h : IsSmoothingPair ψ₁ ψ₂) (hNM : 0 < N * M)
    (hsupp : ∀ x, x ∉ Icc A⁻¹ A → ψ₂ x = 0) (W : Finset ℝ) :
    ∫⁻ u, ENNReal.ofReal (smoothedLagSum ψ₁ ψ₂ N M W u ^ 4)
      ≤ ENNReal.ofReal ((∫ x, ψ₁ x) ^ 2 * ∫ x in Icc A⁻¹ A, ‖lagSum W x‖ ^ 4) := by
  have hK : Measurable fun y : ℝ => ‖N * M * ψ₁ (N * M * y)‖ₑ := by
    have := h.continuous₁.measurable
    fun_prop
  have hF : Measurable fun x : ℝ => ‖ψ₂ x * ‖lagSum W x‖ ^ 2‖ₑ := by
    have := h.continuous₂.measurable
    have := measurable_lagSum W
    fun_prop
  have hG : ∀ u, ‖smoothedLagSum ψ₁ ψ₂ N M W u ^ 2‖ₑ ≤ ∫⁻ y, ‖N * M * ψ₁ (N * M * y)‖ₑ
      * ‖ψ₂ (u - y) * ‖lagSum W (u - y)‖ ^ 2‖ₑ := by
    intro u
    rw [smoothedLagSum_sq h hNM.le]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    rw [← lintegral_sub_left_eq_self (fun y => ‖N * M * ψ₁ (N * M * y)‖ₑ
      * ‖ψ₂ (u - y) * ‖lagSum W (u - y)‖ ^ 2‖ₑ) u]
    refine lintegral_congr fun x => ?_
    simp only [smoothedLagSumIntegrand, sub_sub_cancel]
    rw [← enorm_mul, mul_assoc]
  have hY := GaloisForLFunctions.HTGeometry.lintegral_enorm_sq_le_of_convolution_bound hK hF hG
  rw [lintegral_enorm_smoothingKernel h hNM] at hY
  have hψ₁ : 0 ≤ ∫ x, ψ₁ x := integral_nonneg h.nonneg₁
  have hleft : ∀ u, ‖smoothedLagSum ψ₁ ψ₂ N M W u ^ 2‖ₑ ^ 2
      = ENNReal.ofReal (smoothedLagSum ψ₁ ψ₂ N M W u ^ 4) := by
    intro u
    rw [Real.enorm_of_nonneg (by positivity), ← ENNReal.ofReal_pow (by positivity)]
    ring_nf
  simp_rw [hleft] at hY
  refine hY.trans ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hψ₁]
  gcongr
  exact lintegral_enorm_sq_density_le h hsupp W

/-- **Guth–Maynard Lemma 8.3 for `R̃`, comparison form.** `R̃⁴` is integrable on `ℝ` and
`∫ R̃⁴ ≤ (∫ψ₁)² ∫_{A⁻¹}^{A} |R|⁴`. -/
theorem integrable_and_integral_smoothedLagSum_pow_four_le (h : IsSmoothingPair ψ₁ ψ₂)
    (hNM : 0 < N * M) (hsupp : ∀ x, x ∉ Icc A⁻¹ A → ψ₂ x = 0) (W : Finset ℝ) :
    Integrable (fun u => smoothedLagSum ψ₁ ψ₂ N M W u ^ 4) ∧
      ∫ u, smoothedLagSum ψ₁ ψ₂ N M W u ^ 4
        ≤ (∫ x, ψ₁ x) ^ 2 * ∫ x in Icc A⁻¹ A, ‖lagSum W x‖ ^ 4 := by
  have hbound := lintegral_smoothedLagSum_pow_four_le h hNM hsupp W
  have hnn : 0 ≤ᵐ[volume] fun u => smoothedLagSum ψ₁ ψ₂ N M W u ^ 4 :=
    Filter.Eventually.of_forall fun u => by positivity
  have hmeas : AEStronglyMeasurable (fun u => smoothedLagSum ψ₁ ψ₂ N M W u ^ 4) volume :=
    ((measurable_smoothedLagSum h N M W).pow_const 4).aestronglyMeasurable
  have hrhs : 0 ≤ (∫ x, ψ₁ x) ^ 2 * ∫ x in Icc A⁻¹ A, ‖lagSum W x‖ ^ 4 :=
    mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Icc fun x _ => by positivity)
  refine ⟨⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).mpr
    (hbound.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  exact ENNReal.toReal_le_of_le_ofReal hrhs hbound

/-- **Guth–Maynard Lemma 8.3 for `R̃`, explicit form.** For `A ≥ 1`, a smoothing pair with `ψ₂`
supported in `[A⁻¹, A]`, and `NM > 0`:
`∫_ℝ R̃(u)⁴ du ≤ (∫ψ₁)² · (5π/2) A max(1, log A) · E(W)`. -/
theorem integral_smoothedLagSum_pow_four_le_energy (hA : 1 ≤ A) (h : IsSmoothingPair ψ₁ ψ₂)
    (hNM : 0 < N * M) (hsupp : ∀ x, x ∉ Icc A⁻¹ A → ψ₂ x = 0) (W : Finset ℝ) :
    ∫ u, smoothedLagSum ψ₁ ψ₂ N M W u ^ 4
      ≤ (∫ x, ψ₁ x) ^ 2 * (5 * Real.pi / 2 * A * max 1 (Real.log A)) * additiveEnergy W := by
  refine (integrable_and_integral_smoothedLagSum_pow_four_le h hNM hsupp W).2.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (setIntegral_Icc_inv_lagSum_pow_four_le hA W) (sq_nonneg _)

end

end RHTower.GuthMaynard
