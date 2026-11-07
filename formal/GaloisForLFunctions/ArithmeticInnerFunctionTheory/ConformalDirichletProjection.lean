import GaloisForLFunctions.ArithmeticInnerFunctionTheory.NearExtremalMollifiersAreRigid

/-!+# Conformal coordinates for Dirichlet modes

The chart centred at one sends a Dirichlet mode with logarithmic frequency `t` to
`exp(-t/(1-z))`. Its Hardy coefficients are the conformal–Dirichlet mixed moments.
Horizontal translation acts by an explicit fractional linear map on the disc.
-/

open Complex Metric Filter Topology MeasureTheory Set Finset
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

/-- Translation by `δ` in the half-plane, expressed in the chart centred at one. -/
def translatedDiscCoord (δ : ℝ) (z : ℂ) : ℂ :=
  ((δ : ℂ) + (1 - (δ : ℂ)) * z) / (1 + (δ : ℂ) - (δ : ℂ) * z)

theorem blaschkeCoord_one_translate {δ : ℝ} {z : ℂ} (hz : z ≠ 1)
    (hden : 1 + (δ : ℂ) - (δ : ℂ) * z ≠ 0) :
    blaschkeCoord 1 (discChart 1 z + (δ : ℂ)) = translatedDiscCoord δ z := by
  have hz' : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  rw [blaschkeCoord_one, discChart_one, translatedDiscCoord]
  field_simp
  <;> ring

@[simp] theorem translatedDiscCoord_zero (z : ℂ) : translatedDiscCoord 0 z = z := by
  simp [translatedDiscCoord]

@[simp] theorem translatedDiscCoord_at_zero (δ : ℝ) :
    translatedDiscCoord δ 0 = (δ : ℂ) / (1 + (δ : ℂ)) := by
  simp [translatedDiscCoord]

/-- The Dirichlet mode in the disc chart, with logarithmic frequency `t`. -/
def dirichletDisc (t : ℝ) (z : ℂ) : ℂ := Complex.exp (-(t : ℂ) * (1 - z)⁻¹)

theorem dirichletDisc_zero (t : ℝ) : dirichletDisc t 0 = Complex.exp (-(t : ℂ)) := by
  simp [dirichletDisc]

theorem differentiableAt_dirichletDisc (t : ℝ) {z : ℂ} (hz : z ≠ 1) :
    DifferentiableAt ℂ (dirichletDisc t) z := by
  have hi : DifferentiableAt ℂ (fun u : ℂ => (1 - u)⁻¹) z :=
    ((differentiableAt_const _).sub differentiableAt_id).inv (sub_ne_zero.mpr hz.symm)
  exact Complex.differentiable_exp.differentiableAt.comp z (hi.const_mul _)

theorem measurable_dirichletDisc (t : ℝ) : Measurable (dirichletDisc t) := by
  unfold dirichletDisc
  fun_prop

/-- The singular boundary value at one is harmless: the whole closed disc is bounded by one. -/
theorem norm_dirichletDisc_le_one {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖dirichletDisc t z‖ ≤ 1 := by
  by_cases hz1 : z = 1
  · simp [dirichletDisc, hz1]
  have hr := one_half_le_re_inv hz hz1
  rw [dirichletDisc, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  nlinarith only [ht, hr]

theorem isHardyDisc_dirichletDisc {t : ℝ} (ht : 0 ≤ t) : IsHardyDisc (dirichletDisc t) := by
  refine ⟨fun z hz => (differentiableAt_dirichletDisc t hz).differentiableWithinAt,
    measurable_dirichletDisc t, ?_, ?_, ?_⟩
  · refine ⟨4, by norm_num, fun z hz hz1 => ?_⟩
    have hd : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1.symm)
    have h2 : ‖1 - z‖ ≤ 2 := by
      calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 2 := by simpa using hz
    have h4 : ‖1 - z‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (1 - z)]
    exact (norm_dirichletDisc_le_one ht hz).trans ((le_div_iff₀ (by positivity)).mpr (by simpa using h4))
  · refine ⟨1, fun x hx hx1 => norm_dirichletDisc_le_one ht ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)]
    exact hx1.le
  · have hm : Measurable (fun θ : ℝ => ‖dirichletDisc t (circleMap 0 1 θ)‖ ^ 2) :=
      ((measurable_dirichletDisc t).comp (continuous_circleMap 0 1).measurable).norm.pow_const 2
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0
      (2 * Real.pi)).mono_fun hm.aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
    have hn := norm_dirichletDisc_le_one ht (norm_circleMap_zero_one θ).le
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_one]
    nlinarith only [hn, norm_nonneg (dirichletDisc t (circleMap 0 1 θ))]

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
