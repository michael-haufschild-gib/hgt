import GaloisForLFunctions.RHTower.ConnesLevyKernelScaling
import GaloisForLFunctions.RHTower.SuzukiGammaFrequencySymbol
import GaloisForLFunctions.HTGeometry.ComplexScaledGammaIntegral
import Mathlib.MeasureTheory.Integral.Prod
import GaloisForLFunctions.HTGeometry.HalfLineBetaKernel
import Mathlib.Analysis.MellinTransform

/-!
# Absolute cosine-difference Mellin evaluation

On `0 < re α < 2`, Euler's Laplace representation and an absolutely integrable
product kernel reduce the cosine difference to a square-denominator beta
integral. This classical scalar identity supplies the explicit factor in the
actual Fourier primitive's Mellin transform. It asserts no regularity of the
inversion defect and no sparsity-to-rigidity implication.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
namespace RHTower.WeilHigherDenominator

/-- The positive cosine difference with its complex Mellin weight. -/
def cosineFractionalKernel (α : ℂ) (x : ℝ) : ℂ :=
  (1 - (Real.cos x : ℂ)) * (x : ℂ) ^ (-1 - α)

private lemma norm_one_sub_cos (x : ℝ) :
    ‖1 - (Real.cos x : ℂ)‖ = 1 - Real.cos x := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one x))]

/-- Absolute convergence on the full natural complex strip. -/
theorem integrable_cosineFractionalKernel {α : ℂ} (hα0 : 0 < α.re) (hα2 : α.re < 2) :
    IntegrableOn (cosineFractionalKernel α) (Ioi 0) := by
  apply Integrable.mono' (connes_levy_integrableOn hα0 hα2)
  · apply Measurable.aestronglyMeasurable
    change Measurable (fun x : ℝ =>
      (1 - (Real.cos x : ℂ)) * (x : ℂ) ^ (-1 - α))
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [cosineFractionalKernel, norm_mul, norm_one_sub_cos,
      Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.neg_re,
      Complex.one_re, connesLevyKernel]
    exact le_rfl

private def cosineLaplaceKernel (α : ℂ) (t x : ℝ) : ℂ :=
  (t : ℂ) ^ α * Complex.exp (-((x : ℂ) * t)) * (1 - (Real.cos x : ℂ))

private lemma integrable_cosineLaplace_slice {α : ℂ} (hα : 0 < α.re)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => cosineLaplaceKernel α t x) (Ioi 0) := by
  have h := (integrableOn_cpow_mul_cexp (a := α + 1) (c := (x : ℂ))
    (by simpa using add_pos hα zero_lt_one) hx).mul_const (1 - (Real.cos x : ℂ))
  simpa only [cosineLaplaceKernel, IntegrableOn, add_sub_cancel_right] using h

private lemma norm_cosineLaplaceKernel (α : ℂ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖cosineLaplaceKernel α t x‖ =
      (t ^ α.re * Real.exp (-(x * t))) * (1 - Real.cos x) := by
  simp only [cosineLaplaceKernel, norm_mul, norm_one_sub_cos,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  congr 3
  simp

private lemma integral_norm_cosineLaplaceKernel {α : ℂ} (hα : 0 < α.re)
    {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), ‖cosineLaplaceKernel α t x‖) =
      Real.Gamma (α.re + 1) * connesLevyKernel α.re x := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => norm_cosineLaplaceKernel α ht x), integral_mul_const]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := α.re + 1) (by linarith) hx
  simp only [add_sub_cancel_right] at h
  rw [h, one_div, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
  rw [show -(α.re + 1) = -1 - α.re by ring]
  dsimp [connesLevyKernel]
  ring

/-- Product integrability pays the interchange of the two improper integrals. -/
private lemma integrable_cosineLaplaceKernel {α : ℂ} (hα0 : 0 < α.re) (hα2 : α.re < 2) :
    Integrable (Function.uncurry (cosineLaplaceKernel α))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : AEStronglyMeasurable (Function.uncurry (cosineLaplaceKernel α))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply Measurable.aestronglyMeasurable
    change Measurable (fun tx : ℝ × ℝ => (tx.1 : ℂ) ^ α *
      Complex.exp (-((tx.2 : ℂ) * tx.1)) * (1 - (Real.cos tx.2 : ℂ)))
    fun_prop
  apply (integrable_prod_iff' hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact integrable_cosineLaplace_slice hα0 hx
  · apply ((connes_levy_integrableOn hα0 hα2).const_mul
      (Real.Gamma (α.re + 1))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (integral_norm_cosineLaplaceKernel hα0 hx).symm

private lemma cosineLaplace_euler {α : ℂ} (hα : 0 < α.re) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), cosineLaplaceKernel α t x) =
      Complex.Gamma (α + 1) * cosineFractionalKernel α x := by
  simp only [cosineLaplaceKernel]
  rw [integral_mul_const]
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi
    (a := α + 1) (by simpa using add_pos hα zero_lt_one) hx
  simp only [add_sub_cancel_right] at h
  rw [h]
  have hpow : (1 / (x : ℂ)) ^ (α + 1) = (x : ℂ) ^ (-1 - α) := by
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      exact ne_of_lt Real.pi_pos), ← Complex.cpow_neg]
    congr 1
    ring
  rw [hpow]
  dsimp [cosineFractionalKernel]
  ring

private lemma integral_exp_cosineDifference {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(t * x)) * (1 - Real.cos x)) =
      1 / (t * (1 + t ^ 2)) := by
  have he : IntegrableOn (fun x => Real.exp (-(t * x))) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 ht
  have hec : IntegrableOn (fun x => Real.exp (-(t * x)) * Real.cos x)
      (Ioi (0 : ℝ)) := by
    apply he.mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one x)
  calc
    _ = (∫ x in Ioi (0 : ℝ), Real.exp (-(t * x))) -
        ∫ x in Ioi (0 : ℝ), Real.exp (-(t * x)) * Real.cos x := by
      rw [← integral_sub he hec]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = 1 / t - t / (t ^ 2 + 1) := by
      rw [gammaSymbol_integral_Ioi_exp_neg_mul ht]
      simpa only [one_mul, one_pow] using
        congrArg (fun r => 1 / t - r) (gammaSymbol_integral_Ioi_exp_neg_mul_cos ht 1)
    _ = _ := by
      have ht2 : t ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
      field_simp
      ring

private lemma cosineLaplace_rational (α : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ), cosineLaplaceKernel α t x) =
      (t : ℂ) ^ (α - 1) / (1 + (t : ℂ) ^ 2) := by
  have hc (x : ℝ) : cosineLaplaceKernel α t x = (t : ℂ) ^ α *
      ((Real.exp (-(t * x)) * (1 - Real.cos x) : ℝ) : ℂ) := by
    simp only [cosineLaplaceKernel, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_exp, Complex.ofReal_neg]
    rw [mul_comm (x : ℂ) (t : ℂ)]
    ring
  simp_rw [hc]
  rw [integral_const_mul, integral_complex_ofReal, integral_exp_cosineDifference ht]
  push_cast
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Absolute Laplace interchange turns the cosine Mellin kernel into a beta kernel. -/
theorem Gamma_mul_integral_cosineFractionalKernel {α : ℂ}
    (hα0 : 0 < α.re) (hα2 : α.re < 2) :
    Complex.Gamma (α + 1) * (∫ x in Ioi (0 : ℝ), cosineFractionalKernel α x) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (α - 1) / (1 + (t : ℂ) ^ 2) := by
  rw [← integral_const_mul]
  calc
    _ = ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), cosineLaplaceKernel α t x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (cosineLaplace_euler hα0 hx).symm
    _ = ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), cosineLaplaceKernel α t x :=
      (integral_integral_swap (integrable_cosineLaplaceKernel hα0 hα2)).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact cosineLaplace_rational α ht

/-- The square-denominator Mellin integral on its full absolute strip. -/
theorem integral_cpow_div_one_add_square {α : ℂ}
    (hα0 : 0 < α.re) (hα2 : α.re < 2) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (α - 1) / (1 + (t : ℂ) ^ 2)) =
      (2 : ℂ)⁻¹ * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (α / 2))) := by
  have hb := integral_halfLine_beta (w := α / 2) (c := 1)
    (by simp only [Complex.div_ofNat_re]; linarith)
    (by simp only [Complex.div_ofNat_re, Complex.one_re]; linarith)
  have hm := mellin_comp_rpow (fun u : ℝ => (1 + (u : ℂ))⁻¹) α 2
  have hb' : mellin (fun u : ℝ => (1 + (u : ℂ))⁻¹) (α / 2) =
      Complex.Gamma (α / 2) * Complex.Gamma (1 - α / 2) := by
    simpa only [mellin, smul_eq_mul, Complex.cpow_neg_one, Complex.Gamma_one,
      div_one] using hb
  simp only [Complex.ofReal_ofNat] at hm
  rw [hb', Complex.Gamma_mul_Gamma_one_sub] at hm
  simpa only [mellin, smul_eq_mul, Real.rpow_two, Complex.ofReal_pow,
    div_eq_mul_inv, abs_of_pos (zero_lt_two : (0 : ℝ) < 2), real_smul,
    Complex.ofReal_inv, Complex.ofReal_ofNat] using hm

/-- Euler's cosine-difference integral, justified by absolute Fubini. -/
theorem integral_cosineFractionalKernel {α : ℂ}
    (hα0 : 0 < α.re) (hα2 : α.re < 2) :
    (∫ x in Ioi (0 : ℝ), cosineFractionalKernel α x) =
      (Real.pi : ℂ) /
        (2 * Complex.Gamma (α + 1) * Complex.sin ((Real.pi : ℂ) * (α / 2))) := by
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (s := α + 1) (by simpa using add_pos hα0 zero_lt_one)
  calc
    _ = (Complex.Gamma (α + 1) *
        (∫ x in Ioi (0 : ℝ), cosineFractionalKernel α x)) / Complex.Gamma (α + 1) :=
      (mul_div_cancel_left₀ _ hG).symm
    _ = _ := by
      rw [Gamma_mul_integral_cosineFractionalKernel hα0 hα2,
        integral_cpow_div_one_add_square hα0 hα2]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

end RHTower.WeilHigherDenominator
