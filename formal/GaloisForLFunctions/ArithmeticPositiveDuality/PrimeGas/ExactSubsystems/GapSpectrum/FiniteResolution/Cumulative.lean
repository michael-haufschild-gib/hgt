import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Continuum.Collision
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.CDF

/-! # Distribution functions for the observed gap and its Laplace limit -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Set MeasureTheory Filter Topology
open scoped ENNReal

def gapCDF (h : Ioi (0:ℝ)) (t : ℝ) := (criticalGapLaw h : Measure ℝ).real (Iic t)
def laplaceCDF (t : ℝ) := (_root_.RHTower.mobiusCriticalLaplaceGapProbabilityMeasure : Measure ℝ).real (Iic t)

/-- The half-open band convention records atoms at the upper endpoint. -/
theorem real_band_eq_cdf_sub (P : ProbabilityMeasure ℝ) {a b : ℝ} (hab : a ≤ b) :
    (P:Measure ℝ).real (Ioc a b) = (P:Measure ℝ).real (Iic b) - (P:Measure ℝ).real (Iic a) := by
  have hu : Iic a ∪ Ioc a b = Iic b := by
    ext y
    change y ≤ a ∨ a < y ∧ y ≤ b ↔ y ≤ b
    constructor
    · exact fun h => h.elim (fun ha => ha.trans hab) (fun ha => ha.2)
    · intro hy
      exact (le_or_gt y a).imp_right (fun ha => ⟨ha,hy⟩)
  have hd : Disjoint (Iic a) (Ioc a b) := Set.disjoint_left.mpr (fun _ hx hy => hy.1.not_ge hx)
  have H := measureReal_union (μ := (P:Measure ℝ)) hd measurableSet_Ioc
  rw [hu] at H
  linarith only [H]

theorem gapCDF_atTop (h : Ioi (0:ℝ)) : Tendsto (gapCDF h) atTop (𝓝 1) := by
  have H := ProbabilityTheory.tendsto_cdf_atTop (criticalGapLaw h : Measure ℝ)
  apply H.congr
  exact fun t => ProbabilityTheory.cdf_eq_real _ t

private theorem laplace_band_integral (S : Set ℝ) (hs : MeasurableSet S) :
    (_root_.RHTower.mobiusCriticalLaplaceGapProbabilityMeasure : Measure ℝ).real S =
      ∫ y in S, _root_.RHTower.mobiusCriticalLaplaceGapDensity y := by
  change ((volume.withDensity (fun y => (_root_.RHTower.mobiusCriticalLaplaceGapDensityNNReal y : ℝ≥0∞))) S).toReal = _
  rw [withDensity_apply _ hs]
  have hc : (fun y => (_root_.RHTower.mobiusCriticalLaplaceGapDensityNNReal y : ℝ≥0∞)) =
      fun y => ENNReal.ofReal (_root_.RHTower.mobiusCriticalLaplaceGapDensity y) := by
    funext y
    exact (ENNReal.ofReal_eq_coe_nnreal (_root_.RHTower.mobiusCriticalLaplaceGapDensity_nonneg y)).symm
  rw [hc,← ofReal_integral_eq_lintegral_ofReal _root_.RHTower.integrable_mobiusCriticalLaplaceGapDensity.integrableOn
    (Eventually.of_forall _root_.RHTower.mobiusCriticalLaplaceGapDensity_nonneg),
    ENNReal.toReal_ofReal (integral_nonneg _root_.RHTower.mobiusCriticalLaplaceGapDensity_nonneg)]

theorem laplaceCDF_primitive (t : ℝ) :
    laplaceCDF t = 1/2 + ∫ y in (0:ℝ)..t, _root_.RHTower.mobiusCriticalLaplaceGapDensity y := by
  have hi {a b : ℝ} (hab : a ≤ b) : (∫ y in a..b, _root_.RHTower.mobiusCriticalLaplaceGapDensity y) =
      laplaceCDF b - laplaceCDF a := by
    rw [intervalIntegral.integral_of_le hab,← laplace_band_integral _ measurableSet_Ioc]
    exact real_band_eq_cdf_sub _ hab
  have h0 : laplaceCDF 0 = 1/2 := laplace_cumulative_zero
  rcases le_total 0 t with ht | ht
  · rw [hi ht,h0]
    ring
  · rw [intervalIntegral.integral_symm,hi ht,h0]
    ring

theorem laplaceCDF_positive {t : ℝ} (ht : 0 ≤ t) : laplaceCDF t = 1-Real.exp (-t)/2 := by
  rw [laplaceCDF_primitive]
  have hf : (∫ y in (0:ℝ)..t, _root_.RHTower.mobiusCriticalLaplaceGapDensity y) =
      ∫ y in (0:ℝ)..t, (1/2:ℝ)*Real.exp (-y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le ht] at hy
    simp only [_root_.RHTower.mobiusCriticalLaplaceGapDensity,abs_of_nonneg hy.1]
  rw [hf,intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg Real.exp,integral_exp,neg_zero,Real.exp_zero]
  ring

theorem laplaceCDF_negative {t : ℝ} (ht : t ≤ 0) : laplaceCDF t = Real.exp t/2 := by
  rw [laplaceCDF_primitive]
  have hf : (∫ y in (0:ℝ)..t, _root_.RHTower.mobiusCriticalLaplaceGapDensity y) =
      ∫ y in (0:ℝ)..t, (1/2:ℝ)*Real.exp y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_ge ht] at hy
    simp only [_root_.RHTower.mobiusCriticalLaplaceGapDensity,abs_of_nonpos hy.2,neg_neg]
  rw [hf,intervalIntegral.integral_const_mul,integral_exp,Real.exp_zero]
  ring

theorem laplaceCDF_derivative (t : ℝ) :
    HasDerivAt laplaceCDF (_root_.RHTower.mobiusCriticalLaplaceGapDensity t) t := by
  rw [funext laplaceCDF_primitive]
  exact (_root_.RHTower.continuous_mobiusCriticalLaplaceGapDensity.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _

#print axioms real_band_eq_cdf_sub
#print axioms gapCDF_atTop
#print axioms laplaceCDF_primitive
#print axioms laplaceCDF_positive
#print axioms laplaceCDF_negative
#print axioms laplaceCDF_derivative

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
