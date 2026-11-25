import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.JumpLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Conditioning.LimitMoments

/-! # Exponential moments and mean of the added prime energy -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace

/-- Exponential transforms factor under convolution by Fubini and additivity of energy. -/
private theorem complexMGF_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (z : ℂ) :
    complexMGF id (μ ∗ ν) z = complexMGF id μ z*complexMGF id ν z := by
  let e := fun x : ℝ => Complex.exp (z*(x:ℂ))
  change (∫ x, e x ∂(μ ∗ ν)) = (∫ x, e x ∂μ)*(∫ x, e x ∂ν)
  rw [Measure.conv,integral_map (by fun_prop) (by dsimp [e]; fun_prop),← integral_prod_mul e e]
  exact integral_congr_ae (ae_of_all _ fun p => by simp [e,Complex.ofReal_add,mul_add,Complex.exp_add])

/-- The complex transform of the limiting band measure, at every probe. -/
theorem increment_mgf {c d : ℝ} (hc : 0 < c) (hcd : c < d) (z : ℂ) :
    complexMGF id (increment c d hc hcd : Measure ℝ) z = Complex.exp (bandExponent c d z) := by
  have H := congrFun (complexMGF_cutoffLaw (hc.trans hcd)) z
  rw [cutoff_convolution hc hcd,complexMGF_conv,complexMGF_cutoffLaw hc,factor_transform hc hcd.le] at H
  exact mul_left_cancel₀ (transform_ne_zero c z) H

theorem increment_exp_integrable {c d : ℝ} (hc : 0 < c) (hcd : c < d) (r : ℝ) :
    Integrable (fun x : ℝ => Real.exp (r*x)) (increment c d hc hcd : Measure ℝ) := by
  apply Integrable.of_integral_ne_zero
  have H := increment_mgf hc hcd (r:ℂ)
  rw [complexMGF_ofReal] at H
  intro hzero
  change (∫ x : ℝ, Real.exp (r*x) ∂(increment c d hc hcd : Measure ℝ) : ℝ) = 0 at hzero
  change ((∫ x : ℝ, Real.exp (r*x) ∂(increment c d hc hcd : Measure ℝ) : ℝ):ℂ) = _ at H
  rw [hzero,Complex.ofReal_zero] at H
  exact Complex.exp_ne_zero _ H.symm

private theorem cutoff_integrable {c : ℝ} (hc : 0 < c) : Integrable id (cutoffLaw c : Measure ℝ) := by
  apply Integrable.of_integral_ne_zero
  change (∫ x : ℝ, x ∂(cutoffLaw c : Measure ℝ)) ≠ 0
  rw [cutoffLaw_mean hc]
  exact (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))).ne'

/-- Mean energy supplied by the additional modes, measured in the pole scaling. -/
theorem increment_mean {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    (∫ x : ℝ, x ∂(increment c d hc hcd : Measure ℝ)) = Real.exp (-c)-Real.exp (-d) := by
  let μ : Measure ℝ := cutoffLaw c
  let ν : Measure ℝ := increment c d hc hcd
  letI : IsProbabilityMeasure μ := (cutoffLaw c).property
  letI : IsProbabilityMeasure ν := (increment c d hc hcd).property
  have hE : (cutoffLaw d : Measure ℝ) = (μ.prod ν).map (fun p : ℝ × ℝ => p.1+p.2) := cutoff_convolution hc hcd
  have hT := cutoff_integrable (hc.trans hcd)
  rw [hE] at hT
  have hsum : Integrable (fun p : ℝ × ℝ => p.1+p.2) (μ.prod ν) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable (by fun_prop)).mp hT
  have hlow : Integrable (fun p : ℝ × ℝ => p.1) (μ.prod ν) := (cutoff_integrable hc).comp_fst ν
  have hband : Integrable (fun p : ℝ × ℝ => p.2) (μ.prod ν) := by
    have H := hsum.sub hlow
    change Integrable (fun p : ℝ × ℝ => p.1+p.2-p.1) (μ.prod ν) at H
    simpa only [add_sub_cancel_left] using H
  have H := cutoffLaw_mean (hc.trans hcd)
  rw [hE,integral_map (f := fun x : ℝ => x) (by fun_prop) (by fun_prop)] at H
  change (∫ p : ℝ × ℝ, p.1+p.2 ∂μ.prod ν) = _ at H
  have hfirst : (∫ p : ℝ × ℝ, p.1 ∂μ.prod ν) = ∫ x, x ∂μ := by
    simpa only [probReal_univ,one_smul] using integral_fun_fst (μ := μ) (ν := ν) (fun x : ℝ => x)
  have hsecond : (∫ p : ℝ × ℝ, p.2 ∂μ.prod ν) = ∫ x, x ∂ν := by
    simpa only [probReal_univ,one_smul] using integral_fun_snd (μ := μ) (ν := ν) (fun x : ℝ => x)
  rw [integral_add hlow hband,hfirst,hsecond] at H
  change (∫ x : ℝ, x ∂(cutoffLaw c : Measure ℝ))+(∫ x : ℝ, x ∂ν) = _ at H
  rw [cutoffLaw_mean hc] at H
  change (∫ x : ℝ, x ∂ν) = _
  linarith only [H]

#print axioms increment_mgf
#print axioms increment_exp_integrable
#print axioms increment_mean

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands
