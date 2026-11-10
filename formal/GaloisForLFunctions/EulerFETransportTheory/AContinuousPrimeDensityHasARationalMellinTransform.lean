import GaloisForLFunctions.EulerFETransportTheory.TheMellinTransformOfAContinuousEulerProduct
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-!
# A positive continuous prime-power perturbation

The pushforward of `x exp(-x) dx`, `x>0`, by the exponential map is
supported on `(1,∞)` and has Mellin transform `(s+1)⁻²`. Its positive
convolution exponential therefore has transform `exp((s+1)⁻²)`.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped ENNReal
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.EulerFETransportTheory

/-- A smooth positive measure in the logarithmic prime coordinate. -/
def continuousPrimeLogMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (x * Real.exp (-x)))

/-- A continuous prime-power measure on `(1,∞)`. -/
def continuousPrimeMeasure : Measure ℝ := continuousPrimeLogMeasure.map Real.exp

/-- No added mass lies at or below the unit. -/
theorem continuousPrimeMeasure_Iic_one : continuousPrimeMeasure (Iic 1) = 0 := by
  rw [continuousPrimeMeasure, Measure.map_apply Real.measurable_exp measurableSet_Iic]
  have he : Real.exp ⁻¹' Iic 1 = Iic 0 := by
    ext x
    simp only [mem_preimage, mem_Iic, Real.exp_le_one_iff]
  rw [he, continuousPrimeLogMeasure]
  apply withDensity_absolutelyContinuous _ _
  rw [Measure.restrict_apply measurableSet_Iic]
  have he : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
    exact fun hx => not_lt_of_ge hx
  rw [he, measure_empty]

private theorem exp_cpow_real (x : ℝ) (s : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ (-s) = Complex.exp ((x : ℂ) * (-s)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

private theorem continuousPrimeDensity_mellin_integrand (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (ENNReal.ofReal (x * Real.exp (-x))).toReal •
        (((Real.exp x : ℝ) : ℂ) ^ (-s)) =
      (x : ℂ) ^ 1 * Complex.exp (-((s + 1) * x)) := by
  rw [ENNReal.toReal_ofReal (mul_nonneg hx.le (Real.exp_pos _).le),
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_exp,
    exp_cpow_real, mul_assoc, ← Complex.exp_add, pow_one]
  congr 2
  push_cast
  ring

/-- The continuous measure has every absolute Mellin moment to the right of `-1`. -/
theorem integrable_mellin_continuousPrimeMeasure {s : ℂ} (hs : -1 < s.re) :
    Integrable (fun u : ℝ => (u : ℂ) ^ (-s)) continuousPrimeMeasure := by
  rw [continuousPrimeMeasure, integrable_map_measure
    (measurable_measureMellin s).aestronglyMeasurable Real.measurable_exp.aemeasurable]
  rw [continuousPrimeLogMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply (integrableOn_natPow_mul_cexp
    (show 0 < (s + 1).re by simp only [Complex.add_re, Complex.one_re]; linarith) 1).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (continuousPrimeDensity_mellin_integrand s hx).symm

/-- The Mellin transform of the added positive density. -/
theorem measureDirichlet_continuousPrimeMeasure {s : ℂ} (hs : -1 < s.re) :
    measureDirichlet continuousPrimeMeasure s = 1 / (s + 1) ^ 2 := by
  rw [measureDirichlet, continuousPrimeMeasure,
    integral_map Real.measurable_exp.aemeasurable (measurable_measureMellin s).aestronglyMeasurable,
    continuousPrimeLogMeasure, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hid : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      (ENNReal.ofReal (x * Real.exp (-x))).toReal •
          (((Real.exp x : ℝ) : ℂ) ^ (-s)) =
        (x : ℂ) ^ 1 * Complex.exp (-((s + 1) * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact continuousPrimeDensity_mellin_integrand s hx
  rw [integral_congr_ae hid, integral_Ioi_pow_mul_cexp
    (show 0 < (s + 1).re by simp only [Complex.add_re, Complex.one_re]; linarith)]
  simp only [Nat.factorial_one, Nat.cast_one]

/-- The absolute Mellin moment of the continuous prime measure is finite. -/
theorem integrable_rpow_continuousPrimeMeasure {σ : ℝ} (hσ : -1 < σ) :
    Integrable (fun u : ℝ => u ^ (-σ)) continuousPrimeMeasure := by
  have hi := (integrable_mellin_continuousPrimeMeasure
    (s := (σ : ℂ)) hσ).norm
  apply hi.congr
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero
    (measure_mono_null Iio_subset_Iic_self continuousPrimeMeasure_Iic_one)] with u hu
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hu),
    Complex.neg_re, Complex.ofReal_re]

#print axioms measureDirichlet_continuousPrimeMeasure

end GaloisForLFunctions.EulerFETransportTheory
