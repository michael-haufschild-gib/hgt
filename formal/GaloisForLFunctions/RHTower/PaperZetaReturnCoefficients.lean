import GaloisForLFunctions.RHTower.PaperZetaReturnProfile

/-! # The zero mode controls every deterministic return coefficient

For every positive real window length, the zero Fourier coefficient is exactly
the physical return density. All modes are bounded by that same quantity.
-/

namespace RHTower
noncomputable section
open Set MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry

def paperZetaReturnDensity (D : PaperZetaReturnDisc) (ε T : ℝ) : ℝ :=
  volume.real (paperZetaReturnTimes D ε ∩ Icc 0 T) / T

def paperZetaReturnCoeff (D : PaperZetaReturnDisc) (ε T : ℝ) (k : ℤ) : ℂ :=
  l2Pair (fourierChar k) (paperZetaReturnProfile D ε T)

theorem paperZetaReturnTimes_window_ne_top (D : PaperZetaReturnDisc) (ε T : ℝ) :
    volume (paperZetaReturnTimes D ε ∩ Icc 0 T) ≠ ⊤ := by
  rw [← Measure.restrict_apply (paperZetaReturnTimes_measurable D ε)]
  exact measure_ne_top _ _

theorem paperZetaReturnDensity_nonneg (D : PaperZetaReturnDisc) (ε : ℝ)
    (T : {t : ℝ // 0 < t}) : 0 ≤ paperZetaReturnDensity D ε T :=
  div_nonneg ENNReal.toReal_nonneg T.property.le

theorem paperZetaReturnProfile_integral_norm (D : PaperZetaReturnDisc) (ε : ℝ)
    (T : {t : ℝ // 0 < t}) :
    (∫ x in (0 : ℝ)..1, ‖paperZetaReturnProfile D ε T x‖) =
      paperZetaReturnDensity D ε T := by
  classical
  have he : (fun x => ‖paperZetaReturnProfile D ε T x‖) =
      fun x => (paperZetaReturnTimes D ε).indicator (fun _ => (1 : ℝ)) (T.val * x) := by
    funext x
    by_cases h : T.val * x ∈ paperZetaReturnTimes D ε <;>
      simp [paperZetaReturnProfile, h]
  rw [he, intervalIntegral.integral_comp_mul_left _ (ne_of_gt T.property), mul_zero, mul_one,
    intervalIntegral.integral_of_le T.property.le, restrict_Ioc_eq_restrict_Icc,
    integral_indicator_const _ (paperZetaReturnTimes_measurable D ε)]
  simp [paperZetaReturnDensity, Measure.real,
    Measure.restrict_apply (paperZetaReturnTimes_measurable D ε), div_eq_mul_inv, mul_comm]

theorem paperZetaReturnCoeff_zero (D : PaperZetaReturnDisc) (ε : ℝ)
    (T : {t : ℝ // 0 < t}) :
    paperZetaReturnCoeff D ε T 0 = (paperZetaReturnDensity D ε T : ℂ) := by
  classical
  have he : paperZetaReturnProfile D ε T =
      fun x => (‖paperZetaReturnProfile D ε T x‖ : ℂ) := by
    funext x
    by_cases h : T.val * x ∈ paperZetaReturnTimes D ε <;>
      simp [paperZetaReturnProfile, h]
  simp only [paperZetaReturnCoeff, l2Pair, fourierChar, Int.cast_zero, mul_zero,
    zero_mul, Complex.exp_zero, map_one, one_mul]
  rw [he, intervalIntegral.integral_ofReal, paperZetaReturnProfile_integral_norm]

/-- Uniform in the frequency, even when it is chosen after the window. -/
theorem paperZetaReturnCoeff_norm_le_density (D : PaperZetaReturnDisc) (ε : ℝ)
    (T : {t : ℝ // 0 < t}) (k : ℤ) :
    ‖paperZetaReturnCoeff D ε T k‖ ≤ paperZetaReturnDensity D ε T := by
  have hk (x : ℝ) : ‖fourierChar k x‖ = 1 := by
    simp [fourierChar, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  calc
    ‖paperZetaReturnCoeff D ε T k‖ ≤
        ∫ x in (0 : ℝ)..1, ‖(starRingEnd ℂ) (fourierChar k x) *
          paperZetaReturnProfile D ε T x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = paperZetaReturnDensity D ε T := by
      simpa only [norm_mul, Complex.norm_conj, hk, one_mul] using
        paperZetaReturnProfile_integral_norm D ε T

theorem paperZetaReturnCoeff_zero_norm (D : PaperZetaReturnDisc) (ε : ℝ)
    (T : {t : ℝ // 0 < t}) :
    ‖paperZetaReturnCoeff D ε T 0‖ = paperZetaReturnDensity D ε T := by
  rw [paperZetaReturnCoeff_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperZetaReturnDensity_nonneg D ε T)]

theorem paperZetaReturnCoeff_norm_le_zero (D : PaperZetaReturnDisc) (ε : ℝ)
    (T : {t : ℝ // 0 < t}) (k : ℤ) :
    ‖paperZetaReturnCoeff D ε T k‖ ≤ ‖paperZetaReturnCoeff D ε T 0‖ := by
  rw [paperZetaReturnCoeff_zero_norm]
  exact paperZetaReturnCoeff_norm_le_density D ε T k

end
end RHTower
