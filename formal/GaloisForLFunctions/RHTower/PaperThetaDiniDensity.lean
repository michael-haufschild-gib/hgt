import GaloisForLFunctions.RHTower.PaperThetaLocalRegularity

/-! # Paid local Dirichlet cancellation for the actual theta family

Local differentiability cancels the sine denominator. Away from zero, the
same quotient is controlled by the original L¹ mode on a full period.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

def diniDifference (z : ℂ) (t y : ℝ) : ℂ :=
  (periodicMode z (t-y) - periodicMode z t) / (Real.sin (Real.pi*y) : ℂ)

theorem measurable_diniDifference (z : ℂ) (t : ℝ) : Measurable (diniDifference z t) := by
  exact (((measurable_periodicMode z).comp (measurable_const.sub measurable_id)).sub
    measurable_const).div
    (Complex.continuous_ofReal.measurable.comp ((measurable_const.mul measurable_id).sin))

private theorem centered_sine_lower {y : ℝ} (hy : y ∈ Period.centerWin) :
    Real.pi * |y| / 2 ≤ |Real.sin (Real.pi*y)| := by
  have h : |Real.pi*y| ≤ Real.pi/2 := by
    rw [abs_le]
    constructor <;> nlinarith [hy.1, hy.2, Real.pi_pos]
  simpa only [abs_mul, abs_of_pos Real.pi_pos] using Period.sin_posabs h

/-- One integrable majorant controls the actual quotient on the entire centered period. -/
theorem exists_diniDifference_bound (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ y ∈ Period.centerWin,
      ‖diniDifference z t.val y‖ ≤
        A + B * (‖periodicMode z (t.val-y)‖ + ‖periodicMode z t.val‖) := by
  obtain ⟨K, δ, hK, hδ, hb⟩ := periodicMode_local_difference_bound z t
  refine ⟨2*K/Real.pi, 2/(Real.pi*δ), by positivity, by positivity, fun y hy => ?_⟩
  by_cases hy0 : y = 0
  · subst y
    simp only [diniDifference, sub_zero, sub_self, zero_div, norm_zero]
    positivity
  have hys : 0 < |y| := abs_pos.mpr hy0
  have hs := centered_sine_lower hy
  have hspos : 0 < |Real.sin (Real.pi*y)| := lt_of_lt_of_le (by positivity) hs
  rw [diniDifference, norm_div, Complex.norm_real, Real.norm_eq_abs]
  by_cases hn : |y| < δ
  · have hlocal : ‖periodicMode z (t.val-y) - periodicMode z t.val‖ /
        |Real.sin (Real.pi*y)| ≤ 2*K/Real.pi := by
      calc
        _ ≤ (K*|y|)/(Real.pi*|y|/2) :=
          div_le_div₀ (by positivity) (hb y hn) (by positivity) hs
        _ = _ := by field_simp
    exact hlocal.trans (le_add_of_nonneg_right (by positivity))
  · have hden : Real.pi*δ/2 ≤ |Real.sin (Real.pi*y)| :=
      (by nlinarith [le_of_not_gt hn, Real.pi_pos] : Real.pi*δ/2 ≤ Real.pi*|y|/2).trans hs
    have hfar : ‖periodicMode z (t.val-y) - periodicMode z t.val‖ /
        |Real.sin (Real.pi*y)| ≤
          (2/(Real.pi*δ)) * (‖periodicMode z (t.val-y)‖ + ‖periodicMode z t.val‖) := by
      calc
        _ ≤ (‖periodicMode z (t.val-y)‖ + ‖periodicMode z t.val‖)/(Real.pi*δ/2) :=
          div_le_div₀ (by positivity) (norm_sub_le _ _) (by positivity) hden
        _ = _ := by ring
    exact hfar.trans (le_add_of_nonneg_left (by positivity))

/-- The local difference quotient retains the paper's exact Dirichlet sine identity. -/
theorem diniDifference_dirichlet (z : ℂ) (t : ℝ) (N : ℕ) (y : Period.centerWin) :
    (periodicMode z (t-y.val) - periodicMode z t) * Period.dirichlet N y.val =
      diniDifference z t y.val * (Real.sin (Period.ang N y.val + Real.pi*y.val) : ℂ) := by
  by_cases hy : y.val = 0
  · simp [hy, diniDifference]
  have hs : Real.sin (Real.pi*y.val) ≠ 0 := by
    have h := centered_sine_lower y.property
    have hp : 0 < Real.pi * |y.val| / 2 := by positivity
    exact abs_pos.mp (hp.trans_le h)
  have hsC : (Real.sin (Real.pi*y.val) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [diniDifference, ← Period.dirichlet_sin N y.val]
  rw [div_mul_eq_mul_div, ← mul_assoc, mul_div_cancel_right₀ _ hsC]

/-- No integrability premise remains: the entire quotient is paid on the exact L¹ domain. -/
theorem integrable_diniDifference (z : L1Point) (t : Ioo (0 : ℝ) 1) :
    IntegrableOn (diniDifference z.val t.val) Period.centerWin := by
  letI : IsFiniteMeasure (volume.restrict Period.centerWin) :=
    show IsFiniteMeasure (volume.restrict (Ico (-1/2 : ℝ) (1/2))) from inferInstance
  obtain ⟨A, B, _, _, hb⟩ := exists_diniDifference_bound z.val t
  have h := (integrable_const A).add
    (((integrable_centered_periodicMode z t.val).norm.add
      (integrable_const ‖periodicMode z.val t.val‖)).const_mul B)
  apply h.mono' (measurable_diniDifference z.val t.val).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ico] with y hy
  exact hb y hy

end RHTower.PaperThetaEndpoint
