import GaloisForLFunctions.RHTower.LiClockCentralSineContourStability
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockVolterra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Weighted clock error preserves the actual positive margin

The sinh envelope is bounded by a linear function of the clock on every
fixed positive interval. Combining this with the literal actual source margin
preserves any fixed positive fraction uniformly down to arbitrarily small
positive clocks. The comparison needs only a complex error bound.
-/

open Complex Set Metric Filter Topology MeasureTheory
namespace RHTower
noncomputable section

private theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  have hb (y : ℝ) (hy : y ∈ Icc 0 x) : ‖Real.cosh y‖ ≤ Real.cosh x := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos y)]
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg hy.1, abs_of_nonneg hx] using hy.2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y (_hy : y ∈ Icc 0 x) => (Real.hasDerivAt_sinh y).hasDerivWithinAt)
    hb (convex_Icc 0 x) (show (0 : ℝ) ∈ Icc 0 x by exact ⟨le_rfl, hx⟩)
    (show x ∈ Icc 0 x by exact ⟨hx, le_rfl⟩)
  simpa only [Real.sinh_zero, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx), abs_of_nonneg hx, mul_comm] using h

/-- The exact odd-factorial envelope is linear in the clock uniformly down to zero. -/
theorem liClock_sinh_clock_le_linear {r L t : ℝ} (hr : 0 < r)
    (ht : 0 ≤ t) (htL : t ≤ L) :
    Real.sinh (t/r) ≤ (Real.cosh (L/r)/r)*t := by
  have htr : 0 ≤ t/r := div_nonneg ht hr.le
  have hLr : 0 ≤ L/r := div_nonneg (ht.trans htL) hr.le
  have hcosh : Real.cosh (t/r) ≤ Real.cosh (L/r) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg htr, abs_of_nonneg hLr] using
      div_le_div_of_nonneg_right htL hr.le
  calc
    _ ≤ (t/r)*Real.cosh (t/r) := sinh_le_mul_cosh htr
    _ ≤ (t/r)*Real.cosh (L/r) := mul_le_mul_of_nonneg_left hcosh htr
    _ = _ := by ring

/-- The already proved actual source margin on clocks up to twenty. -/
theorem liEvenCrossActualClockResponse_ge_positive_margin {t : ℝ}
    (ht : 0 ≤ t) (ht20 : t ≤ 20) :
    ((1051/2184 : ℝ)*xiShiftAbsoluteMass 0)*t ≤ liEvenCrossActualClockResponse t := by
  have hw : t^2/16 ≤ 25 := by nlinarith
  have hs := liEvenCrossActualCurrentClockSeries_ge_positive_margin
    (by positivity : 0 ≤ t^2/16) hw
  unfold liEvenCrossActualClockResponse
  nlinarith

/-- A weighted contour error preserves any fixed fraction of the actual positive margin. -/
theorem liClockApproximateResponse_ge_fraction_of_positive_margin
    {F : ℝ → ℂ} {r B θ : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (herror : ∀ t : ℝ, 0 ≤ t → t ≤ 20 →
      ‖F t - (liEvenCrossActualClockResponse t : ℂ)‖ ≤ B*Real.sinh (t/r))
    (hsmall : B*Real.cosh (20/r)/r ≤
      (1-θ)*((1051/2184 : ℝ)*xiShiftAbsoluteMass 0))
    {t : ℝ} (ht : 0 ≤ t) (ht20 : t ≤ 20) :
    θ*((1051/2184 : ℝ)*xiShiftAbsoluteMass 0)*t ≤ (F t).re := by
  have he := (herror t ht ht20).trans
    (mul_le_mul_of_nonneg_left (liClock_sinh_clock_le_linear hr ht ht20) hB)
  have hre : liEvenCrossActualClockResponse t - (F t).re ≤
      ‖F t - (liEvenCrossActualClockResponse t : ℂ)‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re, neg_sub] using
      (neg_le_abs (F t-(liEvenCrossActualClockResponse t : ℂ)).re).trans
        (Complex.abs_re_le_norm _)
  have hs := liEvenCrossActualClockResponse_ge_positive_margin ht ht20
  have hsmallt := mul_le_mul_of_nonneg_right hsmall ht
  have halgebra : B*((Real.cosh (20/r)/r)*t) = (B*Real.cosh (20/r)/r)*t := by ring
  rw [halgebra] at he
  nlinarith


/-- Strict positivity follows from any positive preserved fraction of the actual source margin. -/
theorem liClockApproximateResponse_pos_of_small_weighted_error
    {F : ℝ → ℂ} {r B θ : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hθ : 0 < θ)
    (herror : ∀ t : ℝ, 0 ≤ t → t ≤ 20 →
      ‖F t - (liEvenCrossActualClockResponse t : ℂ)‖ ≤ B*Real.sinh (t/r))
    (hsmall : B*Real.cosh (20/r)/r ≤
      (1-θ)*((1051/2184 : ℝ)*xiShiftAbsoluteMass 0))
    {t : ℝ} (ht : 0 < t) (ht20 : t ≤ 20) : 0 < (F t).re := by
  apply lt_of_lt_of_le _
    (liClockApproximateResponse_ge_fraction_of_positive_margin hr hB herror hsmall ht.le ht20)
  exact mul_pos (mul_pos hθ (mul_pos (by norm_num) (xiShiftAbsoluteMass_pos 0))) ht

end
end RHTower
