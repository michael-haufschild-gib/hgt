import GaloisForLFunctions.HTGeometry.ShiftedCircleLogKernel
import GaloisForLFunctions.HTGeometry.PoissonBoundaryPositivity
import GaloisForLFunctions.Bottcher.HarmonicComp

/-!
# Harnack comparison for shifted Green kernels

For a divisor point outside a shifted disc, its outer-disc Green kernel is positive harmonic on
that disc.  Harnack therefore compares its shifted-circle mean with its value at the origin, which
is the logarithmic counting weight `log (R / ‖u‖)`.
-/

open Complex Metric Real Set Topology InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Outer-disc Green kernel associated with `u`. -/
def outerDiscGreenKernel (u : ℂ) (R : ℝ) (w : ℂ) : ℝ :=
  Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ - Real.log ‖w - u‖

/-- Away from its divisor point, the outer-disc Green kernel is harmonic. -/
theorem harmonicAt_outerDiscGreenKernel {u w : ℂ} {R : ℝ}
    (hR : 0 < R) (hu : u ∈ closedBall (0 : ℂ) R)
    (hw : w ∈ ball (0 : ℂ) R) (hwu : w ≠ u) :
    HarmonicAt (outerDiscGreenKernel u R) w := by
  have hnum : AnalyticAt ℂ (PoissonJensen.innerLogKernel 0 u R) w := by
    unfold PoissonJensen.innerLogKernel
    apply AnalyticAt.div
    · exact analyticAt_const.sub
        (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
    · exact analyticAt_const
    · exact Complex.ofReal_ne_zero.mpr hR.ne'
  have hden : AnalyticAt ℂ (fun z : ℂ ↦ z - u) w :=
    analyticAt_id.sub analyticAt_const
  have hnumne : PoissonJensen.innerLogKernel 0 u R w ≠ 0 := by
    apply PoissonJensen.innerLogKernel_ne_zero hR
    have huR : ‖u‖ ≤ R := by simpa [mem_closedBall_iff_norm] using hu
    have hwR : ‖w‖ < R := by simpa [mem_ball_zero_iff] using hw
    have : ‖u‖ * ‖w‖ < R ^ (2 : ℕ) := by
      calc
        ‖u‖ * ‖w‖ ≤ R * ‖w‖ :=
          mul_le_mul_of_nonneg_right huR (norm_nonneg w)
        _ < R * R := mul_lt_mul_of_pos_left hwR hR
        _ = R ^ (2 : ℕ) := by ring
    simpa using this
  change HarmonicAt
    (fun z ↦ Real.log ‖PoissonJensen.innerLogKernel 0 u R z‖ - Real.log ‖z - u‖) w
  have hsub := (hnum.harmonicAt_log_norm hnumne).sub
    (hden.harmonicAt_log_norm (sub_ne_zero.mpr hwu))
  apply (harmonicAt_congr_nhds ?_).mp hsub
  exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- On the outer disc and away from the divisor, the Green kernel is nonnegative. -/
theorem outerDiscGreenKernel_nonneg {u w : ℂ} {R : ℝ}
    (hR : 0 < R) (hu : u ∈ closedBall (0 : ℂ) R)
    (hw : w ∈ closedBall (0 : ℂ) R) (hwu : w ≠ u) :
    0 ≤ outerDiscGreenKernel u R w := by
  unfold outerDiscGreenKernel
  exact sub_nonneg.mpr (log_norm_sub_le_log_norm_innerLogKernel hR hu hw hwu)

/-- Outer-disc Green kernels are circle-integrable on every circle. -/
theorem circleIntegrable_outerDiscGreenKernel (u c : ℂ) {R r : ℝ} (hR : 0 < R) :
    CircleIntegrable (outerDiscGreenKernel u R) c r := by
  change CircleIntegrable
    ((fun w ↦ Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖) -
      fun w ↦ Real.log ‖w - u‖) c r
  apply CircleIntegrable.sub
  · apply MeromorphicOn.circleIntegrable_log_norm
    intro w _
    apply AnalyticAt.meromorphicAt
    unfold PoissonJensen.innerLogKernel
    apply AnalyticAt.div
    · exact analyticAt_const.sub
        (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
    · exact analyticAt_const
    · exact Complex.ofReal_ne_zero.mpr hR.ne'
  · exact ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn).circleIntegrable_log_norm

/-- The Green kernel at the origin is the standard logarithmic counting weight. -/
theorem outerDiscGreenKernel_zero {u : ℂ} {R : ℝ}
    (hR : 0 < R) (hu : u ≠ 0) :
    outerDiscGreenKernel u R 0 = Real.log (R / ‖u‖) := by
  simp only [outerDiscGreenKernel, PoissonJensen.innerLogKernel, sub_zero, mul_zero,
    zero_sub, norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have huNorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [Real.log_div hR.ne' huNorm]
  congr 1
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
  field_simp [hR.ne']

/-- Harnack comparison of a shifted Green-kernel circle mean with its origin counting weight. -/
theorem circleAverage_outerDiscGreenKernel_le_origin
    {u c : ℂ} {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hc : ‖c‖ < r)
    (hu : u ∈ closedBall (0 : ℂ) R)
    (houter : u ∉ closedBall c r)
    (hinner : ‖c‖ + r < R) :
    Real.circleAverage (outerDiscGreenKernel u R) c r ≤
      (r + ‖c‖) / (r - ‖c‖) * Real.log (R / ‖u‖) := by
  let v : ℂ := -((r : ℂ)⁻¹ * c)
  let h : ℂ → ℝ := fun z ↦ outerDiscGreenKernel u R (c + (r : ℂ) * z)
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hzeroMap : c + (r : ℂ) * v = 0 := by
    dsimp [v]
    field_simp
    ring
  have hvnorm : ‖v‖ = ‖c‖ / r := by
    dsimp [v]
    rw [norm_neg, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    exact inv_mul_eq_div r ‖c‖
  have hv : v ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hvnorm, div_lt_one hr]
    exact hc
  have hmap : ∀ z ∈ ball (0 : ℂ) 1,
      c + (r : ℂ) * z ∈ ball (0 : ℂ) R := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    calc
      ‖c + (r : ℂ) * z‖ ≤ ‖c‖ + ‖(r : ℂ) * z‖ := norm_add_le _ _
      _ = ‖c‖ + r * ‖z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
      _ < ‖c‖ + r := by nlinarith [norm_nonneg z]
      _ < R := hinner
  have havoid : ∀ z ∈ ball (0 : ℂ) 1, c + (r : ℂ) * z ≠ u := by
    intro z hz hzu
    apply houter
    rw [← hzu, mem_closedBall_iff_norm]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    have hz' : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
    nlinarith [norm_nonneg z]
  have hharm : HarmonicOnNhd h (ball (0 : ℂ) 1) := by
    intro z hz
    have hbase := harmonicAt_outerDiscGreenKernel hR hu (hmap z hz) (havoid z hz)
    have haffine : AnalyticAt ℂ (fun w : ℂ ↦ c + (r : ℂ) * w) z := by fun_prop
    change HarmonicAt (fun w ↦ outerDiscGreenKernel u R (c + (r : ℂ) * w)) z
    have hcomp := HarmonicAt.comp_analytic
      (g := outerDiscGreenKernel u R) (f := fun w : ℂ ↦ c + (r : ℂ) * w)
      hbase haffine
    apply (harmonicAt_congr_nhds ?_).mp hcomp
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hnonneg : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ h z := by
    intro z hz
    exact outerDiscGreenKernel_nonneg hR hu
      (Metric.ball_subset_closedBall (hmap z hz)) (havoid z hz)
  have hh := (harnack hharm hnonneg hv).1
  have hfactorPos : 0 < (1 - ‖v‖) / (1 + ‖v‖) := by
    have hvlt : ‖v‖ < 1 := by simpa [mem_ball_zero_iff] using hv
    positivity
  have hcenter : h 0 ≤ (1 + ‖v‖) / (1 - ‖v‖) * h v := by
    calc
      h 0 ≤ h v / ((1 - ‖v‖) / (1 + ‖v‖)) :=
        (le_div_iff₀ hfactorPos).2 (by simpa [mul_comm] using hh)
      _ = (1 + ‖v‖) / (1 - ‖v‖) * h v := by
        have hvlt : ‖v‖ < 1 := by simpa [mem_ball_zero_iff] using hv
        field_simp
  have hu0 : u ≠ 0 := by
    intro hu0
    subst u
    apply houter
    rw [mem_closedBall_iff_norm]
    simpa [norm_neg] using hc.le
  have havg : Real.circleAverage (outerDiscGreenKernel u R) c r = h 0 := by
    have hinnerAvg := circleAverage_log_norm_innerLogKernel hR hr hu hinner
    have hdistAvg : Real.circleAverage (fun w ↦ Real.log ‖w - u‖) c r =
        Real.log ‖c - u‖ := by
      have hanalytic : AnalyticOnNhd ℂ (fun w : ℂ ↦ w - u)
          (closedBall c |r|) := analyticOnNhd_id.sub analyticOnNhd_const
      have hfree : ∀ w ∈ closedBall c |r|, w - u ≠ 0 := by
        intro w hw hwu
        apply houter
        have hwu' : w = u := sub_eq_zero.mp hwu
        simpa [abs_of_pos hr, hwu'] using hw
      exact hanalytic.circleAverage_log_norm_of_ne_zero hfree
    change Real.circleAverage
        ((fun w ↦ Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖) -
          fun w ↦ Real.log ‖w - u‖) c r = _
    have hnumInt : CircleIntegrable
        (fun w ↦ Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖) c r := by
      apply MeromorphicOn.circleIntegrable_log_norm
      intro w _
      apply AnalyticAt.meromorphicAt
      unfold PoissonJensen.innerLogKernel
      fun_prop
    have hdenInt : CircleIntegrable (fun w ↦ Real.log ‖w - u‖) c r :=
      ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn).circleIntegrable_log_norm
    rw [Real.circleAverage_sub hnumInt hdenInt, hinnerAvg, hdistAvg]
    simp [h, outerDiscGreenKernel]
  rw [havg]
  calc
    h 0 ≤ (1 + ‖v‖) / (1 - ‖v‖) * h v := hcenter
    _ = (r + ‖c‖) / (r - ‖c‖) * Real.log (R / ‖u‖) := by
      rw [show h v = outerDiscGreenKernel u R 0 by simp [h, hzeroMap],
        outerDiscGreenKernel_zero hR hu0, hvnorm]
      field_simp [hr.ne']

end

end GaloisForLFunctions.HTGeometry
