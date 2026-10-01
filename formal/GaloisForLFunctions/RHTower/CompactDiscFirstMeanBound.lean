import Mathlib.Analysis.Complex.MeanValue

open Complex MeasureTheory Metric Set Real
noncomputable section
namespace RHTower

/-- The norm of a circle average is bounded by the average of the norm. -/
theorem norm_circleAverage_le_average_norm (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    ‖circleAverage f c R‖ ≤ circleAverage (fun z => ‖f z‖) c R := by
  simp only [circleAverage, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr Real.two_pi_pos), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le)
    (inv_nonneg.mpr Real.two_pi_pos.le)

/-- One boundary first absolute mean controls every value on the smaller disc,
with the exact radius-gap loss. -/
theorem norm_le_circleAverage_norm_of_differentiableOn
    {f : ℂ → ℂ} {c z : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hz : z ∈ closedBall c r) :
    ‖f z‖ ≤ (R / (R - r)) * circleAverage (fun w => ‖f w‖) c R := by
  have hR : 0 < R := hr.trans_lt hrR
  have hgap : 0 < R - r := sub_pos.mpr hrR
  have hdist (w : ℂ) (hw : w ∈ sphere c R) : R - r ≤ ‖w - z‖ := by
    have hw' : dist w c = R := hw
    have hz' : dist z c ≤ r := hz
    have htri := dist_triangle w z c
    rw [hw', dist_eq_norm] at htri
    linarith
  have hne (w : ℂ) (hw : w ∈ sphere c R) : w - z ≠ 0 :=
    norm_pos_iff.mp (hgap.trans_le (hdist w hw))
  have hkernel (w : ℂ) (hw : w ∈ sphere c R) : ‖(w - c) / (w - z)‖ ≤ R / (R - r) := by
    have hw' : ‖w - c‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hw
    rw [norm_div, hw']
    exact div_le_div_of_nonneg_left hR.le hgap (hdist w hw)
  have hfcont : ContinuousOn f (sphere c R) := hf.continuousOn.mono sphere_subset_closedBall
  have hgcont : ContinuousOn (fun w => ((w - c) / (w - z)) • f w) (sphere c R) :=
    ((continuousOn_id.sub continuousOn_const).div (continuousOn_id.sub continuousOn_const) hne).smul hfcont
  have hdc : DiffContOnCl ℂ f (ball c R) := by
    refine ⟨hf.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball c hR.ne']
    exact hf.continuousOn
  have hzR : z ∈ ball c R := closedBall_subset_ball hrR hz
  have hrep : circleAverage (fun w => ((w - c) / (w - z)) • f w) c R = f z :=
    DiffContOnCl.circleAverage_smul_div (f := f) (c := c) (R := R) (w := z) (by simpa only [abs_of_pos hR] using hdc)
      (by simpa only [abs_of_pos hR] using hzR)
  calc
    ‖f z‖ = ‖circleAverage (fun w => ((w - c) / (w - z)) • f w) c R‖ := congrArg norm hrep.symm
    _ ≤ circleAverage (fun w => ‖((w - c) / (w - z)) • f w‖) c R :=
      norm_circleAverage_le_average_norm _ _ _
    _ ≤ circleAverage (fun w => (R / (R - r)) * ‖f w‖) c R := by
      apply circleAverage_mono (hgcont.norm.circleIntegrable hR.le)
        ((continuousOn_const.mul hfcont.norm).circleIntegrable hR.le)
      intro w hw
      rw [abs_of_pos hR] at hw
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hkernel w hw) (norm_nonneg _)
    _ = (R / (R - r)) * circleAverage (fun w => ‖f w‖) c R := by
      simpa only [smul_eq_mul] using
        (circleAverage_fun_smul (a := R / (R - r)) (f := fun w => ‖f w‖) (c := c) (R := R))

end RHTower
