import Mathlib.Analysis.Complex.Poisson

/-!
# The dilated Poisson representation on the unit disc

A holomorphic function on the open unit disc is represented inside every smaller disc by the Poisson
integral of its dilation.  The family of boundary densities obtained this way is the family whose
weak-* limit is the Herglotz measure of a Carathéodory function; this file supplies the family and
its normalization.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric

noncomputable section

/-- Dilation by `r < 1` carries a function holomorphic on the open unit disc to one holomorphic on
a neighbourhood of the closed unit disc. -/
theorem diffContOnCl_dilate {F : ℂ → ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    DiffContOnCl ℂ (fun z => F ((r : ℂ) * z)) (ball (0 : ℂ) 1) := by
  have hrinv : (1 : ℝ) < 1 / r := by
    rw [lt_div_iff₀ hr0]
    linarith
  have hmaps : Set.MapsTo (fun z : ℂ => (r : ℂ) * z) (ball (0 : ℂ) (1 / r)) (ball (0 : ℂ) 1) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    rw [lt_div_iff₀ hr0] at hz
    linarith [hz]
  have hbig : DifferentiableOn ℂ (fun z : ℂ => F ((r : ℂ) * z)) (ball (0 : ℂ) (1 / r)) :=
    hF.comp ((differentiable_id.const_mul _).differentiableOn) hmaps
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball (0 : ℂ) (1 / r) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]
    linarith
  refine ⟨hbig.mono (subset_trans ball_subset_closedBall hsub), ?_⟩
  rw [closure_ball _ (by norm_num)]
  exact (hbig.mono hsub).continuousOn

/-- **The dilated Poisson representation.**  For `0 < r < 1` the dilation of a holomorphic function
on the open unit disc is the Poisson integral of its boundary values on the unit circle. -/
theorem circleAverage_poissonKernel_dilate {F : ℂ → ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    Real.circleAverage (_root_.poissonKernel 0 w • fun z => F ((r : ℂ) * z)) 0 1
      = F ((r : ℂ) * w) :=
  (diffContOnCl_dilate hr0 hr1 hF).circleAverage_poissonKernel_smul hw

/-- The Poisson kernel is the constant one at the centre. -/
theorem poissonKernel_center_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    _root_.poissonKernel 0 0 z = 1 := by
  rw [_root_.poissonKernel_def]
  simp [hz]

/-- **Normalization of the boundary family.**  The circle average of the dilation is the value at
the centre, so the boundary densities of a function with positive real part form a family of
probability densities once the value at the centre is one. -/
theorem circleAverage_dilate_eq_center {F : ℂ → ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    Real.circleAverage (fun z => F ((r : ℂ) * z)) 0 1 = F 0 := by
  have hw : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_self]
    norm_num
  have hmain := circleAverage_poissonKernel_dilate (F := F) hr0 hr1 hF hw
  have hcongr : Real.circleAverage (_root_.poissonKernel 0 0 • fun z => F ((r : ℂ) * z)) 0 1
      = Real.circleAverage (fun z => F ((r : ℂ) * z)) 0 1 := by
    refine Real.circleAverage_congr_sphere fun z hz => ?_
    rw [mem_sphere, dist_zero_right] at hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    simp [poissonKernel_center_eq_one hz1]
  rw [hcongr] at hmain
  simpa using hmain

end

end GaloisForLFunctions.HTGeometry
