import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The height of a point is its distance to the real axis

For a point of the open upper half plane, the disk of radius its height stays in
the half plane, and the height is exactly the distance to the real axis.

This is the geometry behind the shift-lattice radius law: the theta function is
holomorphic on the open half plane, so its expansion at an interior base point
converges at least on the disk of radius the height, and the nearest possible
singularity is the boundary point directly below.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

/-- Inside the disk of radius its height, every point is still in the upper half
plane. -/
theorem im_pos_of_mem_ball {z₀ z : ℂ}
    (h : z ∈ Metric.ball z₀ z₀.im) : 0 < z.im := by
  rw [Metric.mem_ball, Complex.dist_eq] at h
  have hle : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at hle
  have : |z.im - z₀.im| < z₀.im := lt_of_le_of_lt hle h
  have hlt := (abs_lt.mp this).1
  linarith

/-- The real axis, as the zero set of the imaginary part. -/
def realAxis : Set ℂ := {z : ℂ | z.im = 0}

theorem realAxis_nonempty : realAxis.Nonempty := ⟨0, by simp [realAxis]⟩

/-- **The height is the distance to the real axis.** -/
theorem infDist_realAxis_eq_im {z₀ : ℂ} (hz : 0 < z₀.im) :
    Metric.infDist z₀ realAxis = z₀.im := by
  refine le_antisymm ?_ ?_
  · have hmem : ((z₀.re : ℝ) : ℂ) ∈ realAxis := by
      simp [realAxis]
    have hle : Metric.infDist z₀ realAxis ≤ dist z₀ ((z₀.re : ℝ) : ℂ) :=
      Metric.infDist_le_dist_of_mem hmem
    have hdist : dist z₀ ((z₀.re : ℝ) : ℂ) = z₀.im := by
      rw [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        sub_self, sub_zero]
      rw [show (0 : ℝ) * 0 + z₀.im * z₀.im = z₀.im ^ (2 : ℕ) by ring,
        Real.sqrt_sq hz.le]
    rwa [hdist] at hle
  · refine (Metric.le_infDist realAxis_nonempty).mpr fun w hw => ?_
    have hle : |(z₀ - w).im| ≤ ‖z₀ - w‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, (by exact hw : w.im = 0), sub_zero,
      abs_of_pos hz] at hle
    rwa [Complex.dist_eq]

end GaloisForLFunctions.HTGeometry
