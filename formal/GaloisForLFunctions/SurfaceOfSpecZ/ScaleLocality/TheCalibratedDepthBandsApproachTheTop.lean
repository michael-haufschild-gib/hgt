import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheCalibratedBlocksHaveSmallSplineWeights
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SubLogarithmicWindowsMissTheMinimalFace

/-!
# Depth bands with an unattained top

Alternating terms of the existing increasing depth sequence supply common
block depths and strict upper bounds. Small calibration disks stay in the
positive strip, and every depth in the bands approaches the same top.
-/

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The common real exponential shift at one calibrated level. -/
def calibratedDepthCenter (Θ : ℝ) (k : ℕ) : ℝ := SplineTower.depth Θ (2 * k + 1)

/-- A strict upper bound for every perturbed depth at one level. -/
def calibratedDepthUpper (Θ : ℝ) (k : ℕ) : ℝ := SplineTower.depth Θ (2 * k + 2)

/-- Calibration tolerance, keeping the whole depth disk positive and below its upper bound. -/
def calibratedDepthTolerance (Θ : ℝ) (k : ℕ) : ℝ :=
  min (calibratedDepthCenter Θ k / 2)
    ((calibratedDepthUpper Θ k - calibratedDepthCenter Θ k) / 2)

/-- Each calibration disk lies strictly between zero and the level's upper depth. -/
theorem calibratedDepth_bounds {Θ : ℝ} (hΘ : 0 < Θ) (k : ℕ) :
    0 < calibratedDepthTolerance Θ k ∧
      0 < calibratedDepthCenter Θ k - calibratedDepthTolerance Θ k ∧
      calibratedDepthCenter Θ k + calibratedDepthTolerance Θ k < calibratedDepthUpper Θ k ∧
      calibratedDepthUpper Θ k < Θ := by
  have hc : 0 < calibratedDepthCenter Θ k := SplineTower.depth_pos hΘ _
  have hcu : calibratedDepthCenter Θ k < calibratedDepthUpper Θ k :=
    SplineTower.strictMono_depth hΘ (by omega)
  have hu : calibratedDepthUpper Θ k < Θ := SplineTower.depth_lt hΘ _
  have hη0 : 0 < calibratedDepthTolerance Θ k := by
    apply lt_min (half_pos hc)
    exact half_pos (sub_pos.mpr hcu)
  have hηc : calibratedDepthTolerance Θ k ≤ calibratedDepthCenter Θ k / 2 := min_le_left _ _
  have hηu : calibratedDepthTolerance Θ k ≤
      (calibratedDepthUpper Θ k - calibratedDepthCenter Θ k) / 2 := min_le_right _ _
  exact ⟨hη0, by linarith only [hc, hηc], by linarith only [hcu, hηu], hu⟩

/-- Upper depths increase strictly. -/
theorem strictMono_calibratedDepthUpper {Θ : ℝ} (hΘ : 0 < Θ) :
    StrictMono (calibratedDepthUpper Θ) := by
  intro i j hij
  exact SplineTower.strictMono_depth hΘ (by omega)

/-- A new common depth exceeds the preceding level's entire depth band. -/
theorem calibratedDepthUpper_lt_next_center {Θ : ℝ} (hΘ : 0 < Θ) (k : ℕ) :
    calibratedDepthUpper Θ k < calibratedDepthCenter Θ (k + 1) :=
  SplineTower.strictMono_depth hΘ (by omega)

/-- Even the lower edges of the depth bands approach the prescribed top. -/
theorem exists_calibratedDepth_lower_gt {Θ β : ℝ} (hΘ : 0 < Θ) (hβ : β < Θ) :
    ∃ k, β < calibratedDepthCenter Θ k - calibratedDepthTolerance Θ k := by
  obtain ⟨n, hn⟩ := SplineTower.exists_depth_gt hΘ
    (show (2 * β + Θ) / 3 < Θ by linarith only [hβ])
  have hmono : SplineTower.depth Θ n ≤ calibratedDepthCenter Θ n :=
    (SplineTower.strictMono_depth hΘ).monotone (by omega)
  have hηu : calibratedDepthTolerance Θ n ≤
      (calibratedDepthUpper Θ n - calibratedDepthCenter Θ n) / 2 := min_le_right _ _
  have hu := (calibratedDepth_bounds hΘ n).2.2.2
  exact ⟨n, by linarith only [hn, hmono, hηu, hu]⟩

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
