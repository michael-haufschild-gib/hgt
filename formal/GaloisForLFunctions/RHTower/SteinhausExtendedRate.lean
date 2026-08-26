import GaloisForLFunctions.RHTower.SteinhausRateStrictMono

/-!
# Extended planar rate for the weighted Steinhaus model

The planar model is rotationally invariant.  Its rate is the radial Legendre transform inside the
open unit disk and `∞` on the boundary and exterior.
-/

open Set

namespace HTGeometry

noncomputable section

/-- Extended-valued rate on `ℝ²`, represented by `ℂ`. -/
def rvPlanarRate (α : ℝ) (z : ℂ) : ENNReal :=
  if ‖z‖ < 1 then ENNReal.ofReal (rvRate α ‖z‖) else ⊤

theorem rvPlanarRate_of_norm_lt_one {α : ℝ} {z : ℂ} (hz : ‖z‖ < 1) :
    rvPlanarRate α z = ENNReal.ofReal (rvRate α ‖z‖) := by
  rw [rvPlanarRate, if_pos hz]

theorem rvPlanarRate_of_one_le_norm {α : ℝ} {z : ℂ} (hz : 1 ≤ ‖z‖) :
    rvPlanarRate α z = ⊤ := by
  rw [rvPlanarRate, if_neg (not_lt_of_ge hz)]

/-- The rate is finite exactly in the open unit disk. -/
theorem rvPlanarRate_ne_top_iff {α : ℝ} {z : ℂ} :
    rvPlanarRate α z ≠ ⊤ ↔ ‖z‖ < 1 := by
  constructor
  · intro h
    by_contra hz
    exact h (rvPlanarRate_of_one_le_norm (le_of_not_gt hz))
  · intro hz
    rw [rvPlanarRate_of_norm_lt_one hz]
    exact ENNReal.ofReal_ne_top

/-- Boundary and exterior points have infinite rate. -/
theorem rvPlanarRate_eq_top_iff {α : ℝ} {z : ℂ} :
    rvPlanarRate α z = ⊤ ↔ 1 ≤ ‖z‖ := by
  rw [← not_iff_not]
  simpa only [not_le] using rvPlanarRate_ne_top_iff (α := α) (z := z)

theorem rvPlanarRate_zero {α : ℝ} (hα : α < 1) : rvPlanarRate α 0 = 0 := by
  rw [rvPlanarRate_of_norm_lt_one (by simp), norm_zero, rvRate_zero hα, ENNReal.ofReal_zero]

/-- Every nonzero point of the open disk has strictly positive finite rate. -/
theorem rvPlanarRate_pos {α : ℝ} (h0 : 0 ≤ α) (hα : α < 1)
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) :
    0 < rvPlanarRate α z := by
  rw [rvPlanarRate_of_norm_lt_one hz1]
  exact ENNReal.ofReal_pos.mpr (rvRate_pos h0 hα (norm_pos_iff.mpr hz0) hz1)

theorem rvPlanarRate_eq_zero_iff {α : ℝ} (h0 : 0 ≤ α) (hα : α < 1) {z : ℂ} :
    rvPlanarRate α z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    by_contra hz0
    by_cases hz1 : ‖z‖ < 1
    · exact (ne_of_gt (rvPlanarRate_pos h0 hα hz0 hz1)) hz
    · rw [rvPlanarRate_of_one_le_norm (le_of_not_gt hz1)] at hz
      exact ENNReal.top_ne_zero hz
  · rintro rfl
    exact rvPlanarRate_zero hα

/-- Rotations preserve the planar rate. -/
theorem rvPlanarRate_eq_of_norm_eq {α : ℝ} {z w : ℂ} (hzw : ‖z‖ = ‖w‖) :
    rvPlanarRate α z = rvPlanarRate α w := by
  rw [rvPlanarRate, rvPlanarRate, hzw]

theorem rvPlanarRate_unit_mul {α : ℝ} {u z : ℂ} (hu : ‖u‖ = 1) :
    rvPlanarRate α (u * z) = rvPlanarRate α z := by
  apply rvPlanarRate_eq_of_norm_eq
  rw [norm_mul, hu, one_mul]

end


end HTGeometry
