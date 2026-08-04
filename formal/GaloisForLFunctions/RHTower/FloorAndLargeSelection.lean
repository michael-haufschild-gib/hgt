import GaloisForLFunctions.RHTower.EntireCircleFloor
import GaloisForLFunctions.HTGeometry.SphereMaxModulus

/-!
# One point carrying both a floor and a large value

A separation argument needs a single point at which a prescribed nonzero entire function is bounded
below and another entire function is large.  The minimum modulus supplies a circle carrying the floor,
and the maximum principle moves any large value of the second function onto that circle.

The radius is confined to a prescribed unit window, so the selection can be iterated along a sequence
of windows going to infinity.
-/

open Metric

namespace RHTower

/-- **A point with a floor and a dominating value.**  On some circle of radius in `[r, r+1]` the
function `g` is bounded below, and `F` is at least as large there as at any point of the disc of
radius `r`. -/
theorem exists_point_floor_and_large {g F : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Set.univ : Set ℂ)) (hg0 : g 0 ≠ 0)
    (hF : Differentiable ℂ F) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ∃ (z : ℂ) (ε : ℝ), 0 < ε ∧ ε ≤ ‖g z‖ ∧ ‖F w‖ ≤ ‖F z‖ ∧ r ≤ ‖z‖ ∧ ‖z‖ ≤ r + 1 := by
  obtain ⟨s, hs, ε, hε0, hfloor⟩ :=
    exists_circle_floor_of_ne_zero hg hg0 (A := r) (B := r + 1) hr.le (by linarith)
  obtain ⟨hsr, hsr1⟩ := Set.mem_Icc.mp hs
  have hs0 : 0 < s := lt_of_lt_of_le hr hsr
  obtain ⟨z, hzs, hzge⟩ :=
    GaloisForLFunctions.HTGeometry.exists_sphere_norm_ge hF hs0 (le_trans hw hsr)
  refine ⟨z, ε, hε0, ?_, hzge, ?_, ?_⟩
  · refine hfloor z ?_
    simpa using hzs
  · rw [hzs]
    exact hsr
  · rw [hzs]
    exact hsr1

/-- **The selection at a centre where the coefficient does not vanish.**  Only that the function is
not identically zero is needed: the centre is chosen where it is nonzero, and the point is the
maximiser of `F` on the floor circle, so it dominates the whole disc at once. -/
theorem exists_point_floor_and_large_of_ne {g F : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Set.univ : Set ℂ)) (hgne : ∃ c : ℂ, g c ≠ 0)
    (hF : Differentiable ℂ F) {r : ℝ} (hr : 0 < r) :
    ∃ (c z : ℂ) (ε : ℝ), 0 < ε ∧ ε ≤ ‖g z‖ ∧ r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r + 1 ∧
      ∀ w : ℂ, ‖w - c‖ ≤ r → ‖F w‖ ≤ ‖F z‖ := by
  obtain ⟨c, hc⟩ := hgne
  obtain ⟨s, hs, ε, hε0, hfloor⟩ :=
    exists_circle_floor_of_ne_zero hg hc (A := r) (B := r + 1) hr.le (by linarith)
  obtain ⟨hsr, hsr1⟩ := Set.mem_Icc.mp hs
  have hs0 : 0 < s := lt_of_lt_of_le hr hsr
  obtain ⟨z, hzs, hzmax⟩ :=
    GaloisForLFunctions.HTGeometry.exists_sphere_isMaxOn_at hF c hs0
  refine ⟨c, z, ε, hε0, hfloor z hzs, ?_, ?_, ?_⟩
  · rw [hzs]; exact hsr
  · rw [hzs]; exact hsr1
  · intro w hw
    exact hzmax w (le_trans hw hsr)

end RHTower
