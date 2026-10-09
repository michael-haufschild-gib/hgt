import Mathlib.Topology.Homotopy.Affine
import GaloisForLFunctions.HTGeometry.CornerCirclePath

open Set
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A positive rectangular boundary with one side in each quarter of unit time. -/
def rectangleBoundaryPath (a h : ℝ) :
    Path ((-a : ℂ) - (h : ℂ) * Complex.I) ((-a : ℂ) - (h : ℂ) * Complex.I) :=
  ((Path.segment ((-a : ℂ) - (h : ℂ) * Complex.I) ((a : ℂ) - (h : ℂ) * Complex.I)).trans
    (Path.segment ((a : ℂ) - (h : ℂ) * Complex.I) ((a : ℂ) + (h : ℂ) * Complex.I))).trans
    ((Path.segment ((a : ℂ) + (h : ℂ) * Complex.I) ((-a : ℂ) + (h : ℂ) * Complex.I)).trans
      (Path.segment ((-a : ℂ) + (h : ℂ) * Complex.I) ((-a : ℂ) - (h : ℂ) * Complex.I)))

theorem rectangleBoundaryPath_first_im (a h : ℝ) (t : I) (ht : (t : ℝ) ≤ 1 / 4) :
    (rectangleBoundaryPath a h t).im = -h := by
  rw [rectangleBoundaryPath, Path.trans_apply, dif_pos (by linarith : (t : ℝ) ≤ 1 / 2),
    Path.trans_apply, dif_pos (by change 2 * (t : ℝ) ≤ 1 / 2; linarith)]
  simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  ring

theorem rectangleBoundaryPath_second_re (a h : ℝ) (t : I)
    (ht0 : 1 / 4 < (t : ℝ)) (ht1 : (t : ℝ) ≤ 1 / 2) :
    (rectangleBoundaryPath a h t).re = a := by
  rw [rectangleBoundaryPath, Path.trans_apply, dif_pos ht1, Path.trans_apply,
    dif_neg (by change ¬2 * (t : ℝ) ≤ 1 / 2; linarith)]
  simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  ring

theorem rectangleBoundaryPath_third_im (a h : ℝ) (t : I)
    (ht0 : 1 / 2 < (t : ℝ)) (ht1 : (t : ℝ) ≤ 3 / 4) :
    (rectangleBoundaryPath a h t).im = h := by
  rw [rectangleBoundaryPath, Path.trans_apply, dif_neg (not_le.mpr ht0), Path.trans_apply,
    dif_pos (by change 2 * (t : ℝ) - 1 ≤ 1 / 2; linarith)]
  simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  ring

theorem rectangleBoundaryPath_fourth_re (a h : ℝ) (t : I) (ht : 3 / 4 < (t : ℝ)) :
    (rectangleBoundaryPath a h t).re = -a := by
  rw [rectangleBoundaryPath, Path.trans_apply, dif_neg (by linarith : ¬(t : ℝ) ≤ 1 / 2),
    Path.trans_apply, dif_neg (by change ¬2 * (t : ℝ) - 1 ≤ 1 / 2; linarith)]
  simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  ring

/-- The closed coordinate rectangle. -/
def complexCoordinateRectangle (a h : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc (-a) a ∧ z.im ∈ Icc (-h) h}

theorem convex_complexCoordinateRectangle (a h : ℝ) :
    Convex ℝ (complexCoordinateRectangle a h) :=
  ((convex_Icc (-a) a).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Icc (-h) h).linear_preimage Complex.imCLM.toLinearMap)

/-- Every point of the boundary stays inside its actual coordinate rectangle. -/
theorem rectangleBoundaryPath_mem_rectangle {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (t : I) :
    rectangleBoundaryPath a h t ∈ complexCoordinateRectangle a h := by
  have hnegA : -a ≤ a := by linarith
  have hnegH : -h ≤ h := by linarith
  have h₀ : ((-a : ℂ) - (h : ℂ) * Complex.I) ∈ complexCoordinateRectangle a h := by
    simp [complexCoordinateRectangle, hnegA, hnegH]
  have h₁ : ((a : ℂ) - (h : ℂ) * Complex.I) ∈ complexCoordinateRectangle a h := by
    simp [complexCoordinateRectangle, hnegA, hnegH]
  have h₂ : ((a : ℂ) + (h : ℂ) * Complex.I) ∈ complexCoordinateRectangle a h := by
    simp [complexCoordinateRectangle, hnegA, hnegH]
  have h₃ : ((-a : ℂ) + (h : ℂ) * Complex.I) ∈ complexCoordinateRectangle a h := by
    simp [complexCoordinateRectangle, hnegA, hnegH]
  have hs : range (rectangleBoundaryPath a h) ⊆ complexCoordinateRectangle a h := by
    simp only [rectangleBoundaryPath, Path.trans_range, Path.range_segment, union_subset_iff]
    exact ⟨⟨(convex_complexCoordinateRectangle a h).segment_subset h₀ h₁,
      (convex_complexCoordinateRectangle a h).segment_subset h₁ h₂⟩,
      (convex_complexCoordinateRectangle a h).segment_subset h₂ h₃,
      (convex_complexCoordinateRectangle a h).segment_subset h₃ h₀⟩
  exact hs ⟨t, rfl⟩

end
end GaloisForLFunctions.HTGeometry
