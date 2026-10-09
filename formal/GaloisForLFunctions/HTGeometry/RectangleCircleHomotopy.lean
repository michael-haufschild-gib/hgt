import GaloisForLFunctions.HTGeometry.RectangleBoundaryPath

open Set
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem lineMap_ne_zero_of_halfplane (L : ℂ →ₗ[ℝ] ℝ) {x y : ℂ}
    (hx : 0 < L x) (hy : 0 < L y) (s : I) : AffineMap.lineMap x y (s : ℝ) ≠ 0 := by
  have hp : 0 < L (AffineMap.lineMap x y (s : ℝ)) :=
    ((convex_Ioi (0 : ℝ)).linear_preimage L).lineMap_mem hx hy s.property
  intro hz
  rw [hz, map_zero] at hp
  exact (lt_irrefl 0) hp

/-- Straight interpolation of the aligned rectangle and circle, with its basepoint free to move. -/
def rectangleCircleHomotopy (a h r : ℝ) :
    (rectangleBoundaryPath a h).toContinuousMap.Homotopy (cornerCirclePath r).toContinuousMap :=
  ContinuousMap.Homotopy.affine _ _

/-- Every intermediate path remains a loop while its common basepoint moves. -/
theorem rectangleCircleHomotopy_closed (a h r : ℝ) (s : I) :
    rectangleCircleHomotopy a h r (s, 0) = rectangleCircleHomotopy a h r (s, 1) := by
  change AffineMap.lineMap (rectangleBoundaryPath a h 0) (cornerCirclePath r 0) (s : ℝ) =
    AffineMap.lineMap (rectangleBoundaryPath a h 1) (cornerCirclePath r 1) (s : ℝ)
  rw [(rectangleBoundaryPath a h).source, (rectangleBoundaryPath a h).target,
    (cornerCirclePath r).source, (cornerCirclePath r).target]

/-- Alignment alone prevents crossing the center, for every positive radius. -/
theorem rectangleCircleHomotopy_ne_zero {a h r : ℝ} (ha : 0 < a) (hh : 0 < h) (hr : 0 < r)
    (s t : I) : rectangleCircleHomotopy a h r (s, t) ≠ 0 := by
  change AffineMap.lineMap (rectangleBoundaryPath a h t) (cornerCirclePath r t) (s : ℝ) ≠ 0
  by_cases ht0 : (t : ℝ) ≤ 1 / 4
  · apply lineMap_ne_zero_of_halfplane (-Complex.imCLM.toLinearMap) (s := s)
    · change 0 < -(rectangleBoundaryPath a h t).im
      rw [rectangleBoundaryPath_first_im a h t ht0, neg_neg]
      exact hh
    · change 0 < -(cornerCirclePath r t).im
      exact neg_pos.mpr (cornerCirclePath_first_im hr t ht0)
  by_cases ht1 : (t : ℝ) ≤ 1 / 2
  · apply lineMap_ne_zero_of_halfplane Complex.reCLM.toLinearMap (s := s)
    · change 0 < (rectangleBoundaryPath a h t).re
      rw [rectangleBoundaryPath_second_re a h t (lt_of_not_ge ht0) ht1]
      exact ha
    · exact cornerCirclePath_second_re hr t (le_of_lt (lt_of_not_ge ht0)) ht1
  by_cases ht2 : (t : ℝ) ≤ 3 / 4
  · apply lineMap_ne_zero_of_halfplane Complex.imCLM.toLinearMap (s := s)
    · change 0 < (rectangleBoundaryPath a h t).im
      rw [rectangleBoundaryPath_third_im a h t (lt_of_not_ge ht1) ht2]
      exact hh
    · exact cornerCirclePath_third_im hr t (le_of_lt (lt_of_not_ge ht1)) ht2
  · apply lineMap_ne_zero_of_halfplane (-Complex.reCLM.toLinearMap) (s := s)
    · change 0 < -(rectangleBoundaryPath a h t).re
      rw [rectangleBoundaryPath_fourth_re a h t (lt_of_not_ge ht2), neg_neg]
      exact ha
    · change 0 < -(cornerCirclePath r t).re
      exact neg_pos.mpr (cornerCirclePath_fourth_re hr t (le_of_lt (lt_of_not_ge ht2)))

/-- A fitting circle keeps the entire actual homotopy inside the same rectangle. -/
theorem rectangleCircleHomotopy_mem_rectangle {a h r : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hr : 0 ≤ r) (hra : r ≤ a) (hrh : r ≤ h) (s t : I) :
    rectangleCircleHomotopy a h r (s, t) ∈ complexCoordinateRectangle a h := by
  change AffineMap.lineMap (rectangleBoundaryPath a h t) (cornerCirclePath r t) (s : ℝ) ∈ _
  apply (convex_complexCoordinateRectangle a h).lineMap_mem
    (rectangleBoundaryPath_mem_rectangle ha hh t) _ s.property
  have hn : ‖cornerCirclePath r t‖ = r := by rw [norm_cornerCirclePath, abs_of_nonneg hr]
  constructor
  · exact abs_le.mp ((Complex.abs_re_le_norm _).trans (hn.le.trans hra))
  · exact abs_le.mp ((Complex.abs_im_le_norm _).trans (hn.le.trans hrh))

end
end GaloisForLFunctions.HTGeometry
