import GaloisForLFunctions.HTGeometry.VerticalContourShift

/-!
# The truncated contour shift

`integral_vertical_line_eq_of_horizontal_tendsto` shifts a contour between two vertical lines, but
requires the horizontal edges to vanish as the height tends to infinity — which forces the
holomorphy and the bound to hold at *every* height.  For `1/ζ` that is unavailable: the zero-free
region narrows as the height grows.

The classical argument instead truncates at height `T` and keeps the horizontal edges as explicit
terms.  That identity is Cauchy's theorem on the rectangle, and it is what this module exposes.
-/

namespace RHTower.Sieve

open Complex GaloisForLFunctions.HTGeometry

/-- **The truncated contour shift.**  For `G` holomorphic on the closed strip, the difference of the
truncated vertical integrals is the difference of the horizontal edges. -/
theorem integral_vertical_sub_eq_horizontal {G : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hdiff : DifferentiableOn ℂ G (verticalStrip c d)) (T : ℝ) :
    (Complex.I • (∫ y : ℝ in (-T)..T, G ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T, G ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d, G ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d, G ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
  have hz : ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re = c := by simp
  have hz' : ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im = -T := by simp
  have hw : ((d : ℂ) + ((T : ℝ) : ℂ) * Complex.I).re = d := by simp
  have hw' : ((d : ℂ) + ((T : ℝ) : ℂ) * Complex.I).im = T := by simp
  have hsub : DifferentiableOn ℂ G
      (Set.uIcc ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).re
          ((d : ℂ) + ((T : ℝ) : ℂ) * Complex.I).re ×ℂ
        Set.uIcc ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im
          ((d : ℂ) + ((T : ℝ) : ℂ) * Complex.I).im) := by
    rw [hz, hz', hw, hw']
    exact hdiff.mono (rect_subset_verticalStrip hcd T)
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ((d : ℂ) + ((T : ℝ) : ℂ) * Complex.I) hsub
  rw [hz, hz', hw, hw'] at hcauchy
  linear_combination hcauchy

end RHTower.Sieve
