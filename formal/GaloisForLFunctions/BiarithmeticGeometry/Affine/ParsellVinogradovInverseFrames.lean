import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovMomentAffineAction
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovCoveringRange

/-!
# Inverse moment frames and normalized parallel translations

A nonzero vertical scale gives an explicit inverse to each moment-centered
frame. Passing from one parallel frame to another cancels the common shear
and leaves a vertical translation divided by the scale. On an integer grid,
the resulting normalized map depends only on the index difference and density.
-/

open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The full moment-centered affine covering frame. -/
def momentFrame (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (x : AffineAxisSpace r k) : AffineAxisSpace r k :=
  horizontalMoment r k 0 t + Matrix.toLin' (scaledAffineMatrix r k ε δ t) x

/-- Undo the affine physical shear, then undo the vertical dilation. -/
def momentFrameInverse (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (x : AffineAxisSpace r k) : AffineAxisSpace r k :=
  Matrix.toLin' (verticalDilationMatrix r k ε⁻¹)
    (momentAffineAction r k (-(ε • δ)) (-t) x)

/-- A moment frame is the composition of vertical dilation and the full affine action. -/
theorem momentFrame_eq_affineAction (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (x : AffineAxisSpace r k) :
    momentFrame r k ε δ t x = momentAffineAction r k (ε • δ) t
      (Matrix.toLin' (verticalDilationMatrix r k ε) x) := by
  rw [momentFrame, scaledAffineLinear_apply]
  rfl

/-- The explicit inverse undoes every nondegenerate moment frame. -/
theorem momentFrameInverse_frame (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (x : AffineAxisSpace r k) :
    momentFrameInverse r k ε δ t (momentFrame r k ε δ t x) = x := by
  rw [momentFrameInverse, momentFrame_eq_affineAction, momentAffineAction_neg_cancel,
    verticalDilationLinear_comp_apply, inv_mul_cancel₀ hε, verticalDilationLinear_one_apply]

/-- Every ambient point is recovered from its inverse-frame coordinates. -/
theorem momentFrame_frameInverse (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (x : AffineAxisSpace r k) :
    momentFrame r k ε δ t (momentFrameInverse r k ε δ t x) = x := by
  rw [momentFrame_eq_affineAction, momentFrameInverse, verticalDilationLinear_comp_apply,
    mul_inv_cancel₀ hε, verticalDilationLinear_one_apply, momentAffineAction_cancel_neg]

/-- The moment-centered frame equivalence has the explicit inverse above. -/
def momentFrameEquiv (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) : AffineAxisSpace r k ≃ AffineAxisSpace r k where
  toFun := momentFrame r k ε δ t
  invFun := momentFrameInverse r k ε δ t
  left_inv := momentFrameInverse_frame r k ε hε δ t
  right_inv := momentFrame_frameInverse r k ε hε δ t

/-- The affine inverse agrees with subtracting the center and applying the two inverse linear maps. -/
theorem momentFrameInverse_linear_formula (r k : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (x : AffineAxisSpace r k) :
    momentFrameInverse r k ε δ t x =
      Matrix.toLin' (verticalDilationMatrix r k ε⁻¹)
        (Matrix.toLin' (vectorAffineMatrix r k (-(ε • δ)) (-t))
          (x - horizontalMoment r k 0 t)) := by
  have hc : Matrix.toLin' (vectorAffineMatrix r k (-(ε • δ)) (-t))
      (horizontalMoment r k 0 t) = -horizontalMoment r k 0 (-t) := by
    simpa only [Matrix.toLin'_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero, add_neg_cancel, horizontalMoment_zero, zero_sub] using
        vectorAffineMatrix_moment r k (-(ε • δ)) 0 (-t) t
  unfold momentFrameInverse
  congr 1
  rw [momentAffineAction, map_sub, hc]
  abel_nf

/-- Relative coordinates of parallel frames depend only on their normalized vertical displacement. -/
theorem momentFrameInverse_parallelFrame (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t s : ℝ) (x : AffineAxisSpace r k) :
    momentFrameInverse r k ε δ s (momentFrame r k ε δ t x) =
      momentAffineAction r k 0 ((t - s) / ε) x := by
  rw [momentFrameInverse, momentFrame_eq_affineAction, momentAffineAction_comp,
    neg_add_cancel, show -s + t = t - s by ring, verticalDilation_momentAffineAction]
  simp only [smul_zero, verticalDilationLinear_comp_apply, inv_mul_cancel₀ hε,
    verticalDilationLinear_one_apply]
  congr 1
  ring

/-- On a regular integer grid, the normalized relative frame is independent of scale and direction. -/
theorem momentFrameInverse_integer_parallelFrame (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i j : ℤ) (x : AffineAxisSpace r k) :
    momentFrameInverse r k ε δ (ε * (j : ℝ) / (q + 1 : ℝ))
      (momentFrame r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x) =
        momentAffineAction r k 0 (((i : ℝ) - (j : ℝ)) / (q + 1 : ℝ)) x := by
  rw [momentFrameInverse_parallelFrame r k ε hε]
  congr 1
  calc
    _ = ((((i : ℝ) - (j : ℝ)) / (q + 1 : ℝ)) / ε) * ε := by ring
    _ = _ := div_mul_cancel₀ _ hε

/-- Membership in a covering box is exactly the radius-two bound in inverse-frame coordinates. -/
theorem mem_momentCoveringBox_iff_inverse (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (x : AffineAxisSpace r k) :
    x ∈ momentCoveringBox r k ε δ t ↔
      momentFrameInverse r k ε δ t x ∈ centeredCube 0 2 := by
  change x ∈ momentFrame r k ε δ t '' centeredCube 0 2 ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [momentFrameInverse_frame r k ε hε] using hy
  · intro hx
    exact ⟨momentFrameInverse r k ε δ t x, hx, momentFrame_frameInverse r k ε hε δ t x⟩

/-- The defining moment center has zero normalized coordinates. -/
theorem momentFrameInverse_center (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    momentFrameInverse r k ε δ t (horizontalMoment r k 0 t) = 0 := by
  simpa only [momentFrame, map_zero, add_zero] using
    momentFrameInverse_frame r k ε hε δ t 0

/-- Inverse-frame coordinates of a moment are the moments of the inverse physical shear. -/
theorem momentFrameInverse_moment (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ u : Fin (r + 1) → ℝ) (t z : ℝ) :
    momentFrameInverse r k ε δ t (horizontalMoment r k u z) =
      horizontalMoment r k u ((z - t) / ε - ∑ i, δ i * u i) := by
  have hs : (∑ i, (-(ε • δ)) i * u i) = -ε * ∑ i, δ i * u i := by
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_mul,
      Finset.sum_neg_distrib, Finset.mul_sum, mul_assoc]
  rw [momentFrameInverse, momentAffineAction_moment, Matrix.toLin'_apply,
    verticalDilationMatrix_moment, hs]
  congr 1
  field_simp [hε]
  ring

#print axioms momentFrame_eq_affineAction
#print axioms momentFrameInverse_frame
#print axioms momentFrame_frameInverse
#print axioms momentFrameEquiv
#print axioms momentFrameInverse_linear_formula
#print axioms momentFrameInverse_parallelFrame
#print axioms momentFrameInverse_integer_parallelFrame
#print axioms mem_momentCoveringBox_iff_inverse
#print axioms momentFrameInverse_center
#print axioms momentFrameInverse_moment

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
