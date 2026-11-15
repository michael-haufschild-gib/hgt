import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovVerticalDilation

/-!
# The full affine action on moment coordinates

Adding the moment of the vertical center to the linear shear gives the
actual affine action on the ambient moment space. Its composition law
adds the physical shear and translation parameters. Vertical dilation
intertwines this action with simultaneous scaling of those parameters.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The ambient affine map induced by a physical vertical shear and translation. -/
def momentAffineAction (r k : ℕ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (x : AffineAxisSpace r k) : AffineAxisSpace r k :=
  horizontalMoment r k 0 t + Matrix.toLin' (vectorAffineMatrix r k δ t) x

/-- The affine action sends every moment vector to the moment of the transformed physical point. -/
theorem momentAffineAction_moment (r k : ℕ) (δ u : Fin (r + 1) → ℝ) (t z : ℝ) :
    momentAffineAction r k δ t (horizontalMoment r k u z) =
      horizontalMoment r k u (z + ∑ i, δ i * u i + t) := by
  rw [momentAffineAction, Matrix.toLin'_apply, vectorAffineMatrix_moment]
  abel_nf

/-- Composition adds both affine parameters on the full ambient space. -/
theorem momentAffineAction_comp (r k : ℕ) (δ η : Fin (r + 1) → ℝ)
    (t s : ℝ) (x : AffineAxisSpace r k) :
    momentAffineAction r k δ t (momentAffineAction r k η s x) =
      momentAffineAction r k (δ + η) (t + s) x := by
  have hc : Matrix.toLin' (vectorAffineMatrix r k δ t) (horizontalMoment r k 0 s) =
      horizontalMoment r k 0 (t + s) - horizontalMoment r k 0 t := by
    simpa only [Matrix.toLin'_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero, show s + t = t + s by ring] using vectorAffineMatrix_moment r k δ 0 t s
  simp only [momentAffineAction, map_add, hc, vectorAffineLinear_comp_apply]
  abel_nf

/-- The zero affine parameters act as the identity. -/
theorem momentAffineAction_zero (r k : ℕ) (x : AffineAxisSpace r k) :
    momentAffineAction r k 0 0 x = x := by
  rw [momentAffineAction, horizontalMoment_zero, vectorAffineLinear_zero_apply, zero_add]

/-- Negated affine parameters undo the action from the left. -/
theorem momentAffineAction_neg_cancel (r k : ℕ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (x : AffineAxisSpace r k) :
    momentAffineAction r k (-δ) (-t) (momentAffineAction r k δ t x) = x := by
  simp only [momentAffineAction_comp, neg_add_cancel, momentAffineAction_zero]

/-- Negated affine parameters undo the action from the right. -/
theorem momentAffineAction_cancel_neg (r k : ℕ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (x : AffineAxisSpace r k) :
    momentAffineAction r k δ t (momentAffineAction r k (-δ) (-t) x) = x := by
  simp only [momentAffineAction_comp, add_neg_cancel, momentAffineAction_zero]

/-- Every affine moment action is an equivalence, with explicitly negated inverse parameters. -/
def momentAffineEquiv (r k : ℕ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    AffineAxisSpace r k ≃ AffineAxisSpace r k where
  toFun := momentAffineAction r k δ t
  invFun := momentAffineAction r k (-δ) (-t)
  left_inv := momentAffineAction_neg_cancel r k δ t
  right_inv := momentAffineAction_cancel_neg r k δ t

/-- Vertical dilation scales the full affine action, including its moment center. -/
theorem verticalDilation_momentAffineAction (r k : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (x : AffineAxisSpace r k) :
    Matrix.toLin' (verticalDilationMatrix r k ε) (momentAffineAction r k δ t x) =
      momentAffineAction r k (ε • δ) (ε * t)
        (Matrix.toLin' (verticalDilationMatrix r k ε) x) := by
  have hc : Matrix.toLin' (verticalDilationMatrix r k ε) (horizontalMoment r k 0 t) =
      horizontalMoment r k 0 (ε * t) := by
    simpa only [Matrix.toLin'_apply] using verticalDilationMatrix_moment r k ε 0 t
  have hl : Matrix.toLin' (verticalDilationMatrix r k ε)
      (Matrix.toLin' (vectorAffineMatrix r k δ t) x) =
        Matrix.toLin' (vectorAffineMatrix r k (ε • δ) (ε * t))
          (Matrix.toLin' (verticalDilationMatrix r k ε) x) := by
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, verticalDilationMatrix_vectorAffine]
  simp only [momentAffineAction, map_add, hc, hl]

#print axioms momentAffineAction_moment
#print axioms momentAffineAction_comp
#print axioms momentAffineAction_zero
#print axioms momentAffineAction_neg_cancel
#print axioms momentAffineAction_cancel_neg
#print axioms momentAffineEquiv
#print axioms verticalDilation_momentAffineAction

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
