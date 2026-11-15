import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovVerticalExponent
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovVectorGroup

/-!
# Vertical dilation of complete moment frames

The physical map `(u,z) ↦ (u,ε*z)` acts diagonally on monomial coordinates.
Its determinant is the scale raised to the total vertical weight. The
faithful moment action also identifies its exact commutation relation
with every affine shear, including the singular scale zero.
-/

open MeasureTheory Matrix
open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Vertical dilation scales each nonconstant moment by its vertical monomial weight. -/
def verticalDilationMatrix (r k : ℕ) (ε : ℝ) :
    Matrix (AffineAxisIndex r k) (AffineAxisIndex r k) ℝ :=
  Matrix.diagonal (fun a => ε ^ a.2.2.val)

theorem verticalDilationMatrix_mulVec_apply (r k : ℕ) (ε : ℝ)
    (x : AffineAxisSpace r k) (a : AffineAxisIndex r k) :
    (verticalDilationMatrix r k ε *ᵥ x) a = ε ^ a.2.2.val * x a :=
  Matrix.mulVec_diagonal _ _ _

/-- The diagonal matrix is the actual physical vertical dilation on every moment. -/
theorem verticalDilationMatrix_moment (r k : ℕ) (ε : ℝ)
    (u : Fin (r + 1) → ℝ) (z : ℝ) :
    verticalDilationMatrix r k ε *ᵥ horizontalMoment r k u z =
      horizontalMoment r k u (ε * z) := by
  rw [horizontalMoment_eq, horizontalMoment_eq]
  funext a
  rw [verticalDilationMatrix_mulVec_apply]
  dsimp only [affineAxisMoment, fullAxisMoment, positiveAxisIndex]
  rw [mul_pow]
  ring

/-- Vertical dilations multiply their physical scale parameters. -/
theorem verticalDilationMatrix_mul (r k : ℕ) (ε η : ℝ) :
    verticalDilationMatrix r k ε * verticalDilationMatrix r k η =
      verticalDilationMatrix r k (ε * η) := by
  simp only [verticalDilationMatrix, Matrix.diagonal_mul_diagonal, mul_pow]

theorem verticalDilationMatrix_one (r k : ℕ) : verticalDilationMatrix r k 1 = 1 := by
  simp only [verticalDilationMatrix, one_pow, Matrix.diagonal_one]

/-- The exact dilation determinant is the scale raised to the binomial volume exponent. -/
theorem det_verticalDilationMatrix (r k : ℕ) (ε : ℝ) :
    (verticalDilationMatrix r k ε).det = ε ^ verticalExponent r k := by
  rw [verticalDilationMatrix, Matrix.det_diagonal,
    Finset.prod_pow_eq_pow_sum, sum_verticalAxisIndex]

/-- Every set acquires exactly the anisotropic volume factor, even at scale zero. -/
theorem volume_verticalDilation_image (r k : ℕ) (ε : ℝ) (S : Set (AffineAxisSpace r k)) :
    volume ((Matrix.toLin' (verticalDilationMatrix r k ε)) '' S) =
      ENNReal.ofReal (|ε| ^ verticalExponent r k) * volume S := by
  simpa only [LinearMap.det_toLin', det_verticalDilationMatrix, abs_pow] using
    Measure.addHaar_image_linearMap volume (Matrix.toLin' (verticalDilationMatrix r k ε)) S

/-- Dilation scales the horizontal shear coefficients and the vertical translation together. -/
theorem verticalDilationMatrix_vectorAffine (r k : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    verticalDilationMatrix r k ε * vectorAffineMatrix r k δ t =
      vectorAffineMatrix r k (ε • δ) (ε * t) * verticalDilationMatrix r k ε := by
  apply matrix_eq_of_horizontalMoment_eq
  intro u z
  rw [← Matrix.mulVec_mulVec, vectorAffineMatrix_moment, Matrix.mulVec_sub,
    verticalDilationMatrix_moment, verticalDilationMatrix_moment,
    ← Matrix.mulVec_mulVec, verticalDilationMatrix_moment, vectorAffineMatrix_moment]
  have hs : (∑ i, (ε • δ) i * u i) = ε * ∑ i, δ i * u i := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [hs, show ε * (z + ∑ i, δ i * u i + t) =
    ε * z + ε * ∑ i, δ i * u i + ε * t by ring]

/-- The scale composition law holds on the full ambient coordinate space. -/
theorem verticalDilationLinear_comp_apply (r k : ℕ) (ε η : ℝ) (x : AffineAxisSpace r k) :
    Matrix.toLin' (verticalDilationMatrix r k ε)
      (Matrix.toLin' (verticalDilationMatrix r k η) x) =
        Matrix.toLin' (verticalDilationMatrix r k (ε * η)) x := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, verticalDilationMatrix_mul]

theorem verticalDilationLinear_one_apply (r k : ℕ) (x : AffineAxisSpace r k) :
    Matrix.toLin' (verticalDilationMatrix r k 1) x = x := by
  rw [Matrix.toLin'_apply, verticalDilationMatrix_one, Matrix.one_mulVec]

/-- Every nonzero vertical scale is invertible on all moment coordinates. -/
theorem verticalDilationLinear_injective (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0) :
    Function.Injective (Matrix.toLin' (verticalDilationMatrix r k ε)) := by
  apply Function.LeftInverse.injective (g := Matrix.toLin' (verticalDilationMatrix r k ε⁻¹))
  intro x
  rw [verticalDilationLinear_comp_apply, inv_mul_cancel₀ hε, verticalDilationLinear_one_apply]

/-- Common nonzero vertical dilation multiplies every intersection volume by its determinant factor. -/
theorem volume_two_verticalDilation_images (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (S T : Set (AffineAxisSpace r k)) :
    volume ((Matrix.toLin' (verticalDilationMatrix r k ε)) '' S ∩
      (Matrix.toLin' (verticalDilationMatrix r k ε)) '' T) =
        ENNReal.ofReal (|ε| ^ verticalExponent r k) * volume (S ∩ T) := by
  rw [← Set.image_inter (verticalDilationLinear_injective r k ε hε), volume_verticalDilation_image]

#print axioms verticalDilationMatrix_moment
#print axioms verticalDilationMatrix_mul
#print axioms verticalDilationMatrix_one
#print axioms det_verticalDilationMatrix
#print axioms volume_verticalDilation_image
#print axioms verticalDilationMatrix_vectorAffine
#print axioms verticalDilationLinear_comp_apply
#print axioms verticalDilationLinear_injective
#print axioms volume_two_verticalDilation_images

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
