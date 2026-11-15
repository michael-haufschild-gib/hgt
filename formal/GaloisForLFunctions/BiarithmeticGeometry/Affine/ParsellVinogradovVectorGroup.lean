import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovSymmetricFrames

/-!
# The group of complete affine moment shears

The centered polynomial action is faithful. Composition of the physical
maps therefore proves the matrix group law, including vertical translations.
Unit determinant then reduces intersections of two arbitrary image sets
to the single frame at the difference of their affine parameters.
-/

open MeasureTheory Matrix
open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The horizontal moment vectors determine every ambient matrix. -/
theorem matrix_eq_of_horizontalMoment_eq (r k : ℕ)
    (M N : Matrix (AffineAxisIndex r k) (AffineAxisIndex r k) ℝ)
    (h : ∀ u z, M *ᵥ horizontalMoment r k u z = N *ᵥ horizontalMoment r k u z) : M = N := by
  apply matrix_eq_of_affineAxisMoment_eq
  intro y x z
  simpa only [horizontalMoment_eq, Fin.cons_zero, Fin.cons_succ] using h (Fin.cons x y) z

/-- All nonconstant moments vanish at the physical origin. -/
theorem horizontalMoment_zero (r k : ℕ) : horizontalMoment r k 0 0 = 0 := by
  rw [horizontalMoment_eq]
  funext a
  change fullAxisMoment r k 0 0 0 (positiveAxisIndex a) = 0
  rw [fullAxisMoment_zero]
  apply if_neg
  change a.1.val + 1 ≠ 0
  omega

/-- Complete affine shear matrices compose by addition of both parameters. -/
theorem vectorAffineMatrix_mul (r k : ℕ) (δ ε : Fin (r + 1) → ℝ) (t s : ℝ) :
    vectorAffineMatrix r k δ t * vectorAffineMatrix r k ε s =
      vectorAffineMatrix r k (δ + ε) (t + s) := by
  apply matrix_eq_of_horizontalMoment_eq
  intro u z
  rw [← Matrix.mulVec_mulVec, vectorAffineMatrix_moment, Matrix.mulVec_sub,
    vectorAffineMatrix_moment, vectorAffineMatrix_moment, vectorAffineMatrix_moment]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  have hs : (∑ i, (δ + ε) i * u i) = (∑ i, δ i * u i) + ∑ i, ε i * u i := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hs, show z + ∑ i, ε i * u i + s + ∑ i, δ i * u i + t =
    z + ((∑ i, δ i * u i) + ∑ i, ε i * u i) + (t + s) by ring,
    show s + t = t + s by ring]
  abel

/-- Zero direction and zero vertical shift give the identity ambient matrix. -/
theorem vectorAffineMatrix_zero (r k : ℕ) : vectorAffineMatrix r k 0 0 = 1 := by
  apply matrix_eq_of_horizontalMoment_eq
  intro u z
  rw [vectorAffineMatrix_moment, Matrix.one_mulVec, horizontalMoment_zero]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, sub_zero]

/-- Composition acts on every ambient vector, beyond the moment manifold. -/
theorem vectorAffineLinear_comp_apply (r k : ℕ) (δ ε : Fin (r + 1) → ℝ)
    (t s : ℝ) (x : AffineAxisSpace r k) :
    Matrix.toLin' (vectorAffineMatrix r k δ t) (Matrix.toLin' (vectorAffineMatrix r k ε s) x) =
      Matrix.toLin' (vectorAffineMatrix r k (δ + ε) (t + s)) x := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, vectorAffineMatrix_mul]

theorem vectorAffineLinear_zero_apply (r k : ℕ) (x : AffineAxisSpace r k) :
    Matrix.toLin' (vectorAffineMatrix r k 0 0) x = x := by
  rw [Matrix.toLin'_apply, vectorAffineMatrix_zero, Matrix.one_mulVec]

/-- Negating both affine parameters exchanges images and inverse images. -/
theorem vectorAffineLinear_image_eq_preimage_neg (r k : ℕ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (S : Set (AffineAxisSpace r k)) :
    (Matrix.toLin' (vectorAffineMatrix r k δ t)) '' S =
      (Matrix.toLin' (vectorAffineMatrix r k (-δ) (-t))) ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [Set.mem_preimage, vectorAffineLinear_comp_apply, neg_add_cancel,
      vectorAffineLinear_zero_apply] using hx
  · intro hy
    refine ⟨Matrix.toLin' (vectorAffineMatrix r k (-δ) (-t)) y, hy, ?_⟩
    simp only [vectorAffineLinear_comp_apply, add_neg_cancel, vectorAffineLinear_zero_apply]

/-- Every complete affine moment shear preserves outer volume on every set. -/
theorem volume_vectorAffineLinear_image (r k : ℕ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (S : Set (AffineAxisSpace r k)) :
    volume ((Matrix.toLin' (vectorAffineMatrix r k δ t)) '' S) = volume S := by
  simpa only [LinearMap.det_toLin', det_vectorAffineMatrix, abs_one, ENNReal.ofReal_one, one_mul] using
    Measure.addHaar_image_linearMap volume (Matrix.toLin' (vectorAffineMatrix r k δ t)) S

/-- Relative volume depends only on the differences of direction and vertical shift. -/
theorem volume_two_vectorAffineLinear_images (r k : ℕ) (δ ε : Fin (r + 1) → ℝ)
    (t s : ℝ) (A B : Set (AffineAxisSpace r k)) :
    volume ((Matrix.toLin' (vectorAffineMatrix r k δ t)) '' A ∩
      (Matrix.toLin' (vectorAffineMatrix r k ε s)) '' B) =
        volume (A ∩ (Matrix.toLin' (vectorAffineMatrix r k (δ - ε) (t - s))) ⁻¹' B) := by
  have hi : Function.Injective (Matrix.toLin' (vectorAffineMatrix r k δ t)) := by
    apply Function.LeftInverse.injective (g := Matrix.toLin' (vectorAffineMatrix r k (-δ) (-t)))
    intro x
    simp only [vectorAffineLinear_comp_apply, neg_add_cancel, vectorAffineLinear_zero_apply]
  have hc : (fun x => Matrix.toLin' (vectorAffineMatrix r k δ t)
      (Matrix.toLin' (vectorAffineMatrix r k (ε - δ) (s - t)) x)) =
        Matrix.toLin' (vectorAffineMatrix r k ε s) := by
    funext x
    rw [vectorAffineLinear_comp_apply, show δ + (ε - δ) = ε by abel,
      show t + (s - t) = s by ring]
  have hset : (Matrix.toLin' (vectorAffineMatrix r k δ t)) ''
      (A ∩ (Matrix.toLin' (vectorAffineMatrix r k (ε - δ) (s - t))) '' B) =
      (Matrix.toLin' (vectorAffineMatrix r k δ t)) '' A ∩
        (Matrix.toLin' (vectorAffineMatrix r k ε s)) '' B := by
    rw [Set.image_inter hi, Set.image_image, hc]
  rw [← hset, volume_vectorAffineLinear_image, vectorAffineLinear_image_eq_preimage_neg]
  simp only [neg_sub]

#print axioms matrix_eq_of_horizontalMoment_eq
#print axioms horizontalMoment_zero
#print axioms vectorAffineMatrix_mul
#print axioms vectorAffineMatrix_zero
#print axioms vectorAffineLinear_comp_apply
#print axioms vectorAffineLinear_image_eq_preimage_neg
#print axioms volume_vectorAffineLinear_image
#print axioms volume_two_vectorAffineLinear_images

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
