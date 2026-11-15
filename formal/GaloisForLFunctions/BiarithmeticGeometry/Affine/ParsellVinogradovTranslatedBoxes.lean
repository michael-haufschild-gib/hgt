import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovScaledFrames
import GaloisForLFunctions.BiarithmeticGeometry.Affine.CoordinateCubeTranslations

/-!
# Sharp overlap of arbitrarily translated covering boxes

At nonzero scale the complete covering frame is surjective, so every
ambient translation is the image of an input cube center. Uniformity in
those centers transfers the sharp scaled overlap estimate directly.
At scale zero translation preserves the zero volume of each image.
-/

open MeasureTheory Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- A covering-frame cube with an arbitrary translation in the ambient moment space. -/
def scaledAffineBox (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (a : AffineAxisSpace r k) : Set (AffineAxisSpace r k) :=
  translatedLinearCube (Matrix.toLin' (scaledAffineMatrix r k ε δ t)) a 1

/-- The explicit inverse dilation and inverse shear reach every ambient center at nonzero scale. -/
theorem scaledAffineLinear_surjective (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    Function.Surjective (Matrix.toLin' (scaledAffineMatrix r k ε δ t)) := by
  intro y
  refine ⟨Matrix.toLin' (verticalDilationMatrix r k ε⁻¹)
    (Matrix.toLin' (vectorAffineMatrix r k (-(ε • δ)) (-t)) y), ?_⟩
  rw [scaledAffineLinear_apply, verticalDilationLinear_comp_apply,
    mul_inv_cancel₀ hε, verticalDilationLinear_one_apply]
  simp only [vectorAffineLinear_comp_apply, add_neg_cancel, vectorAffineLinear_zero_apply]

/-- An ambient center in the image of the frame is exactly an input cube center. -/
theorem scaledAffineBox_at_image (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (c : AffineAxisSpace r k) :
    scaledAffineBox r k ε δ t (Matrix.toLin' (scaledAffineMatrix r k ε δ t) c) =
      scaledAffineImageCube r k ε δ t c :=
  translatedLinearCube_at_image _ c 1

/-- Every translated covering box is an input-centered frame cube at nonzero scale. -/
theorem exists_scaledAffineBox_center (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (a : AffineAxisSpace r k) :
    ∃ c : AffineAxisSpace r k, scaledAffineBox r k ε δ t a = scaledAffineImageCube r k ε δ t c := by
  obtain ⟨c, hc⟩ := scaledAffineLinear_surjective r k ε hε δ t a
  refine ⟨c, ?_⟩
  rw [← hc, scaledAffineBox_at_image]

/-- At zero scale, arbitrary ambient translation preserves the collapsed image's zero volume. -/
theorem volume_scaledAffineBox_zero (r k : ℕ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (a : AffineAxisSpace r (k + 1)) :
    volume (scaledAffineBox r (k + 1) 0 δ t a) = 0 := by
  rw [scaledAffineBox, volume_translatedLinearCube]
  exact volume_scaledAffineImageCube_zero r k δ t 0

private theorem volume_two_scaledAffineBoxes_zero (r k : ℕ) (δ η : Fin (r + 1) → ℝ)
    (t s : ℝ) (a b : AffineAxisSpace r (k + 1)) :
    volume (scaledAffineBox r (k + 1) 0 δ t a ∩ scaledAffineBox r (k + 1) 0 η s b) = 0 :=
  le_antisymm ((measure_mono Set.inter_subset_left).trans_eq
    (volume_scaledAffineBox_zero r k δ t a)) bot_le

/-- The sharp binomial power controls all translated boxes, uniformly over every real scale. -/
theorem exists_uniform_translated_scaledAffine_euclidean_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 1)),
      volume (scaledAffineBox r (k + 1) ε δ t a ∩ scaledAffineBox r (k + 1) ε η s b) ≤
        ENNReal.ofReal (|ε| ^ verticalExponent r (k + 1) * C /
          (1 + euclideanNorm (δ - η)) ^ axisExponent r (k + 1)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_scaledAffine_euclidean_decay r k
  refine ⟨C, hC, fun ε δ η t s a b => ?_⟩
  by_cases hε : ε = 0
  · subst ε
    rw [volume_two_scaledAffineBoxes_zero]
    exact bot_le
  · obtain ⟨c, hc⟩ := exists_scaledAffineBox_center r (k + 1) ε hε δ t a
    obtain ⟨d, hd⟩ := exists_scaledAffineBox_center r (k + 1) ε hε η s b
    rw [hc, hd]
    exact h ε δ η t s c d

/-- The covering-box dimension-plus-one estimate holds with arbitrary ambient centers and shifts. -/
theorem exists_uniform_translated_scaledAffine_dimension_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 2)),
      volume (scaledAffineBox r (k + 2) ε δ t a ∩ scaledAffineBox r (k + 2) ε η s b) ≤
        ENNReal.ofReal (|ε| ^ verticalExponent r (k + 2) * C /
          (1 + euclideanNorm (δ - η)) ^ (r + 3)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_scaledAffine_dimension_decay r k
  refine ⟨C, hC, fun ε δ η t s a b => ?_⟩
  by_cases hε : ε = 0
  · subst ε
    rw [volume_two_scaledAffineBoxes_zero]
    exact bot_le
  · obtain ⟨c, hc⟩ := exists_scaledAffineBox_center r (k + 2) ε hε δ t a
    obtain ⟨d, hd⟩ := exists_scaledAffineBox_center r (k + 2) ε hε η s b
    rw [hc, hd]
    exact h ε δ η t s c d

/-- The exact sharp power range survives both anisotropic scaling and arbitrary ambient translations. -/
theorem bounded_translated_scaledAffine_euclidean_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 1)),
      (1 + euclideanNorm (δ - η)) ^ p *
        (volume (scaledAffineBox r (k + 1) ε δ t a ∩
          scaledAffineBox r (k + 1) ε η s b)).toReal ≤
            C * |ε| ^ verticalExponent r (k + 1)) ↔ p ≤ (axisExponent r (k + 1) : ℝ) := by
  constructor
  · rintro ⟨C, h⟩
    apply (bounded_scaledAffine_euclidean_iff r k p).mp
    refine ⟨C, fun ε δ η t s a b => ?_⟩
    simpa only [scaledAffineBox_at_image] using h ε δ η t s
      (Matrix.toLin' (scaledAffineMatrix r (k + 1) ε δ t) a)
      (Matrix.toLin' (scaledAffineMatrix r (k + 1) ε η s) b)
  · intro hp
    obtain ⟨C, h⟩ := (bounded_scaledAffine_euclidean_iff r k p).mpr hp
    refine ⟨C, fun ε δ η t s a b => ?_⟩
    by_cases hε : ε = 0
    · subst ε
      simp only [volume_two_scaledAffineBoxes_zero, ENNReal.toReal_zero, mul_zero,
        abs_zero, zero_pow (Nat.ne_of_gt (verticalExponent_pos r k)), le_refl]
    · obtain ⟨c, hc⟩ := exists_scaledAffineBox_center r (k + 1) ε hε δ t a
      obtain ⟨d, hd⟩ := exists_scaledAffineBox_center r (k + 1) ε hε η s b
      rw [hc, hd]
      exact h ε δ η t s c d

#print axioms scaledAffineLinear_surjective
#print axioms scaledAffineBox_at_image
#print axioms exists_scaledAffineBox_center
#print axioms volume_scaledAffineBox_zero
#print axioms exists_uniform_translated_scaledAffine_euclidean_decay
#print axioms exists_uniform_translated_scaledAffine_dimension_decay
#print axioms bounded_translated_scaledAffine_euclidean_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
