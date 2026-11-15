import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovVerticalDilation
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovVectorRelativeFrames

/-!
# Sharp overlap of anisotropically scaled affine moment frames

Moving vertical dilation to the outside normalizes the horizontal shear
direction and divides the vertical shift by the scale. Common dilation
then contributes exactly its determinant factor to overlap volume.
At scale zero every positive-degree image has zero volume, so the final
bounds and sharp weighted-power criterion hold for every real scale.
-/

open MeasureTheory Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The covering-frame matrix with horizontal direction `ε • δ` and physical vertical shift `t`. -/
def scaledAffineMatrix (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    Matrix (AffineAxisIndex r k) (AffineAxisIndex r k) ℝ :=
  vectorAffineMatrix r k (ε • δ) t * verticalDilationMatrix r k ε

theorem det_scaledAffineMatrix (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    (scaledAffineMatrix r k ε δ t).det = ε ^ verticalExponent r k := by
  rw [scaledAffineMatrix, Matrix.det_mul, det_vectorAffineMatrix, det_verticalDilationMatrix, one_mul]

/-- Every nonzero scale moves to the outside after normalizing the physical vertical shift. -/
theorem scaledAffineMatrix_eq_dilation_mul (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    scaledAffineMatrix r k ε δ t =
      verticalDilationMatrix r k ε * vectorAffineMatrix r k δ (t / ε) := by
  have ht : ε * (t / ε) = t := (mul_comm _ _).trans (div_mul_cancel₀ t hε)
  simpa only [scaledAffineMatrix, ht] using
    (verticalDilationMatrix_vectorAffine r k ε δ (t / ε)).symm

theorem scaledAffineLinear_apply (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (x : AffineAxisSpace r k) :
    Matrix.toLin' (scaledAffineMatrix r k ε δ t) x =
      Matrix.toLin' (vectorAffineMatrix r k (ε • δ) t)
        (Matrix.toLin' (verticalDilationMatrix r k ε) x) := by
  simp only [scaledAffineMatrix, Matrix.toLin'_apply, Matrix.mulVec_mulVec]

/-- A coordinate cube in the scaled covering frame. -/
def scaledAffineImageCube (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (a : AffineAxisSpace r k) : Set (AffineAxisSpace r k) :=
  (Matrix.toLin' (scaledAffineMatrix r k ε δ t)) '' centeredCube a 1

/-- A scaled cube is the common vertical dilation of its normalized affine-frame cube. -/
theorem scaledAffineImageCube_eq_dilation_image (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (a : AffineAxisSpace r k) :
    scaledAffineImageCube r k ε δ t a =
      (Matrix.toLin' (verticalDilationMatrix r k ε)) '' vectorAffineImageCube r k δ (t / ε) a := by
  unfold scaledAffineImageCube vectorAffineImageCube
  rw [scaledAffineMatrix_eq_dilation_mul r k ε hε, Set.image_image]
  congr 1
  funext x
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]

/-- At zero scale the positive-degree covering frame has zero image volume. -/
theorem volume_scaledAffineImageCube_zero (r k : ℕ) (δ : Fin (r + 1) → ℝ)
    (t : ℝ) (a : AffineAxisSpace r (k + 1)) :
    volume (scaledAffineImageCube r (k + 1) 0 δ t a) = 0 := by
  have hA : verticalExponent r (k + 1) ≠ 0 := Nat.ne_of_gt (verticalExponent_pos r k)
  simpa only [scaledAffineImageCube, LinearMap.det_toLin', det_scaledAffineMatrix,
    zero_pow hA, abs_zero, ENNReal.ofReal_zero, zero_mul] using
    Measure.addHaar_image_linearMap volume
      (Matrix.toLin' (scaledAffineMatrix r (k + 1) 0 δ t)) (centeredCube a 1)

/-- Exact relative-overlap scaling holds for every real scale in every positive degree. -/
theorem volume_two_scaledAffineImageCubes (r k : ℕ) (ε : ℝ) (δ η : Fin (r + 1) → ℝ)
    (t s : ℝ) (a b : AffineAxisSpace r (k + 1)) :
    volume (scaledAffineImageCube r (k + 1) ε δ t a ∩
      scaledAffineImageCube r (k + 1) ε η s b) =
        ENNReal.ofReal (|ε| ^ verticalExponent r (k + 1)) *
          volume (vectorAffineOverlap r (k + 1) (δ - η) (t / ε - s / ε) a b) := by
  by_cases hε : ε = 0
  · subst ε
    have hz : volume (scaledAffineImageCube r (k + 1) 0 δ t a ∩
        scaledAffineImageCube r (k + 1) 0 η s b) = 0 :=
      le_antisymm ((measure_mono Set.inter_subset_left).trans_eq
        (volume_scaledAffineImageCube_zero r k δ t a)) bot_le
    rw [hz, abs_zero, zero_pow (Nat.ne_of_gt (verticalExponent_pos r k)), ENNReal.ofReal_zero, zero_mul]
  · rw [scaledAffineImageCube_eq_dilation_image r (k + 1) ε hε,
      scaledAffineImageCube_eq_dilation_image r (k + 1) ε hε,
      volume_two_verticalDilation_images r (k + 1) ε hε, volume_two_vectorAffineImageCubes]

/-- Scaled affine cubes satisfy the sharp Euclidean overlap bound with the exact volume factor. -/
theorem exists_uniform_scaledAffine_euclidean_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 1)),
      volume (scaledAffineImageCube r (k + 1) ε δ t a ∩
        scaledAffineImageCube r (k + 1) ε η s b) ≤
          ENNReal.ofReal (|ε| ^ verticalExponent r (k + 1) * C /
            (1 + euclideanNorm (δ - η)) ^ axisExponent r (k + 1)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_vectorAffine_euclidean_overlap_decay r (k + 1)
  refine ⟨C, hC, fun ε δ η t s a b => ?_⟩
  rw [volume_two_scaledAffineImageCubes]
  calc
    _ ≤ ENNReal.ofReal (|ε| ^ verticalExponent r (k + 1)) *
        ENNReal.ofReal (C / (1 + euclideanNorm (δ - η)) ^ axisExponent r (k + 1)) :=
      mul_le_mul_right (h (δ - η) (t / ε - s / ε) a b) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (abs_nonneg ε) _)]
      congr 1
      ring

/-- Degree at least two supplies the dimension-plus-one power used for covering boxes. -/
theorem exists_uniform_scaledAffine_dimension_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 2)),
      volume (scaledAffineImageCube r (k + 2) ε δ t a ∩
        scaledAffineImageCube r (k + 2) ε η s b) ≤
          ENNReal.ofReal (|ε| ^ verticalExponent r (k + 2) * C /
            (1 + euclideanNorm (δ - η)) ^ (r + 3)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_vectorAffine_dimension_overlap_decay r k
  refine ⟨C, hC, fun ε δ η t s a b => ?_⟩
  rw [volume_two_scaledAffineImageCubes]
  calc
    _ ≤ ENNReal.ofReal (|ε| ^ verticalExponent r (k + 2)) *
        ENNReal.ofReal (C / (1 + euclideanNorm (δ - η)) ^ (r + 3)) :=
      mul_le_mul_right (h (δ - η) (t / ε - s / ε) a b) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (abs_nonneg ε) _)]
      congr 1
      ring

/-- After removing the exact volume factor, the sharp Euclidean power threshold is unchanged by scaling. -/
theorem bounded_scaledAffine_euclidean_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 1)),
      (1 + euclideanNorm (δ - η)) ^ p *
        (volume (scaledAffineImageCube r (k + 1) ε δ t a ∩
          scaledAffineImageCube r (k + 1) ε η s b)).toReal ≤
            C * |ε| ^ verticalExponent r (k + 1)) ↔ p ≤ (axisExponent r (k + 1) : ℝ) := by
  constructor
  · rintro ⟨C, h⟩
    have hb : ∃ C : ℝ, ∀ (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
        (a b : AffineAxisSpace r (k + 1)),
        (1 + euclideanNorm (δ - η)) ^ p *
          (volume (vectorAffineImageCube r (k + 1) δ t a ∩
            vectorAffineImageCube r (k + 1) η s b)).toReal ≤ C := by
      refine ⟨C, fun δ η t s a b => ?_⟩
      simpa only [scaledAffineImageCube, scaledAffineMatrix, one_smul,
        verticalDilationMatrix_one, mul_one, abs_one, one_pow, vectorAffineImageCube] using
        h 1 δ η t s a b
    simpa only [axisExponent_eq_binomial_sum] using
      (bounded_two_vectorAffine_euclidean_iff r (k + 1) p).mp hb
  · intro hp
    have hp' := hp
    rw [axisExponent_eq_binomial_sum] at hp'
    obtain ⟨C, h⟩ := (bounded_vectorAffine_euclidean_overlap_iff r (k + 1) p).mpr hp'
    refine ⟨C, fun ε δ η t s a b => ?_⟩
    rw [volume_two_scaledAffineImageCubes, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (abs_nonneg ε) _)]
    calc
      _ = |ε| ^ verticalExponent r (k + 1) *
          ((1 + euclideanNorm (δ - η)) ^ p *
            (volume (vectorAffineOverlap r (k + 1) (δ - η) (t / ε - s / ε) a b)).toReal) := by ring
      _ ≤ |ε| ^ verticalExponent r (k + 1) * C :=
        mul_le_mul_of_nonneg_left (h (δ - η) (t / ε - s / ε) a b) (pow_nonneg (abs_nonneg ε) _)
      _ = _ := mul_comm _ _

#print axioms det_scaledAffineMatrix
#print axioms scaledAffineMatrix_eq_dilation_mul
#print axioms scaledAffineLinear_apply
#print axioms scaledAffineImageCube_eq_dilation_image
#print axioms volume_scaledAffineImageCube_zero
#print axioms volume_two_scaledAffineImageCubes
#print axioms exists_uniform_scaledAffine_euclidean_decay
#print axioms exists_uniform_scaledAffine_dimension_decay
#print axioms bounded_scaledAffine_euclidean_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
