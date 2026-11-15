import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovVectorGroup
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovDegreeDecay

/-!
# Sharp relative overlap for complete affine moment frames

Two affine frames reduce exactly to their relative direction and shift.
The Euclidean binomial decay estimate is therefore uniform over both
frames and both cube centers. Restricting the second frame to the identity
also transfers the sharpness statement without losing any power.
-/

open MeasureTheory
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- A coordinate cube in the complete affine moment frame. -/
def vectorAffineImageCube (r k : ℕ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (a : AffineAxisSpace r k) : Set (AffineAxisSpace r k) :=
  (Matrix.toLin' (vectorAffineMatrix r k δ t)) '' centeredCube a 1

/-- Two complete frame cubes have exactly the overlap volume of their relative frame. -/
theorem volume_two_vectorAffineImageCubes (r k : ℕ) (δ ε : Fin (r + 1) → ℝ)
    (t s : ℝ) (a b : AffineAxisSpace r k) :
    volume (vectorAffineImageCube r k δ t a ∩ vectorAffineImageCube r k ε s b) =
      volume (vectorAffineOverlap r k (δ - ε) (t - s) a b) :=
  volume_two_vectorAffineLinear_images r k δ ε t s (centeredCube a 1) (centeredCube b 1)

/-- The sharp binomial power controls the Euclidean separation of two arbitrary affine frames. -/
theorem exists_uniform_two_vectorAffine_euclidean_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ ε : Fin (r + 1) → ℝ) (t s : ℝ) (a b : AffineAxisSpace r k),
      volume (vectorAffineImageCube r k δ t a ∩ vectorAffineImageCube r k ε s b) ≤
        ENNReal.ofReal (C / (1 + euclideanNorm (δ - ε)) ^ axisExponent r k) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_vectorAffine_euclidean_overlap_decay r k
  refine ⟨C, hC, fun δ ε t s a b => ?_⟩
  rw [volume_two_vectorAffineImageCubes]
  exact h (δ - ε) (t - s) a b

/-- The exact binomial threshold remains sharp for two independently chosen affine frames. -/
theorem bounded_two_vectorAffine_euclidean_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (δ ε : Fin (r + 1) → ℝ) (t s : ℝ) (a b : AffineAxisSpace r k),
      (1 + euclideanNorm (δ - ε)) ^ p *
        (volume (vectorAffineImageCube r k δ t a ∩ vectorAffineImageCube r k ε s b)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  constructor
  · rintro ⟨C, h⟩
    apply (bounded_vectorAffine_euclidean_overlap_iff r k p).mp
    refine ⟨C, fun δ t a b => ?_⟩
    simpa only [volume_two_vectorAffineImageCubes, sub_zero] using h δ 0 t 0 a b
  · intro hp
    obtain ⟨C, h⟩ := (bounded_vectorAffine_euclidean_overlap_iff r k p).mpr hp
    refine ⟨C, fun δ ε t s a b => ?_⟩
    rw [volume_two_vectorAffineImageCubes]
    exact h (δ - ε) (t - s) a b

/-- Degree at least two gives the dimension-plus-one power used in the covering argument. -/
theorem exists_uniform_two_vectorAffine_dimension_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ ε : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 2)),
      volume (vectorAffineImageCube r (k + 2) δ t a ∩ vectorAffineImageCube r (k + 2) ε s b) ≤
        ENNReal.ofReal (C / (1 + euclideanNorm (δ - ε)) ^ (r + 3)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_vectorAffine_dimension_overlap_decay r k
  refine ⟨C, hC, fun δ ε t s a b => ?_⟩
  rw [volume_two_vectorAffineImageCubes]
  exact h (δ - ε) (t - s) a b

#print axioms volume_two_vectorAffineImageCubes
#print axioms exists_uniform_two_vectorAffine_euclidean_decay
#print axioms bounded_two_vectorAffine_euclidean_iff
#print axioms exists_uniform_two_vectorAffine_dimension_decay

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
