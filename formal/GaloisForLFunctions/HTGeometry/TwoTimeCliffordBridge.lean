import GaloisForLFunctions.HTGeometry.TwoTimeQuadratic
import GaloisForLFunctions.HTGeometry.SpinTorsionChannel

/-!
# The two-negative-direction form as a chiral Clifford square

The flat Euclidean chiral Clifford representation already realizes a negative
norm square. On a two-coordinate plane, its square is exactly the diagonal
two-negative-direction form. This pointwise symbol has no nonzero null vector.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

/-- Include a coordinate pair in the flat Euclidean four-space Clifford model. -/
noncomputable def twoTimeCliffordEmbedding (p : ℝ × ℝ) : SeibergWitten.FourSpace :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm ![p.1, p.2, 0, 0]

/-- The Euclidean square of the embedding is the negative of the two-time form. -/
theorem twoTimeCliffordEmbedding_inner (p : ℝ × ℝ) :
    inner ℝ (twoTimeCliffordEmbedding p) (twoTimeCliffordEmbedding p) =
      p.1 ^ (2 : ℕ) + p.2 ^ (2 : ℕ) := by
  rw [SeibergWitten.flatFourCoordinate_inner]
  simp [SeibergWitten.flatFourCoordinate, twoTimeCliffordEmbedding]
  ring

/-- The existing chiral Clifford square realizes the two-negative-direction
quadratic form exactly. -/
theorem twoTimeClifford_square (p : ℝ × ℝ) :
    (SeibergWitten.flatCliffordMinus (twoTimeCliffordEmbedding p)).comp
        (SeibergWitten.flatCliffordPlus (twoTimeCliffordEmbedding p)) =
      ((twoTimeQuadratic p : ℝ) : ℂ) • LinearMap.id := by
  rw [SeibergWitten.flatClifford_sameDirection_positive,
    twoTimeCliffordEmbedding_inner]
  simp [twoTimeQuadratic]

end GaloisForLFunctions.HTGeometry
