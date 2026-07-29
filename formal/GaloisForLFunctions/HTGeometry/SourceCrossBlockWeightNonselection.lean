import GaloisForLFunctions.HTGeometry.MinimalSourceQuadraticSquareIsotropy

/-!
# Total reciprocal-square weight does not select a higher cross block

In a balanced higher-rank source grading, the cross-polarity block is classified up to independent
unitary frame changes on its two sides. Its determinant modulus is an invariant of that
biunitary equivalence.

This file gives two invertible two-by-two cross blocks with the same total reciprocal-square trace
but different determinant modulus. Hence odd support, full rank, and one total positive weight do
not select the calibrated singular spectrum.

The result is unconditional finite matrix algebra. It is a standard singular-value obstruction,
not new mathematics or physics.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

set_option maxRecDepth 4096

/-- Equivalence of a cross block under independent unitary source and target frame changes. -/
def BiunitarilyEquivalent
    (B C : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ U V : Matrix (Fin 2) (Fin 2) ℂ,
    Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ C = U * B * V

/-- Biunitary equivalence preserves squared determinant modulus. -/
theorem detNormSq_eq_of_biunitarilyEquivalent
    {B C : Matrix (Fin 2) (Fin 2) ℂ}
    (h : BiunitarilyEquivalent B C) :
    star C.det * C.det = star B.det * B.det := by
  obtain ⟨U, V, hU, hV, rfl⟩ := h
  have hUdet := congrArg Matrix.det hU
  have hVdet := congrArg Matrix.det hV
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hUdet hVdet
  simp only [Matrix.det_mul]
  rw [star_mul, star_mul]
  calc
    star V.det * (star B.det * star U.det) *
          (U.det * B.det * V.det) =
        (star U.det * U.det) * (star B.det * B.det) *
          (star V.det * V.det) := by ring
    _ = star B.det * B.det := by rw [hUdet, hVdet, one_mul, mul_one]

/-- First full-rank cross block with total squared weight `65`. -/
def firstWeightedCrossBlock : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 8]

/-- Second full-rank cross block with the same total squared weight `65`. -/
def secondWeightedCrossBlock : Matrix (Fin 2) (Fin 2) ℂ :=
  !![4, 0; 0, 7]

theorem firstWeightedCrossBlock_det :
    firstWeightedCrossBlock.det = 8 := by
  norm_num [firstWeightedCrossBlock, Matrix.det_fin_two]

theorem secondWeightedCrossBlock_det :
    secondWeightedCrossBlock.det = 28 := by
  norm_num [secondWeightedCrossBlock, Matrix.det_fin_two]

/-- The two cross blocks have equal total reciprocal-square trace. -/
theorem weightedCrossBlocks_equal_totalSquare :
    (firstWeightedCrossBlockᴴ * firstWeightedCrossBlock).trace =
      (secondWeightedCrossBlockᴴ * secondWeightedCrossBlock).trace := by
  simp [firstWeightedCrossBlock, secondWeightedCrossBlock, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp [starRingEnd_apply]
  norm_num

/--
**Higher-rank weight nonselection.** Equal total positive weight and nonzero determinant do not
select a cross block up to independent unitary frame changes.
-/
theorem weightedCrossBlocks_not_biunitarilyEquivalent :
    ¬ BiunitarilyEquivalent firstWeightedCrossBlock secondWeightedCrossBlock := by
  intro h
  have hdet := detNormSq_eq_of_biunitarilyEquivalent h
  rw [firstWeightedCrossBlock_det, secondWeightedCrossBlock_det] at hdet
  norm_num at hdet

end GaloisForLFunctions.HTGeometry
