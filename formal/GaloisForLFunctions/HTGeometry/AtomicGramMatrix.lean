import GaloisForLFunctions.HTGeometry.EventualNegDefFromEntrywise

/-!
# The scaled atomic Gram matrix

The inserted atoms contribute a matrix of rank-one terms to the Pick Gram.  Scaled by the height
squared and evaluated at the nodes directly above the atoms, its diagonal splits into the atom's own
coefficient — exactly, with no error — and cross terms from the other atoms.

Bounding those cross terms by the same-node estimate shows the diagonal converges to the coefficient
with an explicit `O(y²)` rate.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Finset

noncomputable section

/-- The scaled atomic part of the Pick Gram matrix at the nodes above the atoms. -/
def atomicGram {d : ℕ} (a c : Fin d → ℝ) (y : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  fun l m => (y : ℂ) ^ 2 * ∑ j, (c j : ℂ) /
    (((a j : ℂ) - upperNode (a l) y) *
      ((a j : ℂ) - (starRingEnd ℂ) (upperNode (a m) y)))

/-- **The atomic diagonal splits off its own coefficient exactly.** -/
theorem atomicGram_diagonal_split {d : ℕ} (a c : Fin d → ℝ) {y : ℝ} (hy : y ≠ 0) (l : Fin d) :
    atomicGram a c y l l = (c l : ℂ) +
      ∑ j ∈ univ.erase l, (y : ℂ) ^ 2 * ((c j : ℂ) /
        (((a j : ℂ) - upperNode (a l) y) *
          ((a j : ℂ) - (starRingEnd ℂ) (upperNode (a l) y)))) := by
  classical
  rw [atomicGram, Finset.mul_sum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
  congr 1
  exact scaled_atomic_diagonal (a l) y hy (c l)

/-- **The atomic diagonal converges to the coefficient at rate `O(y²)`.**  The deviation is bounded
by the height squared times the sum of the other coefficients over their squared separations. -/
theorem norm_atomicGram_diagonal_sub_le {d : ℕ} (a c : Fin d → ℝ)
    (ha : Function.Injective a) {y : ℝ} (hy : y ≠ 0) (l : Fin d) :
    ‖atomicGram a c y l l - (c l : ℂ)‖ ≤
      ∑ j ∈ univ.erase l, y ^ 2 * ‖(c j : ℂ)‖ / (a j - a l) ^ 2 := by
  classical
  rw [atomicGram_diagonal_split a c hy l, add_sub_cancel_left]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun j hj => ?_
  have hne : a j ≠ a l := fun h => (Finset.ne_of_mem_erase hj) (ha h)
  exact norm_scaled_atomic_cross_le y hne (c j)

end

end GaloisForLFunctions.HTGeometry
