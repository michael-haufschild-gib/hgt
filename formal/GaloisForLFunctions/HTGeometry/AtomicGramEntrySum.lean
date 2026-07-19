import GaloisForLFunctions.HTGeometry.ScaledAtomicFarTerms

/-!
# The atomic Gram entry as a sum of scaled terms

Each entry of the scaled atomic Gram is a sum over the atoms of individually scaled terms, so the
five case estimates apply termwise and combine by summation.

For heights at most one the two decay rates unify: a term that is `O(y²)` is in particular `O(|y|)`,
so a single linear rate covers every off-diagonal term and the summation needs no case split on the
rate.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

/-- The atomic Gram entry is the sum of the individually scaled atom terms. -/
theorem atomicGram_eq_sum {d : ℕ} (a c : Fin d → ℝ) (y : ℝ) (l m : Fin d) :
    atomicGram a c y l m = ∑ j, (y : ℂ) ^ 2 * ((c j : ℂ) /
      (((a j : ℂ) - upperNode (a l) y) *
        ((a j : ℂ) - (starRingEnd ℂ) (upperNode (a m) y)))) := by
  rw [atomicGram, Finset.mul_sum]

/-- For heights at most one the quadratic rate is dominated by the linear rate. -/
theorem sq_le_abs_of_abs_le_one {y : ℝ} (hy : |y| ≤ 1) : y ^ 2 ≤ |y| := by
  have h : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  rw [h, sq]
  nlinarith [abs_nonneg y, hy]

/-- **A termwise bound gives an entrywise bound.**  If every atom's scaled term is bounded by a
linear-in-height quantity, the whole entry is bounded by their sum. -/
theorem norm_atomicGram_le_of_termwise {d : ℕ} (a c : Fin d → ℝ) (y : ℝ) (l m : Fin d)
    (B : Fin d → ℝ)
    (hB : ∀ j, ‖(y : ℂ) ^ 2 * ((c j : ℂ) /
      (((a j : ℂ) - upperNode (a l) y) *
        ((a j : ℂ) - (starRingEnd ℂ) (upperNode (a m) y))))‖ ≤ B j) :
    ‖atomicGram a c y l m‖ ≤ ∑ j, B j := by
  rw [atomicGram_eq_sum]
  exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => hB j)

end

end GaloisForLFunctions.HTGeometry
