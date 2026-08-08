import GaloisForLFunctions.HTGeometry.ExpPolyGeneralHeight
import GaloisForLFunctions.HTGeometry.LogJetHeightThreeNonvanishing

/-!
# The three-map polynomial-coefficient cascade has differential order three

The chain from the head determinant to the exact order is height-independent, and the head
determinant at height three is the logarithmic `2×2` determinant, which is nonzero because the
cross term of the newest level outgrows the Wronskian of the level below.

The data of a polynomial-coefficient cascade satisfies the hypotheses: `polyQ` is nonzero and
nonconstant at every positive index, and `polyV` is linear there.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {A : ℕ → Polynomial ℂ} {c d : ℕ → ℂ}

theorem natDegree_polyV_succ (d : ℕ → ℂ) (k : ℕ) : (polyV d (k + 1)).natDegree = 1 := by
  rw [polyV_succ]
  exact Polynomial.natDegree_X_sub_C (d k)

/-- **The head determinant at height three is nonzero.** -/
theorem headJetJacobian_two_det_ne_zero (hA : ∀ j, 1 ≤ (A j).natDegree) :
    (headJetJacobian (polyQ A d) (polyV d) 2).det ≠ 0 := by
  refine headJetJacobian_det_ne_zero_of_log (polyV d) (polyQ_ne_zero hA) 1 ?_
  refine logJetJacobian_one_det_ne_zero (polyV d) (polyQ_ne_zero hA)
    (one_le_natDegree_polyQ_succ hA 0) ?_ (one_le_natDegree_polyQ_succ hA 1) ?_
  · exact le_of_eq (natDegree_polyV_succ d 0)
  · exact natDegree_polyV_succ d 1

/-- **A three-map cascade of first-order linear entire maps with polynomial coefficients has
differential order exactly three.** -/
theorem exactDifferentialOrder_expPolyCascade_three
    (hc : ∀ k, c k ≠ 0) (hA : ∀ k, 1 ≤ (A k).natDegree) :
    ExactDifferentialOrder (entireCascade (expPoly A c d) 3) 3 :=
  exactDifferentialOrder_expPolyCascade hc hA (m := 2) (headJetJacobian_two_det_ne_zero hA)

end GaloisForLFunctions.HTGeometry
