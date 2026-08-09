import GaloisForLFunctions.HTGeometry.PeelInduction
import GaloisForLFunctions.HTGeometry.ExpPolyGeneralHeight

/-!
# The unit-cost law at every height

The logarithmic Jacobian is nonsingular at every height, so the head determinant is, so the
observability step of the cascade order theorem is discharged for every length.

A cascade of first-order linear entire maps with polynomial coefficients therefore has differential
order exactly its length — the card's law, unconditionally, for an explicit infinite family at every
height.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {A : ℕ → Polynomial ℂ} {c d : ℕ → ℂ}

/-- The product law of a polynomial-coefficient cascade has linear terminal factors. -/
theorem polyV_linear (d : ℕ → ℂ) (j : ℕ) :
    ∃ α β : ℂ, α ≠ 0 ∧ polyV d (j + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β := by
  refine ⟨1, -(d j), one_ne_zero, ?_⟩
  rw [polyV_succ, map_neg, map_one]
  ring

/-- **The head determinant of a polynomial-coefficient cascade is nonzero at every height.** -/
theorem headJetJacobian_det_ne_zero_all (hA : ∀ j, 1 ≤ (A j).natDegree) (m : ℕ) :
    (headJetJacobian (polyQ A d) (polyV d) m).det ≠ 0 := by
  match m with
  | 0 =>
      rw [Matrix.det_fin_zero]
      exact one_ne_zero
  | (n + 1) =>
      refine headJetJacobian_det_ne_zero_of_log (polyV d) (polyQ_ne_zero hA) n ?_
      exact logJetJacobian_det_ne_zero (polyQ_ne_zero hA)
        (fun j => one_le_natDegree_polyQ_succ hA j) (fun j => polyV_linear d j) n

/-- **The unit-cost law at every height.**  A cascade of `m+1` first-order linear entire maps with
polynomial coefficients has differential order exactly `m+1`. -/
theorem exactDifferentialOrder_expPolyCascade_all
    (hc : ∀ k, c k ≠ 0) (hA : ∀ k, 1 ≤ (A k).natDegree) (m : ℕ) :
    ExactDifferentialOrder (entireCascade (expPoly A c d) (m + 1)) (m + 1) :=
  exactDifferentialOrder_expPolyCascade hc hA (headJetJacobian_det_ne_zero_all hA m)

end GaloisForLFunctions.HTGeometry
