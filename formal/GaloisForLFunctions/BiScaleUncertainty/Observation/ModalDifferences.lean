import GaloisForLFunctions.HTGeometry.FiniteModalTransfer

/-!
# Offset removal and exact modal observability

The first-difference identification in arXiv:2611.13534, Corollary 3.2,
extends to every finite modal packet. Each difference multiplies mode
`i` by `node i - 1`. The resulting Hankel determinant gives the exact
criterion for preserving observable modes after removing a constant.
-/

open scoped BigOperators
open _root_.HTGeometry

namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section

variable {K : Type*} [CommRing K] {d : ℕ}

/-- Consecutive differences of an observation sequence. -/
def forwardDifference (f : ℕ → K) (n : ℕ) : K := f (n + 1) - f n

/-- Repeated differencing, with order zero equal to the original sequence. -/
def repeatedDifference (r : ℕ) (f : ℕ → K) : ℕ → K :=
  match r with
  | 0 => f
  | r + 1 => forwardDifference (repeatedDifference r f)

/-- An unknown constant offset disappears from the first difference. -/
theorem forwardDifference_offset (c : K) (f : ℕ → K) :
    forwardDifference (fun n => c + f n) = forwardDifference f := by
  funext n
  simp only [forwardDifference]
  ring

/-- Differencing is the diagonal modal filter with transfer value `node - 1`. -/
theorem forwardDifference_modal (weight node : Fin d → K) :
    forwardDifference (finiteModalSequence weight node) =
      finiteModalTransferSequence (fun i => node i - 1) weight node := by
  funext n
  simp only [forwardDifference, finiteModalTransferSequence, finiteModalSequence,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

/-- Every difference order has an explicit transfer polynomial. -/
theorem repeatedDifference_modal (r : ℕ) (weight node : Fin d → K) :
    repeatedDifference r (finiteModalSequence weight node) =
      finiteModalTransferSequence (fun i => (node i - 1) ^ r) weight node := by
  induction r with
  | zero => simp only [repeatedDifference, pow_zero, finiteModalTransferSequence, mul_one]
  | succ r ih =>
    rw [repeatedDifference, ih, finiteModalTransferSequence, forwardDifference_modal]
    unfold finiteModalTransferSequence
    congr 1
    funext i
    dsimp only
    rw [pow_succ, mul_assoc]

/-- The maximal determinant changes by the product of all modal differences. -/
theorem det_forwardDifference_offset (c : K) (weight node : Fin d → K) :
    (algebraicHankelMatrix
      (forwardDifference (fun n => c + finiteModalSequence weight node n)) d).det =
      (algebraicHankelMatrix (finiteModalSequence weight node) d).det *
        ∏ i, (node i - 1) := by
  rw [forwardDifference_offset, forwardDifference_modal,
    det_algebraicHankelMatrix_finiteModalTransferSequence]

/-- The complete determinant law for any difference order. -/
theorem det_repeatedDifference_modal (r : ℕ) (weight node : Fin d → K) :
    (algebraicHankelMatrix (repeatedDifference r (finiteModalSequence weight node)) d).det =
      (algebraicHankelMatrix (finiteModalSequence weight node) d).det *
        ∏ i, (node i - 1) ^ r := by
  rw [repeatedDifference_modal, det_algebraicHankelMatrix_finiteModalTransferSequence]

section Field
variable {F : Type*} [Field F]

/-- Offset removal preserves the maximal observed rank exactly when no constant mode occurs. -/
theorem det_forwardDifference_offset_ne_zero_iff (c : F) (weight node : Fin d → F) :
    (algebraicHankelMatrix
      (forwardDifference (fun n => c + finiteModalSequence weight node n)) d).det ≠ 0 ↔
      (algebraicHankelMatrix (finiteModalSequence weight node) d).det ≠ 0 ∧
        ∀ i, node i ≠ 1 := by
  rw [det_forwardDifference_offset, mul_ne_zero_iff, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, forall_const, sub_ne_zero]

/-- After offset removal, the next oversized block remains singular. -/
theorem det_forwardDifference_offset_succ (c : F) (weight node : Fin d → F) :
    (algebraicHankelMatrix
      (forwardDifference (fun n => c + finiteModalSequence weight node n)) (d + 1)).det = 0 := by
  rw [forwardDifference_offset, forwardDifference_modal, finiteModalTransferSequence]
  exact det_algebraicHankelMatrix_finiteModalSequence_succ_eq_zero _ _

end Field

#print axioms repeatedDifference_modal
#print axioms det_repeatedDifference_modal
#print axioms det_forwardDifference_offset_ne_zero_iff
#print axioms det_forwardDifference_offset_succ

end
end GaloisForLFunctions.BiScaleUncertainty.Observation
