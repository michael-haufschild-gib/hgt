import GaloisForLFunctions.HTGeometry.FiniteRankDeterminantCompletion
import GaloisForLFunctions.RHTower.MertensClockRelativeDeterminant
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Actual operator Fredholm determinants of finite coordinate blocks

The trace-class operator determinant agrees exactly with its finite coordinate
block determinant. Strictly triangular blocks therefore have determinant one,
without a small-norm assumption or a replacement by a formal matrix model.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt ContinuousLinearMap OrderDual
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [DecidableEq ι]

theorem opTrace_eq_hsTraceDiag_coordMatrix (b : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T) :
    opTrace T = hsTraceDiag (RHTower.coordMatrix b T) := by
  rw [RHTower.opTrace_eq_tsum_basis_of_memSchattenClass_one hT b, hsTraceDiag]
  apply tsum_congr
  intro i
  rw [RHTower.coordMatrix_apply]

theorem fredholmDetOp_eq_det_block_of_support (b : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T) (s : Finset ι)
    (hs : ∀ p, p ∉ s ×ˢ s → RHTower.coordMatrix b T p = 0) :
    RHTower.fredholmDetOp b T = (1 + blockMatrix (RHTower.coordMatrix b T) s).det := by
  have hK := isHS_of_support_subset (s ×ˢ s) hs
  have h := det_one_sub_smul_blockMatrix hK hs (-1)
  rw [RHTower.fredholmDetOp, RHTower.det2Op, opTrace_eq_hsTraceDiag_coordMatrix b hT]
  simpa only [completedDet2, neg_one_smul, sub_neg_eq_add, neg_one_mul, neg_neg] using h.symm

theorem fredholmDetOp_eq_one_of_strict_lower [LinearOrder ι] (b : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T) (s : Finset ι)
    (hs : ∀ p, p ∉ s ×ˢ s → RHTower.coordMatrix b T p = 0)
    (hLower : ∀ i j, i ≤ j → RHTower.coordMatrix b T (i, j) = 0) :
    RHTower.fredholmDetOp b T = 1 := by
  rw [fredholmDetOp_eq_det_block_of_support b hT s hs]
  have htri : (1 + blockMatrix (RHTower.coordMatrix b T) s).BlockTriangular toDual := by
    intro i j hij
    have hlt : (i : ι) < (j : ι) := hij
    have hne : i ≠ j := by intro h; exact (ne_of_lt hlt) (congrArg Subtype.val h)
    simp only [Matrix.add_apply, Matrix.one_apply, if_neg hne, blockMatrix,
      hLower _ _ hlt.le, add_zero]
  rw [Matrix.det_of_lowerTriangular _ htri]
  apply Finset.prod_eq_one
  intro i _
  simp only [Matrix.add_apply, Matrix.one_apply, ite_true, blockMatrix,
    hLower _ _ le_rfl, add_zero]

end
end GaloisForLFunctions.HTGeometry
