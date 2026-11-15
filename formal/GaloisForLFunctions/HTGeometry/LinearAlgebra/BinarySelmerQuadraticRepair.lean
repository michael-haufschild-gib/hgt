import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryQuadraticGraphs
import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinarySelmerDictionary
import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinarySelmerCompletion

/-!
# Canonical correction of symmetric binary descent matrices

The alternating Selmer completion is the diagonal outer-product correction of
the symmetric descent matrix. This identifies the exact change in kernel and
rank. Even ambient dimension makes determinants equal throughout the diagonal
completion family, transferring nonsingular completion to the symmetric model.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The descent dictionary matrix is symmetric for arbitrary inputs. -/
theorem isSymm_binarySelmerSymmetric (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    (binarySelmerSymmetric A z).IsSymm := by
  change (fromBlocks (A + Aᵀ) Aᵀ A (diagonal z))ᵀ =
    fromBlocks (A + Aᵀ) Aᵀ A (diagonal z)
  rw [fromBlocks_transpose, transpose_add, transpose_transpose, diagonal_transpose,
    add_comm Aᵀ A]

omit [Fintype ι] in
/-- The only quadratic obstruction is the lower diagonal vector. -/
theorem diagonal_binarySelmerSymmetric (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    (fun i => binarySelmerSymmetric A z i i) = Sum.elim 0 z := by
  funext i
  cases i with
  | inl i =>
      change A i i + A i i = 0
      exact CharTwo.add_self_eq_zero _
  | inr i =>
      change diagonal z i i = z i
      simp

/-- The existing alternating completion is exactly the canonical rank-one repair of
the symmetric descent matrix. -/
theorem binaryAlternatingRepair_binarySelmerSymmetric
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    binaryAlternatingRepair (binarySelmerSymmetric A z) = binarySelmerMatrix Aᵀ z 0 := by
  have houter : vecMulVec (Sum.elim (0 : ι → ZMod 2) z) (Sum.elim 0 z) =
      fromBlocks (0 : Matrix ι ι (ZMod 2)) 0 0 (vecMulVec z z) := by
    ext (i | i) (j | j) <;> simp [vecMulVec, fromBlocks]
  rw [binaryAlternatingRepair, diagonal_binarySelmerSymmetric, houter]
  dsimp only [binarySelmerSymmetric, binarySelmerMatrix]
  rw [diagonal_zero, add_zero, transpose_transpose, fromBlocks_add]
  simp only [add_zero]
  rw [add_comm A Aᵀ, add_comm (diagonal z) (vecMulVec z z)]
  rfl

/-- The alternating Selmer matrix discards precisely the odd rank unit. -/
theorem rank_binarySelmerMatrix_eq_even_part
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    (binarySelmerMatrix Aᵀ z 0).rank =
      (binarySelmerSymmetric A z).rank - (binarySelmerSymmetric A z).rank % 2 := by
  rw [← binaryAlternatingRepair_binarySelmerSymmetric]
  exact rank_binaryAlternatingRepair _ (isSymm_binarySelmerSymmetric A z)

/-- The correction preserves every solution of the symmetric descent equations. -/
theorem ker_binarySelmerSymmetric_le_completion
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    (binarySelmerSymmetric A z).mulVecLin.ker ≤ (binarySelmerMatrix Aᵀ z 0).mulVecLin.ker := by
  rw [← binaryAlternatingRepair_binarySelmerSymmetric]
  exact ker_le_binaryAlternatingRepair _ (isSymm_binarySelmerSymmetric A z)

/-- Kernel growth records the original rank parity exactly. -/
theorem nullity_binarySelmerMatrix_eq_nullity_add_parity
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    finrank (ZMod 2) (binarySelmerMatrix Aᵀ z 0).mulVecLin.ker =
      finrank (ZMod 2) (binarySelmerSymmetric A z).mulVecLin.ker +
        (binarySelmerSymmetric A z).rank % 2 := by
  rw [← binaryAlternatingRepair_binarySelmerSymmetric]
  exact nullity_binaryAlternatingRepair _ (isSymm_binarySelmerSymmetric A z)

/-- The uncorrected graph is a quadratic Lagrangian exactly when the lower diagonal vanishes. -/
theorem binarySelmerSymmetricGraph_isQuadraticLagrangian_iff
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    IsQuadraticLagrangian hyperbolicMatrixQuadratic (binarySelmerSymmetric A z).mulVecLin.graph ↔
      z = 0 := by
  rw [binarySymmetricGraph_isQuadraticLagrangian_iff _ (isSymm_binarySelmerSymmetric A z),
    diagonal_binarySelmerSymmetric]
  constructor
  · intro h
    funext i
    exact congrFun h (Sum.inr i)
  · intro h
    subst z
    rfl

/-- The two matrix models have graph defect exactly one when correction is needed. -/
theorem binarySelmerSymmetric_completion_defect
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    intersectionCodimension (binarySelmerSymmetric A z).mulVecLin.graph
      (binarySelmerMatrix Aᵀ z 0).mulVecLin.graph = if z = 0 then 0 else 1 := by
  rw [← binaryAlternatingRepair_binarySelmerSymmetric, binaryRepairGraph_defect,
    diagonal_binarySelmerSymmetric]
  have heq : Sum.elim (0 : ι → ZMod 2) z = 0 ↔ z = 0 := by
    constructor
    · intro h
      funext i
      exact congrFun h (Sum.inr i)
    · intro h
      subst z
      rfl
  simp only [heq]

#print axioms rank_binarySelmerMatrix_eq_even_part
#print axioms ker_binarySelmerSymmetric_le_completion
#print axioms nullity_binarySelmerMatrix_eq_nullity_add_parity
#print axioms binarySelmerSymmetricGraph_isQuadraticLagrangian_iff
#print axioms binarySelmerSymmetric_completion_defect
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In even dimension the canonical correction preserves nonsingularity. -/
theorem binarySelmerMatrix_det_ne_zero_iff_symmetric
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    (binarySelmerMatrix Aᵀ z 0).det ≠ 0 ↔ (binarySelmerSymmetric A z).det ≠ 0 := by
  rw [← binaryAlternatingRepair_binarySelmerSymmetric,
    binaryAlternatingRepair_det_ne_zero_iff _ (isSymm_binarySelmerSymmetric A z)]
  have he : Fintype.card (ι ⊕ ι) % 2 = 0 := by rw [Fintype.card_sum]; omega
  simp only [he, and_true]

/-- The two binary determinants agree exactly, since their only nonzero value is one. -/
theorem det_binarySelmerMatrix_eq_symmetric
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    (binarySelmerMatrix Aᵀ z 0).det = (binarySelmerSymmetric A z).det := by
  rw [← binaryAlternatingRepair_binarySelmerSymmetric,
    det_binaryAlternatingRepair _ (isSymm_binarySelmerSymmetric A z)]
  have he : Fintype.card (ι ⊕ ι) % 2 = 0 := by rw [Fintype.card_sum]; omega
  exact if_pos he

/-- Determinant preservation holds throughout the full diagonal-completion family. -/
theorem det_binarySelmerMatrix_eq_symmetric_diagonal
    (A : Matrix ι ι (ZMod 2)) (z ε : ι → ZMod 2) :
    (binarySelmerMatrix Aᵀ z ε).det = (binarySelmerSymmetric (A + diagonal ε) z).det := by
  have h := det_binarySelmerMatrix_eq_symmetric (A + diagonal ε) z
  have heq : binarySelmerMatrix (A + diagonal ε)ᵀ z 0 = binarySelmerMatrix Aᵀ z ε := by
    simp only [binarySelmerMatrix, transpose_add, diagonal_transpose, diagonal_zero, add_zero]
  rwa [heq] at h

/-- Arbitrary symmetric descent matrices admit a nonsingular diagonal completion. -/
theorem exists_nonsingular_binarySelmerSymmetric
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    ∃ ε : ι → ZMod 2, (binarySelmerSymmetric (A + diagonal ε) z).det ≠ 0 := by
  obtain ⟨ε, hε⟩ := exists_nonsingular_binarySelmerMatrix Aᵀ z
  exact ⟨ε, by rwa [det_binarySelmerMatrix_eq_symmetric_diagonal] at hε⟩

#print axioms det_binarySelmerMatrix_eq_symmetric_diagonal
#print axioms exists_nonsingular_binarySelmerSymmetric
end GaloisForLFunctions.HTGeometry.LinearAlgebra
