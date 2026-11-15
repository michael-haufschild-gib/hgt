import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryMatchingParity
import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinarySelmerQuadraticRepair

/-!
# Completion parity for binary descent matrices

Diagonal changes of the descent matrix are matching perturbations after
reindexing. Their determinant sum is one, so nonsingular completions have odd
cardinality for arbitrary binary input data. The alternating correction
preserves every determinant and hence both singular and nonsingular counts.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A diagonal change of the descent matrix is a matching perturbation in paired coordinates. -/
theorem binarySelmerSymmetric_diagonal_submatrix
    (A : Matrix ι ι (ZMod 2)) (z ε : ι → ZMod 2) :
    (binarySelmerSymmetric (A + diagonal ε) z).submatrix (twoLayerEquiv ι) (twoLayerEquiv ι) =
      (binarySelmerSymmetric A z).submatrix (twoLayerEquiv ι) (twoLayerEquiv ι) +
        matchingPerturbation ε := by
  classical
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> by_cases hij : i = j <;>
    simp [binarySelmerSymmetric, twoLayerEquiv, matchingPerturbation,
      blockDiagonal_apply, fromBlocks, alternatingPair, hij,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero]

/-- Determinants of the native diagonal family agree with paired matching determinants. -/
theorem det_binarySelmerSymmetric_diagonal_matching
    (A : Matrix ι ι (ZMod 2)) (z ε : ι → ZMod 2) :
    (binarySelmerSymmetric (A + diagonal ε) z).det =
      ((binarySelmerSymmetric A z).submatrix (twoLayerEquiv ι) (twoLayerEquiv ι) +
        matchingPerturbation ε).det := by
  rw [← binarySelmerSymmetric_diagonal_submatrix]
  exact (det_submatrix_equiv_self (twoLayerEquiv ι) _).symm

/-- The determinant sum over every diagonal completion of the symmetric descent model is one. -/
theorem sum_det_binarySelmerSymmetric_diagonal
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    (∑ ε : ι → ZMod 2, (binarySelmerSymmetric (A + diagonal ε) z).det) = 1 := by
  simp only [det_binarySelmerSymmetric_diagonal_matching]
  exact sum_binaryMatching_det_eq_one _ ((isSymm_binarySelmerSymmetric A z).submatrix _)

/-- Arbitrary binary descent data have an odd number of nonsingular diagonal completions. -/
theorem odd_card_nonsingular_binarySelmerSymmetric
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    Odd (Fintype.card {ε : ι → ZMod 2 //
      (binarySelmerSymmetric (A + diagonal ε) z).det ≠ 0}) := by
  classical
  let e : {ε : ι → ZMod 2 // (binarySelmerSymmetric (A + diagonal ε) z).det ≠ 0} ≃
      {ε : ι → ZMod 2 //
        ((binarySelmerSymmetric A z).submatrix (twoLayerEquiv ι) (twoLayerEquiv ι) +
          matchingPerturbation ε).det ≠ 0} :=
    Equiv.subtypeEquivRight (fun ε => by rw [det_binarySelmerSymmetric_diagonal_matching])
  rw [Fintype.card_congr e]
  exact odd_card_binaryMatching_nonsingular _ ((isSymm_binarySelmerSymmetric A z).submatrix _)

/-- The alternating and symmetric Selmer families have the same determinant sum. -/
theorem sum_det_binarySelmerMatrix
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    (∑ ε : ι → ZMod 2, (binarySelmerMatrix A z ε).det) = 1 := by
  have hd (ε : ι → ZMod 2) : (binarySelmerMatrix A z ε).det =
      (binarySelmerSymmetric (Aᵀ + diagonal ε) z).det := by
    simpa only [transpose_transpose] using det_binarySelmerMatrix_eq_symmetric_diagonal Aᵀ z ε
  simpa only [hd] using sum_det_binarySelmerSymmetric_diagonal Aᵀ z

/-- Every alternating Selmer completion family has an odd number of nonsingular members. -/
theorem odd_card_nonsingular_binarySelmerMatrix
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    Odd (Fintype.card {ε : ι → ZMod 2 // (binarySelmerMatrix A z ε).det ≠ 0}) := by
  classical
  let e : {ε : ι → ZMod 2 // (binarySelmerMatrix A z ε).det ≠ 0} ≃
      {ε : ι → ZMod 2 // (binarySelmerSymmetric (Aᵀ + diagonal ε) z).det ≠ 0} :=
    Equiv.subtypeEquivRight (fun ε => by
      have hd : (binarySelmerMatrix A z ε).det =
          (binarySelmerSymmetric (Aᵀ + diagonal ε) z).det := by
        simpa only [transpose_transpose] using det_binarySelmerMatrix_eq_symmetric_diagonal Aᵀ z ε
      rw [hd])
  rw [Fintype.card_congr e]
  exact odd_card_nonsingular_binarySelmerSymmetric Aᵀ z

#print axioms sum_det_binarySelmerSymmetric_diagonal
#print axioms odd_card_nonsingular_binarySelmerSymmetric
#print axioms sum_det_binarySelmerMatrix
#print axioms odd_card_nonsingular_binarySelmerMatrix

/-- When there is a diagonal parameter, the singular symmetric completions also have odd count. -/
theorem odd_card_singular_binarySelmerSymmetric [Nonempty ι]
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    Odd (Fintype.card {ε : ι → ZMod 2 //
      (binarySelmerSymmetric (A + diagonal ε) z).det = 0}) := by
  classical
  let e : {ε : ι → ZMod 2 // (binarySelmerSymmetric (A + diagonal ε) z).det = 0} ≃
      {ε : ι → ZMod 2 //
        ((binarySelmerSymmetric A z).submatrix (twoLayerEquiv ι) (twoLayerEquiv ι) +
          matchingPerturbation ε).det = 0} :=
    Equiv.subtypeEquivRight (fun ε => by rw [det_binarySelmerSymmetric_diagonal_matching])
  rw [Fintype.card_congr e]
  exact odd_card_binaryMatching_singular _ ((isSymm_binarySelmerSymmetric A z).submatrix _)

/-- Singular alternating Selmer completions have odd count whenever the parameter set is nonempty. -/
theorem odd_card_singular_binarySelmerMatrix [Nonempty ι]
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    Odd (Fintype.card {ε : ι → ZMod 2 // (binarySelmerMatrix A z ε).det = 0}) := by
  classical
  let e : {ε : ι → ZMod 2 // (binarySelmerMatrix A z ε).det = 0} ≃
      {ε : ι → ZMod 2 // (binarySelmerSymmetric (Aᵀ + diagonal ε) z).det = 0} :=
    Equiv.subtypeEquivRight (fun ε => by
      have hd : (binarySelmerMatrix A z ε).det =
          (binarySelmerSymmetric (Aᵀ + diagonal ε) z).det := by
        simpa only [transpose_transpose] using det_binarySelmerMatrix_eq_symmetric_diagonal Aᵀ z ε
      rw [hd])
  rw [Fintype.card_congr e]
  exact odd_card_singular_binarySelmerSymmetric Aᵀ z

#print axioms odd_card_singular_binarySelmerSymmetric
#print axioms odd_card_singular_binarySelmerMatrix
end GaloisForLFunctions.HTGeometry.LinearAlgebra
