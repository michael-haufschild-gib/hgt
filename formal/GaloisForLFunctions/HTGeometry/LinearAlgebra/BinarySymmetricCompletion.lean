import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryQuadraticGraphs
import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryAlternatingCompletion

/-!
# Binary matching completion for symmetric matrices

Canonical alternating correction commutes with every zero-diagonal perturbation.
In even dimension it preserves determinants. Consequently every symmetric binary
matrix admits a nonsingular perturbation along any fixed matching, extending
alternating matching completion to arbitrary diagonal data.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix
variable {ι : Type*}

/-- Zero-diagonal perturbations commute with canonical alternating correction. -/
theorem binaryAlternatingRepair_add_zeroDiagonal (M N : Matrix ι ι (ZMod 2))
    (hN : (fun i => N i i) = 0) :
    binaryAlternatingRepair (M + N) = binaryAlternatingRepair M + N := by
  have hd : (fun i => (M + N) i i) = fun i => M i i := by
    funext i
    change M i i + N i i = M i i
    rw [show N i i = 0 from congrFun hN i, add_zero]
  rw [binaryAlternatingRepair, hd, binaryAlternatingRepair]
  abel

variable [Fintype ι] [DecidableEq ι]

/-- Alternating binary matrices are symmetric. -/
theorem IsAlternatingMatrix.isSymm_binary {M : Matrix ι ι (ZMod 2)}
    (hM : IsAlternatingMatrix M) : M.IsSymm :=
  ((binaryGraph_isQuadraticLagrangian_iff M).mp hM.graph_isQuadraticLagrangian).1

/-- Every matched perturbation has the same determinant before and after canonical repair. -/
theorem det_binaryMatching_repair (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2))
    (hM : M.IsSymm) (ε : ι → ZMod 2) :
    (binaryAlternatingRepair M + matchingPerturbation ε).det =
      (M + matchingPerturbation ε).det := by
  have hP := isAlternatingMatrix_matchingPerturbation ε
  have hs : (M + matchingPerturbation ε).IsSymm := by
    change (M + matchingPerturbation ε)ᵀ = M + matchingPerturbation ε
    rw [transpose_add, hM, hP.isSymm_binary]
  have he : Fintype.card (Fin 2 × ι) % 2 = 0 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    omega
  have h := det_binaryAlternatingRepair (M + matchingPerturbation ε) hs
  rwa [binaryAlternatingRepair_add_zeroDiagonal M _ hP.diagonal_zero, if_pos he] at h

/-- Every symmetric binary matrix admits a nonsingular perturbation along a fixed matching. -/
theorem exists_binary_symmetric_matching_completion
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) (hM : M.IsSymm) :
    ∃ ε : ι → ZMod 2, (M + matchingPerturbation ε).det ≠ 0 := by
  obtain ⟨ε, _, hε⟩ := exists_binary_matching_completion (binaryAlternatingRepair M)
    (isAlternatingMatrix_binaryAlternatingRepair M hM)
  exact ⟨ε, by rwa [det_binaryMatching_repair M hM ε] at hε⟩

/-- Arbitrary off-diagonal data and diagonal entries admit nonsingular matched completion. -/
theorem exists_binary_symmetric_model_matching_completion
    (B : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) (z : Fin 2 × ι → ZMod 2) :
    ∃ ε : ι → ZMod 2,
      (B + Bᵀ + diagonal z + matchingPerturbation ε).det ≠ 0 := by
  apply exists_binary_symmetric_matching_completion
  change (B + Bᵀ + diagonal z)ᵀ = B + Bᵀ + diagonal z
  rw [transpose_add, transpose_add, transpose_transpose, diagonal_transpose, add_comm Bᵀ B]

#print axioms binaryAlternatingRepair_add_zeroDiagonal
#print axioms det_binaryMatching_repair
#print axioms exists_binary_symmetric_matching_completion
#print axioms exists_binary_symmetric_model_matching_completion
end GaloisForLFunctions.HTGeometry.LinearAlgebra
