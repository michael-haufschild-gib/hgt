import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryAlternatingCompletion
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Nonsingular completion of binary Selmer block matrices

For arbitrary binary `A` and `z`, some diagonal perturbation `G=A+diag ε`
makes `[[G+Gᵀ,G],[Gᵀ,zzᵀ+diag z]]` nonsingular. The rank-one correction
is alternating because every binary scalar is idempotent. The existence
theorem follows from completion along a fixed matching.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The zero-diagonal correction of a binary rank-one symmetric matrix. -/
def binaryRankOneCorrection (z : ι → ZMod 2) : Matrix ι ι (ZMod 2) :=
  vecMulVec z z + diagonal z

theorem isAlternatingMatrix_binaryRankOneCorrection (z : ι → ZMod 2) :
    IsAlternatingMatrix (binaryRankOneCorrection z) := by
  intro v
  have houter : v ⬝ᵥ (vecMulVec z z *ᵥ v) = z ⬝ᵥ v := by
    rw [vecMulVec_mulVec, dotProduct_smul]
    change (v ⬝ᵥ z) * (z ⬝ᵥ v) = z ⬝ᵥ v
    rw [dotProduct_comm v z, ← sq, ZMod.pow_card]
  have hdiag : v ⬝ᵥ (diagonal z *ᵥ v) = z ⬝ᵥ v := by
    simp only [dotProduct, mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    calc
      v i * (z i * v i) = z i * (v i) ^ 2 := by ring
      _ = z i * v i := by rw [ZMod.pow_card]
  rw [binaryRankOneCorrection, add_mulVec, dotProduct_add, houter, hdiag,
    CharTwo.add_self_eq_zero]

omit [DecidableEq ι] in
private theorem dot_transpose (A : Matrix ι ι (ZMod 2)) (u v : ι → ZMod 2) :
    u ⬝ᵥ (Aᵀ *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

private theorem binarySelmer_core_alternating (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    IsAlternatingMatrix (fromBlocks (A + Aᵀ) A Aᵀ (binaryRankOneCorrection z)) := by
  intro w
  rw [quadratic_fromBlocks]
  simp only [add_mulVec, dotProduct_add]
  rw [dot_transpose A (w ∘ Sum.inl) (w ∘ Sum.inl),
    dot_transpose A (w ∘ Sum.inr) (w ∘ Sum.inl),
    isAlternatingMatrix_binaryRankOneCorrection z (w ∘ Sum.inr), add_zero,
    CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]

/-- The binary block matrix with freely chosen diagonal in its off-diagonal block. -/
def binarySelmerMatrix (A : Matrix ι ι (ZMod 2)) (z ε : ι → ZMod 2) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  let G := A + diagonal ε
  fromBlocks (G + Gᵀ) G Gᵀ (binaryRankOneCorrection z)

/-- Every binary matrix and vector admit a nonsingular Selmer block
completion. No condition on their entries is needed. -/
theorem exists_nonsingular_binarySelmerMatrix
    (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    ∃ ε : ι → ZMod 2, (binarySelmerMatrix A z ε).det ≠ 0 := by
  obtain ⟨ε, _, hdet⟩ := exists_binary_offDiagonal_completion _ (binarySelmer_core_alternating A z)
  refine ⟨ε, ?_⟩
  have hdouble : diagonal ε + diagonal ε = (0 : Matrix ι ι (ZMod 2)) := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  have hneg : -diagonal ε = diagonal ε := by
    ext i j
    exact CharTwo.neg_eq _
  have htop : (A + diagonal ε) + (A + diagonal ε)ᵀ = A + Aᵀ := by
    rw [transpose_add, diagonal_transpose]
    calc
      (A + diagonal ε) + (Aᵀ + diagonal ε) =
          (A + Aᵀ) + (diagonal ε + diagonal ε) := by abel
      _ = A + Aᵀ := by rw [hdouble, add_zero]
  have heq : binarySelmerMatrix A z ε =
      fromBlocks (A + Aᵀ) A Aᵀ (binaryRankOneCorrection z) +
        fromBlocks 0 (diagonal ε) (-diagonal ε) 0 := by
    dsimp only [binarySelmerMatrix]
    rw [htop, transpose_add, diagonal_transpose, fromBlocks_add, hneg, add_zero, add_zero]
  rw [heq]
  exact hdet

#print axioms isAlternatingMatrix_binaryRankOneCorrection
#print axioms exists_nonsingular_binarySelmerMatrix

end GaloisForLFunctions.HTGeometry.LinearAlgebra
