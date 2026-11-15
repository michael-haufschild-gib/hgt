import GaloisForLFunctions.HTGeometry.LinearAlgebra.AlternatingMatrixRank
import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinarySelmerCompletion

/-!
# Parity throughout the binary Selmer matrix family

Every diagonal choice gives even rank and even nullity. Thus nonsingular completion
belongs to a family whose kernel dimensions can change only by even integers.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every binary rank-one correction has even rank. -/
theorem even_rank_binaryRankOneCorrection (z : ι → ZMod 2) :
    Even (binaryRankOneCorrection z).rank :=
  (isAlternatingMatrix_binaryRankOneCorrection z).even_rank

/-- Every diagonal choice has even rank, without conditions on the initial matrix. -/
theorem even_rank_binarySelmerMatrix (A : Matrix ι ι (ZMod 2)) (z ε : ι → ZMod 2) :
    Even (binarySelmerMatrix A z ε).rank :=
  (isAlternatingMatrix_binarySelmerMatrix A z ε).even_rank

/-- Every diagonal choice has even kernel dimension. -/
theorem even_nullity_binarySelmerMatrix (A : Matrix ι ι (ZMod 2)) (z ε : ι → ZMod 2) :
    Even (finrank (ZMod 2) (binarySelmerMatrix A z ε).mulVecLin.ker) := by
  have h := (isAlternatingMatrix_binarySelmerMatrix A z ε).nullity_mod_two
  rw [Fintype.card_sum] at h
  refine ⟨finrank (ZMod 2) (binarySelmerMatrix A z ε).mulVecLin.ker / 2, ?_⟩
  omega

/-- Every binary Selmer kernel has cardinality a power of four. -/
theorem card_binarySelmerKernel_eq_four_pow
    (A : Matrix ι ι (ZMod 2)) (z ε : ι → ZMod 2) :
    ∃ k : ℕ, Nat.card (binarySelmerMatrix A z ε).mulVecLin.ker = 4 ^ k := by
  obtain ⟨k, hk⟩ := even_nullity_binarySelmerMatrix A z ε
  refine ⟨k, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card,
    ZMod.card, hk, ← two_mul, pow_mul]
  rfl

#print axioms even_rank_binaryRankOneCorrection
#print axioms even_rank_binarySelmerMatrix
#print axioms even_nullity_binarySelmerMatrix
#print axioms card_binarySelmerKernel_eq_four_pow
end GaloisForLFunctions.HTGeometry.LinearAlgebra
