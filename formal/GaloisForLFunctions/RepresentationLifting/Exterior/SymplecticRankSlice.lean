import GaloisForLFunctions.HTGeometry.LinearAlgebra.BlockTriangularRank
import GaloisForLFunctions.HTGeometry.LinearAlgebra.AlternatingMatrixRank

/-!
# Exact transverse slices at a symplectic block

A unitriangular congruence separates a standard symplectic head from its
Schur complement. Rank drops are therefore exactly the rank drops of the
smaller alternating form; the transverse coordinate change is reversible.
-/

open Matrix
namespace GaloisForLFunctions.RepresentationLifting.Exterior
noncomputable section
variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- Standard symplectic matrix, with its inverse given by its negative. -/
def symplecticHead : Matrix (ι ⊕ ι) (ι ⊕ ι) K := fromBlocks 0 1 (-1) 0

omit [Fintype ι] in
lemma symplecticHead_transpose : (symplecticHead (K := K) (ι := ι))ᵀ = -symplecticHead := by
  simp only [symplecticHead, fromBlocks_transpose, transpose_zero, transpose_one,
    transpose_neg, fromBlocks_neg, neg_zero, neg_neg]

lemma symplecticHead_square :
    symplecticHead (K := K) (ι := ι) * symplecticHead = -1 := by
  simp only [symplecticHead, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
    Matrix.mul_one, zero_add, add_zero]
  have h : fromBlocks (1 : Matrix ι ι K) 0 0 (1 : Matrix ι ι K) = 1 := fromBlocks_one
  simpa only [fromBlocks_neg, neg_zero] using congrArg Neg.neg h

lemma symplecticHead_isUnit : IsUnit (symplecticHead (K := K) (ι := ι)) := by
  refine ⟨⟨symplecticHead, -symplecticHead, ?_, ?_⟩, rfl⟩ <;>
    simp only [Matrix.mul_neg, Matrix.neg_mul, symplecticHead_square, neg_neg]

/-- The trailing block after elimination of the symplectic head. -/
def symplecticSlice (B : Matrix (ι ⊕ ι) κ K) (C : Matrix κ κ K) : Matrix κ κ K :=
  C - Bᵀ * symplecticHead * B

/-- The congruence matrix eliminating the off-diagonal rectangle. -/
def symplecticEliminator (B : Matrix (ι ⊕ ι) κ K) :
    Matrix ((ι ⊕ ι) ⊕ κ) ((ι ⊕ ι) ⊕ κ) K :=
  fromBlocks 1 (symplecticHead * B) 0 1

lemma symplecticEliminator_det (B : Matrix (ι ⊕ ι) κ K) :
    (symplecticEliminator B).det = 1 := by
  rw [symplecticEliminator, det_fromBlocks_zero₂₁, det_one, det_one, one_mul]

/-- Explicit congruence, valid for every trailing matrix and every coupling. -/
theorem symplecticSlice_congruence (B : Matrix (ι ⊕ ι) κ K) (C : Matrix κ κ K) :
    (symplecticEliminator B)ᵀ * fromBlocks symplecticHead B (-Bᵀ) C *
      symplecticEliminator B = fromBlocks symplecticHead 0 0 (symplecticSlice B C) := by
  unfold symplecticEliminator symplecticSlice
  rw [fromBlocks_transpose, transpose_mul, symplecticHead_transpose]
  simp only [transpose_one, transpose_zero, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero]
  have h₁ : symplecticHead (K := K) * (symplecticHead * B) + B = 0 := by
    rw [← Matrix.mul_assoc, symplecticHead_square, Matrix.neg_mul, Matrix.one_mul, neg_add_cancel]
  have h₂ : Bᵀ * -symplecticHead * symplecticHead + -Bᵀ = 0 := by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, symplecticHead_square, Matrix.mul_neg, Matrix.mul_one, neg_neg,
      add_neg_cancel]
  rw [h₁, h₂, Matrix.zero_mul, zero_add]
  congr 1
  rw [Matrix.mul_neg, Matrix.neg_mul]
  abel

/-- The transverse coordinate change has a polynomial inverse. -/
def symplecticSliceEquiv (B : Matrix (ι ⊕ ι) κ K) : Matrix κ κ K ≃ Matrix κ κ K where
  toFun := symplecticSlice B
  invFun S := S + Bᵀ * symplecticHead * B
  left_inv C := by dsimp [symplecticSlice]; abel
  right_inv S := by dsimp [symplecticSlice]; abel

/-- The head contributes exactly twice its half-size to the rank. -/
theorem symplecticSlice_rank (B : Matrix (ι ⊕ ι) κ K) (C : Matrix κ κ K) :
    (fromBlocks symplecticHead B (-Bᵀ) C).rank =
      2 * Fintype.card ι + (symplecticSlice B C).rank := by
  have h := congrArg Matrix.rank (symplecticSlice_congruence B C)
  have hu : IsUnit (symplecticEliminator B).det := by
    rw [symplecticEliminator_det]; exact isUnit_one
  rw [rank_mul_eq_left_of_isUnit_det _ _ hu,
    rank_mul_eq_right_of_isUnit_det _ _ (by rw [det_transpose]; exact hu)] at h
  rw [GaloisForLFunctions.HTGeometry.rank_fromBlocks_zero_upper,
    GaloisForLFunctions.HTGeometry.lowerBlockVertical, Matrix.mulVecLin_zero,
    Submodule.map_zero, sup_bot_eq, ← Matrix.rank,
    rank_of_isUnit _ symplecticHead_isUnit, Fintype.card_sum] at h
  simpa only [two_mul] using h

private lemma rank_zero_iff (C : Matrix κ κ K) : C.rank = 0 ↔ C = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  constructor
  · intro h
    ext i j
    have hv := congrArg (fun f : (κ → K) →ₗ[K] (κ → K) => f (Pi.single j 1) i) h
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using hv
  · rintro rfl
    exact Matrix.mulVecLin_zero

/-- The minimum rank is attained precisely on one explicit graph of the coupling. -/
theorem symplecticSlice_minimum_iff (B : Matrix (ι ⊕ ι) κ K) (C : Matrix κ κ K) :
    (fromBlocks symplecticHead B (-Bᵀ) C).rank = 2 * Fintype.card ι ↔
      C = Bᵀ * symplecticHead * B := by
  rw [symplecticSlice_rank, Nat.add_eq_left, rank_zero_iff, symplecticSlice, sub_eq_zero]

/-- Every prescribed smaller matrix occurs as the exact transverse slice. -/
theorem symplecticSlice_prescribed_rank (B : Matrix (ι ⊕ ι) κ K) (S : Matrix κ κ K) :
    (fromBlocks symplecticHead B (-Bᵀ) (S + Bᵀ * symplecticHead * B)).rank =
      2 * Fintype.card ι + S.rank := by
  rw [symplecticSlice_rank]
  congr 1
  congr 1
  unfold symplecticSlice
  abel

/-- The standard head is alternating, including in characteristic two. -/
lemma symplecticHead_alternating :
    GaloisForLFunctions.HTGeometry.LinearAlgebra.IsAlternatingMatrix
      (symplecticHead (K := K) (ι := ι)) := by
  intro v
  rw [symplecticHead, GaloisForLFunctions.HTGeometry.LinearAlgebra.quadratic_fromBlocks]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero]
  rw [dotProduct_neg, dotProduct_comm (v ∘ Sum.inr), add_neg_cancel]

omit [DecidableEq κ] in
/-- The transverse slice of a skew-symmetrization remains alternating. -/
theorem symplecticSlice_alternating (B : Matrix (ι ⊕ ι) κ K) (M : Matrix κ κ K) :
    GaloisForLFunctions.HTGeometry.LinearAlgebra.IsAlternatingMatrix
      (symplecticSlice B (M-Mᵀ)) := by
  intro v
  rw [symplecticSlice, Matrix.sub_mulVec, dotProduct_sub,
    GaloisForLFunctions.HTGeometry.LinearAlgebra.isAlternatingMatrix_sub_transpose M v]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose, symplecticHead_alternating, sub_zero]

/-- Rank in this alternating family changes only by even transverse increments. -/
theorem symplecticSlice_even_increment (B : Matrix (ι ⊕ ι) κ K) (M : Matrix κ κ K) :
    ∃ r : ℕ, (fromBlocks symplecticHead B (-Bᵀ) (M-Mᵀ)).rank =
      2 * (Fintype.card ι + r) := by
  obtain ⟨r, hr⟩ := (symplecticSlice_alternating B M).even_rank
  refine ⟨r, ?_⟩
  rw [symplecticSlice_rank, hr]
  omega

#print axioms symplecticSlice_rank
#print axioms symplecticSlice_minimum_iff
#print axioms symplecticSlice_prescribed_rank
#print axioms symplecticSlice_even_increment
end
end GaloisForLFunctions.RepresentationLifting.Exterior
