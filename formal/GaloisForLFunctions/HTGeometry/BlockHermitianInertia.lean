import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Inertia of heterogeneous Hermitian block diagonals

This module supplies the finite-dimensional block-diagonal inertia identity used by
Schur-complement certificates.  It works for two unrelated finite index types and therefore does
not require padding either block with artificial zero coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex

noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Splitting a finite filtered cardinality across a sum type. -/
theorem card_filter_sum (P : m ⊕ n → Prop) [DecidablePred P] :
    ({i | P i} : Finset (m ⊕ n)).card =
      ({i | P (Sum.inl i)} : Finset m).card +
        ({j | P (Sum.inr j)} : Finset n).card := by
  rw [← Fintype.card_subtype P,
    ← Fintype.card_subtype (fun i : m => P (Sum.inl i)),
    ← Fintype.card_subtype (fun j : n => P (Sum.inr j)),
    Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]

variable [DecidableEq m] [DecidableEq n]

/-- The positive, negative, and null indices add across a heterogeneous Hermitian block
diagonal. -/
theorem inertia_fromBlocks_zero {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    hermPosIndex (Matrix.fromBlocks A 0 0 D) = hermPosIndex A + hermPosIndex D ∧
      hermNegIndex (Matrix.fromBlocks A 0 0 D) = hermNegIndex A + hermNegIndex D ∧
        hermNullIndex (Matrix.fromBlocks A 0 0 D) = hermNullIndex A + hermNullIndex D := by
  let U : Matrix (m ⊕ n) (m ⊕ n) ℂ := Matrix.fromBlocks
    (hA.eigenvectorUnitary : Matrix m m ℂ) 0 0 (hD.eigenvectorUnitary : Matrix n n ℂ)
  let μ : m ⊕ n → ℝ := Sum.elim hA.eigenvalues hD.eigenvalues
  have hU : IsUnit U := by
    rw [show U = Matrix.fromBlocks (hA.eigenvectorUnitary : Matrix m m ℂ) 0 0
      (hD.eigenvectorUnitary : Matrix n n ℂ) from rfl]
    exact Matrix.isUnit_fromBlocks_zero₂₁.mpr
      ⟨isUnit_eigenvectorUnitary hA, isUnit_eigenvectorUnitary hD⟩
  have hcong : Uᴴ * Matrix.fromBlocks A 0 0 D * U =
      Matrix.diagonal (fun i : m ⊕ n => ((μ i : ℝ) : ℂ)) := by
    dsimp [U, μ]
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [conjTranspose_mul_mul_eigenvectorUnitary hA,
      conjTranspose_mul_mul_eigenvectorUnitary hD, Matrix.fromBlocks_diagonal]
    congr 1
    funext i
    cases i <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · calc
      hermPosIndex (Matrix.fromBlocks A 0 0 D) =
          hermPosIndex (Uᴴ * Matrix.fromBlocks A 0 0 D * U) :=
        (posIndex_conjugate _ hU).symm
      _ = hermPosIndex (Matrix.diagonal (fun i : m ⊕ n => ((μ i : ℝ) : ℂ))) :=
        congrArg hermPosIndex hcong
      _ = ({i | 0 < μ i} : Finset (m ⊕ n)).card := posIndex_diagonal μ
      _ = ({i | 0 < hA.eigenvalues i} : Finset m).card +
          ({j | 0 < hD.eigenvalues j} : Finset n).card := by
        rw [card_filter_sum (fun i => 0 < μ i)]
        simp [μ]
      _ = hermPosIndex A + hermPosIndex D := by
        rw [← posIndex_eq_card_pos_eigenvalues hA, ← posIndex_eq_card_pos_eigenvalues hD]
  · calc
      hermNegIndex (Matrix.fromBlocks A 0 0 D) =
          hermNegIndex (Uᴴ * Matrix.fromBlocks A 0 0 D * U) :=
        (negIndex_conjugate _ hU).symm
      _ = hermNegIndex (Matrix.diagonal (fun i : m ⊕ n => ((μ i : ℝ) : ℂ))) :=
        congrArg hermNegIndex hcong
      _ = ({i | μ i < 0} : Finset (m ⊕ n)).card := negIndex_diagonal μ
      _ = ({i | hA.eigenvalues i < 0} : Finset m).card +
          ({j | hD.eigenvalues j < 0} : Finset n).card := by
        rw [card_filter_sum (fun i => μ i < 0)]
        simp [μ]
      _ = hermNegIndex A + hermNegIndex D := by
        rw [← negIndex_eq_card_neg_eigenvalues hA, ← negIndex_eq_card_neg_eigenvalues hD]
  · calc
      hermNullIndex (Matrix.fromBlocks A 0 0 D) =
          hermNullIndex (Uᴴ * Matrix.fromBlocks A 0 0 D * U) :=
        (nullIndex_conjugate _ hU).symm
      _ = hermNullIndex (Matrix.diagonal (fun i : m ⊕ n => ((μ i : ℝ) : ℂ))) :=
        congrArg hermNullIndex hcong
      _ = ({i | μ i = 0} : Finset (m ⊕ n)).card := nullIndex_diagonal μ
      _ = ({i | hA.eigenvalues i = 0} : Finset m).card +
          ({j | hD.eigenvalues j = 0} : Finset n).card := by
        rw [card_filter_sum (fun i => μ i = 0)]
        simp [μ]
      _ = hermNullIndex A + hermNullIndex D := by
        rw [← nullIndex_eq_card_zero_eigenvalues hA, ← nullIndex_eq_card_zero_eigenvalues hD]

end

end GaloisForLFunctions.HTGeometry
