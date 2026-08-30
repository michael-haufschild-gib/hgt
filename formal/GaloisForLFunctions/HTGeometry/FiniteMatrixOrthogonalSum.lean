import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite positive-definite block sums

An indexed block-diagonal family and a binary orthogonal sum preserve positive definiteness,
including when an index type is empty.  These elementary facts let real and doubled-complex
archimedean blocks be assembled before pulling the resulting form back to canonical coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Classical Matrix

noncomputable section

/-- Move a real rectangular matrix across the Euclidean pairing. -/
theorem star_mulVec_dotProduct_rect_real
    {r c : Type*} [Fintype r] [Fintype c]
    (P : Matrix r c ℝ) (x : c → ℝ) (y : r → ℝ) :
    star (P.mulVec x) ⬝ᵥ y = star x ⬝ᵥ Pᴴ.mulVec y := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring

/-- A real congruence evaluates the source form on the changed vector. -/
theorem star_dotProduct_real_congr_mulVec
    {r c : Type*} [Fintype r] [Fintype c]
    (M : Matrix r r ℝ) (P : Matrix r c ℝ) (x : c → ℝ) :
    star x ⬝ᵥ (Pᴴ * M * P).mulVec x =
      star (P.mulVec x) ⬝ᵥ M.mulVec (P.mulVec x) := by
  have h1 : (Pᴴ * M * P).mulVec x =
      Pᴴ.mulVec (M.mulVec (P.mulVec x)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h1, ← star_mulVec_dotProduct_rect_real]

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι]

/-- Block-diagonal matrix of an indexed family of square real matrices. -/
def matrixFamilyBlockDiagonal (A : ι → Matrix n n ℝ) :
    Matrix (ι × n) (ι × n) ℝ :=
  fun p q => if p.1 = q.1 then A p.1 p.2 q.2 else 0

/-- The quadratic form of a block-diagonal family is the sum of its local forms. -/
theorem matrixFamilyBlockDiagonal_quadratic
    (A : ι → Matrix n n ℝ) (x : ι × n → ℝ) :
    x ⬝ᵥ (matrixFamilyBlockDiagonal A).mulVec x =
      ∑ w : ι, (fun i => x (w, i)) ⬝ᵥ (A w).mulVec (fun i => x (w, i)) := by
  simp only [dotProduct, mulVec, matrixFamilyBlockDiagonal,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [Finset.sum_eq_single w]
  · simp
  · intro v hv hvw
    simp [Ne.symm hvw]
  · simp

/-- A finite block-diagonal family of positive-definite matrices is positive definite. -/
theorem matrixFamilyBlockDiagonal_posDef
    {A : ι → Matrix n n ℝ} (hA : ∀ w, (A w).PosDef) :
    (matrixFamilyBlockDiagonal A).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext p q
    simp only [Matrix.conjTranspose_apply, star_trivial, matrixFamilyBlockDiagonal]
    by_cases hpq : p.1 = q.1
    · simp only [hpq, ↓reduceIte]
      exact congrFun (congrFun (hA q.1).1 p.2) q.2
    · have hqp : ¬q.1 = p.1 := fun h => hpq h.symm
      simp only [hpq, hqp, ↓reduceIte]
  · intro x hx
    have hp : ∃ p, x p ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    obtain ⟨⟨w, i⟩, hi⟩ := hp
    have hwne : (fun j => x (w, j)) ≠ 0 := by
      intro h
      exact hi (congrFun h i)
    rw [star_trivial, matrixFamilyBlockDiagonal_quadratic]
    apply Finset.sum_pos'
    · intro v hv
      simpa only [star_trivial] using (hA v).posSemidef.dotProduct_mulVec_nonneg
        (fun j => x (v, j))
    · exact ⟨w, Finset.mem_univ w, by
        have hwpos := ((Matrix.posDef_iff_dotProduct_mulVec).mp (hA w)).2 hwne
        simpa only [star_trivial] using hwpos⟩

variable {m : Type*} [Fintype m]

/-- Orthogonal sum of two real square matrices. -/
def matrixOrthogonalSum (A : Matrix n n ℝ) (B : Matrix m m ℝ) :
    Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  Matrix.fromBlocks A 0 0 B

/-- A binary orthogonal sum has the sum of the two component quadratic forms. -/
theorem matrixOrthogonalSum_quadratic
    (A : Matrix n n ℝ) (B : Matrix m m ℝ) (x : n ⊕ m → ℝ) :
    x ⬝ᵥ (matrixOrthogonalSum A B).mulVec x =
      (fun i => x (Sum.inl i)) ⬝ᵥ A.mulVec (fun i => x (Sum.inl i)) +
      (fun i => x (Sum.inr i)) ⬝ᵥ B.mulVec (fun i => x (Sum.inr i)) := by
  simp [matrixOrthogonalSum, dotProduct, mulVec, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- The orthogonal sum of two positive-definite real matrices is positive definite. -/
theorem matrixOrthogonalSum_posDef
    {A : Matrix n n ℝ} {B : Matrix m m ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (matrixOrthogonalSum A B).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · exact hA.1.fromBlocks (by simp) hB.1
  · intro x hx
    rw [star_trivial, matrixOrthogonalSum_quadratic]
    have hleft : 0 ≤ (fun i => x (Sum.inl i)) ⬝ᵥ
        A.mulVec (fun i => x (Sum.inl i)) := by
      simpa only [star_trivial] using hA.posSemidef.dotProduct_mulVec_nonneg
        (fun i => x (Sum.inl i))
    have hright : 0 ≤ (fun i => x (Sum.inr i)) ⬝ᵥ
        B.mulVec (fun i => x (Sum.inr i)) := by
      simpa only [star_trivial] using hB.posSemidef.dotProduct_mulVec_nonneg
        (fun i => x (Sum.inr i))
    by_cases hl : (fun i => x (Sum.inl i)) = 0
    · have hr : (fun i => x (Sum.inr i)) ≠ 0 := by
        intro hr
        apply hx
        funext i
        rcases i with i | i
        · exact congrFun hl i
        · exact congrFun hr i
      have hrightpos : 0 < (fun i => x (Sum.inr i)) ⬝ᵥ
          B.mulVec (fun i => x (Sum.inr i)) := by
        have hp := ((Matrix.posDef_iff_dotProduct_mulVec).mp hB).2 hr
        simpa only [star_trivial] using hp
      nlinarith
    · have hleftpos : 0 < (fun i => x (Sum.inl i)) ⬝ᵥ
          A.mulVec (fun i => x (Sum.inl i)) := by
        have hp := ((Matrix.posDef_iff_dotProduct_mulVec).mp hA).2 hl
        simpa only [star_trivial] using hp
      nlinarith

end

end GaloisForLFunctions.HTGeometry
