import Mathlib

/-!
# A real matrix with positive quadratic form has positive determinant

**Theorem** (`det_pos_of_quadForm_pos`).  If `A` is a real square matrix with `xᵀ A x > 0` for every
`x ≠ 0`, then `det A > 0`.

The symmetric part `S = (A + Aᵀ)/2` has the same quadratic form, so it is positive definite and
`det S > 0`.  Along the segment `B(s) = (1 − s) S + s A` the quadratic form is still `xᵀ A x > 0`,
so `B(s)` has trivial kernel and `det B(s) ≠ 0` for `s ∈ [0, 1]`.  By continuity and the
intermediate value theorem the sign of `det B(s)` cannot change between `s = 0` and `s = 1`.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem dotProduct_transpose_mulVec (A : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

/-- **Positive quadratic form ⟹ positive determinant.** -/
theorem det_pos_of_quadForm_pos (A : Matrix n n ℝ)
    (h : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) : 0 < A.det := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix n n ℝ, S = (1 / 2 : ℝ) • (A + Aᵀ) := ⟨_, rfl⟩
  have hSq : ∀ x : n → ℝ, x ⬝ᵥ (S *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
    intro x
    rw [hS, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add,
      dotProduct_transpose_mulVec, smul_eq_mul]
    ring
  have hSpd : S.PosDef := by
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hS, transpose_smul, transpose_add,
        transpose_transpose, add_comm]
    · simpa [hSq] using h x hx
  obtain ⟨B, hB⟩ : ∃ B : ℝ → Matrix n n ℝ, B = fun s => (1 - s) • S + s • A := ⟨_, rfl⟩
  have hBq : ∀ s : ℝ, ∀ x : n → ℝ, x ⬝ᵥ (B s *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
    intro s x
    rw [hB]
    simp only
    rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul,
      hSq x, smul_eq_mul, smul_eq_mul]
    ring
  have hBdet : ∀ s : ℝ, (B s).det ≠ 0 := by
    intro s hs
    obtain ⟨v, hv, hBv⟩ := exists_mulVec_eq_zero_iff.mpr hs
    have := h v hv
    rw [← hBq s v, hBv, dotProduct_zero] at this
    exact lt_irrefl 0 this
  have hcont : Continuous fun s : ℝ => (B s).det := by
    refine Continuous.matrix_det ?_
    rw [hB]
    fun_prop
  have h0 : B 0 = S := by rw [hB]; simp
  have h1 : B 1 = A := by rw [hB]; simp
  have hS0 : 0 < (B 0).det := by rw [h0]; exact hSpd.det_pos
  by_contra hneg
  push Not at hneg
  rw [← h1] at hneg
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' (zero_le_one : (0 : ℝ) ≤ 1) hcont.continuousOn
    ⟨hneg, hS0.le⟩
  exact hBdet s hs0

end

end GaloisForLFunctions.HTGeometry
