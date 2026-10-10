import Mathlib

/-!
# Sylvester's criterion for leading principal minors

For a symmetric array `m : ℕ → ℕ → ℝ` let `L_N = (m i j)_{i,j<N}`.  If every leading principal minor
`det L_k` with `k ≤ N` is positive, then `L_N` is positive definite
(`posDef_leadingMatrix_of_det_pos`); conversely positive definite leading blocks have positive
determinants.

The inductive step writes `L_{n+1}` as the block matrix `(L_n, b; bᵀ, c)`.  Its determinant is
`det L_n · (c − bᵀ L_n⁻¹ b)`, so the one-by-one Schur complement is positive, the block matrix is
positive semidefinite, and it is positive definite because its determinant is nonzero.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The leading `N × N` block of an array. -/
def leadingMatrix (m : ℕ → ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => m i j

theorem leadingMatrix_succ_submatrix {m : ℕ → ℕ → ℝ} (hsym : ∀ i j, m i j = m j i) (n : ℕ) :
    (leadingMatrix m (n + 1)).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (leadingMatrix m n) (Matrix.of fun (i : Fin n) (j : Fin 1) => m i (n + j))
        (Matrix.of fun (i : Fin n) (j : Fin 1) => m i (n + j))ᴴ
        (Matrix.of fun (i j : Fin 1) => m (n + i) (n + j)) := by
  ext (i | i) (j | j)
  · simp [leadingMatrix]
  · simp [leadingMatrix]
  · simp [leadingMatrix, hsym]
  · simp [leadingMatrix]

theorem posDef_leadingMatrix_zero (m : ℕ → ℕ → ℝ) : (leadingMatrix m 0).PosDef :=
  posDef_iff_dotProduct_mulVec.2 ⟨by ext i; exact i.elim0,
    fun x hx => absurd (Subsingleton.elim x 0) hx⟩

theorem posSemidef_fin_one {S : Matrix (Fin 1) (Fin 1) ℝ} (hS : 0 ≤ S 0 0) : S.PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp [conjTranspose_apply]
  · simp only [dotProduct, mulVec, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      star_trivial]
    nlinarith [sq_nonneg (x 0)]

/-- **The inductive step.** -/
theorem posDef_leadingMatrix_succ {m : ℕ → ℕ → ℝ} (hsym : ∀ i j, m i j = m j i) {n : ℕ}
    (hn : (leadingMatrix m n).PosDef) (hdet : 0 < (leadingMatrix m (n + 1)).det) :
    (leadingMatrix m (n + 1)).PosDef := by
  set A := leadingMatrix m n with hAdef
  set B : Matrix (Fin n) (Fin 1) ℝ := Matrix.of fun i j => m i (n + j) with hB
  set D : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun i j => m (n + i) (n + j) with hD
  have hblock := leadingMatrix_succ_submatrix hsym n
  letI : Invertible A := hn.isUnit.invertible
  have hdetblock : (fromBlocks A B Bᴴ D).det = A.det * (D - Bᴴ * A⁻¹ * B).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  rw [← hblock, det_submatrix_equiv_self] at hdetblock
  have hA := hn.det_pos
  have hS : 0 < (D - Bᴴ * A⁻¹ * B).det := by
    rw [hdetblock] at hdet
    exact pos_of_mul_pos_right hdet hA.le
  have hS00 : 0 ≤ (D - Bᴴ * A⁻¹ * B) 0 0 := by
    rw [det_unique] at hS
    exact hS.le
  have hpsd : (fromBlocks A B Bᴴ D).PosSemidef := (PosDef.fromBlocks₁₁ B D hn).2 (posSemidef_fin_one hS00)
  have hpsdL : (leadingMatrix m (n + 1)).PosSemidef := by
    rw [← posSemidef_submatrix_equiv finSumFinEquiv, hblock]
    exact hpsd
  exact hpsdL.posDef_iff_det_ne_zero.2 hdet.ne'

/-- **Sylvester's criterion.**  If all leading principal minors up to size `N` of a symmetric array are
positive, the leading `N × N` block is positive definite. -/
theorem posDef_leadingMatrix_of_det_pos {m : ℕ → ℕ → ℝ} (hsym : ∀ i j, m i j = m j i) {N : ℕ}
    (h : ∀ k ≤ N, 0 < (leadingMatrix m k).det) : (leadingMatrix m N).PosDef := by
  induction N with
  | zero => exact posDef_leadingMatrix_zero m
  | succ n ih =>
    exact posDef_leadingMatrix_succ hsym (ih fun k hk => h k (by omega)) (h (n + 1) le_rfl)

/-- **Sylvester's criterion, all sizes.** -/
theorem forall_posDef_leadingMatrix_iff {m : ℕ → ℕ → ℝ} (hsym : ∀ i j, m i j = m j i) :
    (∀ N, (leadingMatrix m N).PosDef) ↔ ∀ N, 0 < (leadingMatrix m N).det :=
  ⟨fun h N => (h N).det_pos, fun h _ => posDef_leadingMatrix_of_det_pos hsym fun k _ => h k⟩

end

end GaloisForLFunctions.HTGeometry
