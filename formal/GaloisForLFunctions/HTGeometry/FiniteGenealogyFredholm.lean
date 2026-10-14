import GaloisForLFunctions.HTGeometry.FiniteGenealogyGramMatrix
import GaloisForLFunctions.HTGeometry.FiniteBilateralWeightedShift

/-! # Literal finite scalar genealogies on the full Hilbert space

Each finite column is the original certificate column `e_j-c_(j-1)e_(j-1)`.
The finite matrix used for the determinant is obtained from this actual operator.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt _root_.ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

theorem finitePathMatrix_entry {R : Type*} [CommRing R] (d u l : ℕ → R) :
    ∀ (N : ℕ) (i j : Fin N), finitePathMatrix d u l N i j =
      if i = j then d (N - 1 - i) else
      if (i : ℕ) + 1 = j then u (N - 2 - i) else
      if (j : ℕ) + 1 = i then l (N - 2 - j) else 0 := by
  intro N
  induction N with
  | zero => intro i; exact Fin.elim0 i
  | succ N ih =>
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp
        · have hN : N + 1 - 2 = N - 1 := by omega
          simp [hN, Fin.ext_iff]
      · refine Fin.cases ?_ (fun j => ?_) j
        · have hN : N + 1 - 2 = N - 1 := by omega
          simp [hN]
        · rw [finitePathMatrix_succ_succ, ih]
          have h1 : N + 1 - 1 - ((i : ℕ) + 1) = N - 1 - i := by omega
          have h2 : N + 1 - 2 - ((i : ℕ) + 1) = N - 2 - i := by omega
          have h3 : N + 1 - 2 - ((j : ℕ) + 1) = N - 2 - j := by omega
          simp only [Fin.succ_inj, Fin.val_succ, h1, h2, h3, Nat.add_right_cancel_iff]

def finiteGenealogyColumn (w : ℕ → ℂ) : ℕ → lp (fun _ : ℕ => ℂ) 2
  | 0 => lpBasisVec 0
  | n + 1 => lpBasisVec (n + 1) - w n • lpBasisVec n

@[simp] theorem finiteGenealogyColumn_zero (w : ℕ → ℂ) :
    finiteGenealogyColumn w 0 = lpBasisVec 0 := rfl

@[simp] theorem finiteGenealogyColumn_succ (w : ℕ → ℂ) (n : ℕ) :
    finiteGenealogyColumn w (n + 1) = lpBasisVec (n + 1) - w n • lpBasisVec n := rfl

theorem inner_lpBasisVec_lpBasisVec (i j : ℕ) :
    ⟪lpBasisVec i, lpBasisVec j⟫_ℂ = if i = j then 1 else 0 := by
  rw [inner_lpBasisVec]
  by_cases h : i = j
  · subst i; simp [lpBasisVec, lp.single_apply]
  · simp [lpBasisVec, lp.single_apply, h]

theorem inner_finiteGenealogyColumn (w : ℕ → ℂ) (i j : ℕ) :
    ⟪finiteGenealogyColumn w i, finiteGenealogyColumn w j⟫_ℂ =
      if i = j then (if i = 0 then 1 else 1 + ((‖w (i - 1)‖ ^ 2 : ℝ) : ℂ)) else
      if i + 1 = j then -w i else
      if j + 1 = i then -conj (w j) else 0 := by
  cases i with
  | zero =>
      cases j with
      | zero => simp only [finiteGenealogyColumn_zero, inner_lpBasisVec_lpBasisVec, ite_true]
      | succ j =>
          simp only [finiteGenealogyColumn_zero, finiteGenealogyColumn_succ,
            inner_sub_right, inner_smul_right, inner_lpBasisVec_lpBasisVec]
          by_cases hj : j = 0
          · subst j; simp
          · simp [hj, Ne.symm hj]
  | succ i =>
      cases j with
      | zero =>
          simp only [finiteGenealogyColumn_zero, finiteGenealogyColumn_succ,
            inner_sub_left, inner_smul_left, inner_lpBasisVec_lpBasisVec]
          by_cases hi : i = 0
          · subst i; simp
          · simp [hi]
      | succ j =>
          simp only [finiteGenealogyColumn_succ, inner_sub_left, inner_sub_right,
            inner_smul_left, inner_smul_right, inner_lpBasisVec_lpBasisVec]
          by_cases hij : i = j
          · subst j
            simp [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          · by_cases h1 : i + 1 = j
            · have h2 : j + 1 ≠ i := by omega
              simp [hij, h1, Ne.symm h2]
            · by_cases h2 : j + 1 = i
              · simp [hij, h1, h2]; omega
              · simp [hij, h1, h2, Ne.symm h2]

def finiteScalarGenealogy (w : ℕ → ℂ) (N : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  ∑ j ∈ Finset.range N, rankOne ℂ (finiteGenealogyColumn w j) (lpBasisVec j)

theorem finiteScalarGenealogy_traceClass (w : ℕ → ℂ) (N : ℕ) :
    RHTower.MemSchattenClass 1 (finiteScalarGenealogy w N) :=
  memSchattenClass_one_sum_rankOne (Finset.range N) (finiteGenealogyColumn w) lpBasisVec

theorem finiteScalarGenealogy_basis (w : ℕ → ℂ) (N j : ℕ) :
    finiteScalarGenealogy w N (lpBasisVec j) =
      if j < N then finiteGenealogyColumn w j else 0 := by
  rw [finiteScalarGenealogy, FunLike.coe_sum, Finset.sum_apply]
  have hterm (k : ℕ) : rankOne ℂ (finiteGenealogyColumn w k) (lpBasisVec k) (lpBasisVec j) =
      if k = j then finiteGenealogyColumn w j else 0 := by
    rw [rankOne_apply, inner_lpBasisVec_lpBasisVec]
    split_ifs with h
    · subst k; simp
    · simp
  simp_rw [hterm]
  simp

def finiteScalarGenealogyGramMatrix (w : ℕ → ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (if i = j then 1 else 0) +
    ⟪finiteGenealogyColumn w i, finiteGenealogyColumn w j⟫_ℂ

private theorem pathDiagonal_eq (w : ℕ → ℂ) (n : ℕ) :
    genealogyPathDiagonal w n =
      if n = 0 then 2 else 2 + ((‖w (n - 1)‖ ^ 2 : ℝ) : ℂ) := by
  cases n <;> simp [genealogyPathDiagonal]

theorem finiteScalarGenealogyGramMatrix_reverse (w : ℕ → ℂ) (N : ℕ) :
    (finiteScalarGenealogyGramMatrix w N).submatrix Fin.rev Fin.rev = genealogyPathMatrix w N := by
  ext i j
  have hv (k : Fin N) : (k.rev : ℕ) = N - 1 - k := by
    change N - ((k : ℕ) + 1) = N - 1 - k
    omega
  have hd : (i.rev : ℕ) = (j.rev : ℕ) ↔ i = j := by
    constructor
    · intro h
      exact Fin.rev_injective (Fin.ext h)
    · rintro rfl; rfl
  have hrev1 : (i.rev : ℕ) + 1 = (j.rev : ℕ) ↔ (j : ℕ) + 1 = i := by
    rw [hv, hv]
    omega
  have hrev2 : (j.rev : ℕ) + 1 = (i.rev : ℕ) ↔ (i : ℕ) + 1 = j := by
    rw [hv, hv]
    omega
  simp only [Matrix.submatrix_apply, finiteScalarGenealogyGramMatrix, inner_finiteGenealogyColumn,
    genealogyPathMatrix, finitePathMatrix_entry, hd, hrev1, hrev2]
  by_cases hij : i = j
  · subst j
    simp only [hv, pathDiagonal_eq]
    split_ifs <;> ring
  · have hrev : i.rev ≠ j.rev := fun h => hij (Fin.rev_injective h)
    simp only [if_neg hij, if_neg hrev, zero_add]
    by_cases h1 : (i : ℕ) + 1 = j
    · have h2 : ¬ (j : ℕ) + 1 = i := by omega
      have hj : (j.rev : ℕ) = N - 2 - i := by rw [hv]; omega
      simp only [if_pos h1, if_neg h2, hj]
    · by_cases h2 : (j : ℕ) + 1 = i
      · have hi : (i.rev : ℕ) = N - 2 - j := by rw [hv]; omega
        simp only [if_neg h1, if_pos h2, hi]
      · simp [h1, h2]

theorem det_finiteScalarGenealogyGramMatrix (w : ℕ → ℂ) (N : ℕ) :
    (finiteScalarGenealogyGramMatrix w N).det = (finiteGenealogyGramValue w N : ℂ) := by
  rw [← Matrix.det_submatrix_equiv_self Fin.revPerm]
  change ((finiteScalarGenealogyGramMatrix w N).submatrix Fin.rev Fin.rev).det = _
  rw [finiteScalarGenealogyGramMatrix_reverse, det_genealogyPathMatrix]

theorem finiteGenealogyColumn_coordinate (w : ℕ → ℂ) (j i : ℕ) :
    finiteGenealogyColumn w j i =
      (if i = j then 1 else 0) - (if i + 1 = j then w i else 0) := by
  cases j with
  | zero =>
      by_cases h : i = 0
      · subst i; simp [lpBasisVec, lp.single_apply]
      · simp [lpBasisVec, lp.single_apply, h]
  | succ j =>
      by_cases h : i = j
      · subst i; simp [lpBasisVec, lp.single_apply]
      · by_cases hs : i = j + 1
        · subst i; simp [lpBasisVec, lp.single_apply]
        · simp [lpBasisVec, lp.single_apply, h, hs]

theorem finiteScalarGenealogy_apply_coordinate (w : ℕ → ℂ) (N : ℕ)
    (f : lp (fun _ : ℕ => ℂ) 2) (i : ℕ) :
    finiteScalarGenealogy w N f i = (if i < N then f i else 0) -
      w i * (if i + 1 < N then f (i + 1) else 0) := by
  rw [finiteScalarGenealogy, FunLike.coe_sum, Finset.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  have hc (j : ℕ) : rankOne ℂ (finiteGenealogyColumn w j) (lpBasisVec j) f i =
      (if j = i then f i else 0) - (if j = i + 1 then w i * f (i + 1) else 0) := by
    rw [rankOne_apply, inner_lpBasisVec]
    change f j * finiteGenealogyColumn w j i = _
    rw [finiteGenealogyColumn_coordinate]
    by_cases h : j = i <;> by_cases hs : j = i + 1 <;>
      simp_all [mul_comm, eq_comm]
  simp_rw [hc]
  rw [Finset.sum_sub_distrib]
  simp [mul_ite]

theorem coordMatrix_finiteScalarGenealogy (w : ℕ → ℂ) (N i j : ℕ) :
    RHTower.coordMatrix (lpBasis ℕ) (finiteScalarGenealogy w N) (i, j) =
      if j < N then
        (if i = j then 1 else 0) - (if i + 1 = j then w i else 0) else 0 := by
  rw [RHTower.coordMatrix_apply, lpBasis_apply, lpBasis_apply]
  change ⟪lpBasisVec i, finiteScalarGenealogy w N (lpBasisVec j)⟫_ℂ = _
  rw [inner_lpBasisVec, finiteScalarGenealogy_basis]
  by_cases h : j < N <;> simp [h, finiteGenealogyColumn_coordinate]

theorem finiteScalarGenealogy_coordinate_support (w : ℕ → ℂ) (N : ℕ)
    (p : ℕ × ℕ) (hp : p ∉ Finset.range N ×ˢ Finset.range N) :
    RHTower.coordMatrix (lpBasis ℕ) (finiteScalarGenealogy w N) p = 0 := by
  rcases p with ⟨i, j⟩
  rw [coordMatrix_finiteScalarGenealogy]
  by_cases hj : j < N
  · have hi : ¬ i < N := by
      intro hi
      exact hp (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩)
    have hne : i ≠ j := by omega
    have hs : i + 1 ≠ j := by omega
    simp [hj, hne, hs]
  · simp [hj]

theorem finiteScalarGenealogy_gram_traceClass (w : ℕ → ℂ) (N : ℕ) :
    RHTower.MemSchattenClass 1
      ((finiteScalarGenealogy w N).adjoint ∘L finiteScalarGenealogy w N) :=
  RHTower.memSchattenClass_one_comp_left (finiteScalarGenealogy_traceClass w N) _

theorem coordMatrix_finiteScalarGenealogy_gram (w : ℕ → ℂ) (N i j : ℕ) :
    RHTower.coordMatrix (lpBasis ℕ)
      ((finiteScalarGenealogy w N).adjoint ∘L finiteScalarGenealogy w N) (i, j) =
        if i < N ∧ j < N then
          ⟪finiteGenealogyColumn w i, finiteGenealogyColumn w j⟫_ℂ else 0 := by
  rw [RHTower.coordMatrix_apply, comp_apply, adjoint_inner_right,
    lpBasis_apply, lpBasis_apply]
  change ⟪finiteScalarGenealogy w N (lpBasisVec i),
    finiteScalarGenealogy w N (lpBasisVec j)⟫_ℂ = _
  rw [finiteScalarGenealogy_basis, finiteScalarGenealogy_basis]
  by_cases hi : i < N <;> by_cases hj : j < N <;> simp [hi, hj]

theorem finiteScalarGenealogy_gram_coordinate_support (w : ℕ → ℂ) (N : ℕ)
    (p : ℕ × ℕ) (hp : p ∉ Finset.range N ×ˢ Finset.range N) :
    RHTower.coordMatrix (lpBasis ℕ)
      ((finiteScalarGenealogy w N).adjoint ∘L finiteScalarGenealogy w N) p = 0 := by
  rcases p with ⟨i, j⟩
  rw [coordMatrix_finiteScalarGenealogy_gram]
  apply if_neg
  simpa only [Finset.mem_product, Finset.mem_range] using hp

private theorem det_one_add_blockMatrix_range (K : ℕ × ℕ → ℂ) (N : ℕ) :
    (1 + blockMatrix K (Finset.range N)).det =
      Matrix.det (fun i j : Fin N => (if i = j then 1 else 0) + K (i, j)) := by
  let e : Fin N ≃ Finset.range N :=
    { toFun := fun i => ⟨i, Finset.mem_range.mpr i.isLt⟩
      invFun := fun i => ⟨i, Finset.mem_range.mp i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i j
  simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, blockMatrix, e, Fin.ext_iff]

theorem fredholmDetOp_finiteScalarGenealogy_gram (w : ℕ → ℂ) (N : ℕ) :
    RHTower.fredholmDetOp (lpBasis ℕ)
      ((finiteScalarGenealogy w N).adjoint ∘L finiteScalarGenealogy w N) =
        (finiteGenealogyGramValue w N : ℂ) := by
  rw [fredholmDetOp_eq_det_block_of_support (lpBasis ℕ)
    (finiteScalarGenealogy_gram_traceClass w N) (Finset.range N)
    (finiteScalarGenealogy_gram_coordinate_support w N), det_one_add_blockMatrix_range]
  have heq : (fun i j : Fin N => (if i = j then (1 : ℂ) else 0) +
      RHTower.coordMatrix (lpBasis ℕ)
        ((finiteScalarGenealogy w N).adjoint ∘L finiteScalarGenealogy w N) (i, j)) =
      finiteScalarGenealogyGramMatrix w N := by
    ext i j
    simp [coordMatrix_finiteScalarGenealogy_gram, i.isLt, j.isLt,
      finiteScalarGenealogyGramMatrix]
  rw [heq, det_finiteScalarGenealogyGramMatrix]

theorem fredholmDetOp_smul_finiteScalarGenealogy (w : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    RHTower.fredholmDetOp (lpBasis ℕ) (z • finiteScalarGenealogy w N) = (1 + z) ^ N := by
  have hc (i j : ℕ) : RHTower.coordMatrix (lpBasis ℕ)
      (z • finiteScalarGenealogy w N) (i, j) =
      z * RHTower.coordMatrix (lpBasis ℕ) (finiteScalarGenealogy w N) (i, j) := by
    simp only [RHTower.coordMatrix_apply, smul_apply, inner_smul_right]
  have hs (p : ℕ × ℕ) (hp : p ∉ Finset.range N ×ˢ Finset.range N) :
      RHTower.coordMatrix (lpBasis ℕ) (z • finiteScalarGenealogy w N) p = 0 := by
    rcases p with ⟨i, j⟩
    rw [hc, finiteScalarGenealogy_coordinate_support w N (i, j) hp, mul_zero]
  rw [fredholmDetOp_eq_det_block_of_support (lpBasis ℕ)
    (RHTower.memSchattenClass_one_smul (finiteScalarGenealogy_traceClass w N) z)
    (Finset.range N) hs, det_one_add_blockMatrix_range]
  have hentry (i j : Fin N) :
      RHTower.coordMatrix (lpBasis ℕ) (z • finiteScalarGenealogy w N) (i, j) =
        z * ((if i = j then 1 else 0) - (if (i : ℕ) + 1 = j then w i else 0)) := by
    rw [hc, coordMatrix_finiteScalarGenealogy, if_pos j.isLt]
    simp only [Fin.ext_iff]
  have htri : Matrix.BlockTriangular (fun i j : Fin N => (if i = j then (1 : ℂ) else 0) +
      RHTower.coordMatrix (lpBasis ℕ) (z • finiteScalarGenealogy w N) (i, j)) id := by
    intro i j hij
    have hlt : (j : ℕ) < i := hij
    have hne : i ≠ j := by intro h; subst i; omega
    have hs : (i : ℕ) + 1 ≠ j := by omega
    simp [hentry, hne, hs]
  rw [Matrix.det_of_upperTriangular htri]
  simp [hentry]

end
end GaloisForLFunctions.HTGeometry
