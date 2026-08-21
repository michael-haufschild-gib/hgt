import GaloisForLFunctions.HTGeometry.BorelWeil.PolyRealization

/-!
# Gaussian elimination and the big cell

A matrix all of whose leading principal minors are nonzero factors as `g = L * B` with `L` lower
unitriangular and `B` invertible upper triangular.  This is the statement that the *big cell*
`U⁻ · B` of the matrix space is exactly the locus where the leading principal minors do not
vanish; it is the geometric input for the uniqueness of the Borel–Weil highest weight vector.

The proof is Gaussian elimination without pivoting: one clears the sub-diagonal entries of the
columns from left to right, the pivot at step `c` being `D_{c+1}/D_c ≠ 0`.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.IsLowerUni`
* `GaloisForLFunctions.HTGeometry.BorelWeil.clearCol`

## Main results

* `exists_lu_of_leadingMinor_ne_zero` — the LU decomposition.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {N : ℕ} {k : Type*} [Field k]

/-- Lower unitriangular matrices. -/
def IsLowerUni (L : Matrix (Fin N) (Fin N) k) : Prop :=
  (∀ i j : Fin N, i < j → L i j = 0) ∧ (∀ i, L i i = 1)

theorem IsLowerUni.blockTriangular {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L) :
    L.BlockTriangular (OrderDual.toDual : Fin N → (Fin N)ᵒᵈ) := by
  intro i j hij
  exact hL.1 i j (by simpa using hij)

theorem IsLowerUni.one : IsLowerUni (1 : Matrix (Fin N) (Fin N) k) :=
  ⟨fun i j hij => Matrix.one_apply_ne (ne_of_lt hij), fun i => by simp⟩

theorem IsLowerUni.mul {L M : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L) (hM : IsLowerUni M) :
    IsLowerUni (L * M) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := Matrix.BlockTriangular.mul hL.blockTriangular hM.blockTriangular
    exact this (by simpa using hij)
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hL.2 i, hM.2 i, one_mul]
    · intro r _ hr
      rcases lt_or_gt_of_ne hr with h | h
      · rw [hM.1 r i h, mul_zero]
      · rw [hL.1 i r h, zero_mul]
    · intro hnot; exact absurd (Finset.mem_univ i) hnot

theorem IsLowerUni.det_eq_one {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L hL.blockTriangular]
  simp [hL.2]

/-- The transpose of a truncation is the truncation of the transpose. -/
theorem truncate_transpose (j : ℕ) (M : Matrix (Fin N) (Fin N) k) :
    truncate j Mᵀ = (truncate j M)ᵀ := by
  ext i i'
  by_cases h1 : (i : ℕ) < j
  · by_cases h2 : (i' : ℕ) < j
    · rw [truncate_apply_of_both h1 h2, Matrix.transpose_apply, Matrix.transpose_apply,
        truncate_apply_of_both h2 h1]
    · rw [truncate_apply_of_not_right h2, Matrix.transpose_apply, truncate_apply_of_not_left h2]
      by_cases h3 : i = i' <;> simp [h3, eq_comm]
  · rw [truncate_apply_of_not_left h1, Matrix.transpose_apply, truncate_apply_of_not_right h1]
    by_cases h3 : i = i' <;> simp [h3, eq_comm]

theorem truncate_mul_left (j : ℕ) {L : Matrix (Fin N) (Fin N) k}
    (hL : ∀ i j : Fin N, i < j → L i j = 0) (g : Matrix (Fin N) (Fin N) k) :
    truncate j (L * g) = truncate j L * truncate j g := by
  have hLT : (Lᵀ).BlockTriangular id := by
    intro a b hab
    exact hL b a (by simpa using hab)
  have h1 : truncate j ((L * g)ᵀ) = truncate j (gᵀ) * truncate j (Lᵀ) := by
    rw [Matrix.transpose_mul, truncate_mul j _ _ hLT]
  rw [truncate_transpose] at h1
  have h2 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_transpose, Matrix.transpose_mul, ← truncate_transpose,
    ← truncate_transpose, Matrix.transpose_transpose, Matrix.transpose_transpose] at h2
  exact h2

theorem leadingMinorMat_lowerUni_mul (j : ℕ) {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L)
    (g : Matrix (Fin N) (Fin N) k) :
    leadingMinorMat j (L * g) = leadingMinorMat j g := by
  have htL : IsLowerUni (truncate j L) := by
    refine ⟨fun i i' hii => ?_, fun i => ?_⟩
    · by_cases h1 : (i : ℕ) < j
      · by_cases h2 : (i' : ℕ) < j
        · rw [truncate_apply_of_both h1 h2]; exact hL.1 i i' hii
        · rw [truncate_apply_of_not_right h2, if_neg (ne_of_lt hii)]
      · rw [truncate_apply_of_not_left h1, if_neg (ne_of_lt hii)]
    · by_cases h1 : (i : ℕ) < j
      · rw [truncate_apply_of_both h1 h1]; exact hL.2 i
      · rw [truncate_apply_of_not_left h1, if_pos rfl]
  rw [leadingMinorMat, truncate_mul_left j hL.1 g, Matrix.det_mul, htL.det_eq_one, one_mul,
    leadingMinorMat]

/-- The elementary matrix clearing the sub-diagonal entries of column `c`. -/
def clearCol (c : Fin N) (v : Fin N → k) : Matrix (Fin N) (Fin N) k :=
  1 + ∑ r : Fin N, (if c < r then Matrix.single r c (v r) else 0)

theorem clearCol_apply (c : Fin N) (v : Fin N → k) (i j : Fin N) :
    clearCol c v i j = (1 : Matrix (Fin N) (Fin N) k) i j + (if c < i ∧ c = j then v i else 0) := by
  rw [clearCol, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  rw [Finset.sum_eq_single i]
  · by_cases h : c < i
    · rw [if_pos h, Matrix.single_apply]
      by_cases h2 : c = j
      · rw [if_pos ⟨rfl, h2⟩, if_pos ⟨h, h2⟩]
      · rw [if_neg (by tauto), if_neg (by tauto)]
    · rw [if_neg h, if_neg (by tauto)]
      simp
  · intro r _ hr
    by_cases h : c < r
    · rw [if_pos h, Matrix.single_apply, if_neg (by tauto)]
    · rw [if_neg h]; simp
  · intro hnot; exact absurd (Finset.mem_univ i) hnot

theorem isLowerUni_clearCol (c : Fin N) (v : Fin N → k) : IsLowerUni (clearCol c v) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [clearCol_apply, Matrix.one_apply_ne (ne_of_lt hij)]
    have : ¬ (c < i ∧ c = j) := by
      rintro ⟨h1, rfl⟩
      exact absurd hij (not_lt.mpr (le_of_lt h1))
    rw [if_neg this, add_zero]
  · rw [clearCol_apply, Matrix.one_apply_eq]
    have : ¬ (c < i ∧ c = i) := by rintro ⟨h1, rfl⟩; exact lt_irrefl _ h1
    rw [if_neg this, add_zero]

theorem clearCol_mul_apply (c : Fin N) (v : Fin N → k) (h : Matrix (Fin N) (Fin N) k)
    (i j : Fin N) :
    (clearCol c v * h) i j = h i j + (if c < i then v i * h c j else 0) := by
  rw [Matrix.mul_apply]
  have hsplit : ∀ r : Fin N, clearCol c v i r * h r j
      = (1 : Matrix (Fin N) (Fin N) k) i r * h r j
        + (if c < i ∧ c = r then v i * h r j else 0) := by
    intro r
    rw [clearCol_apply, add_mul]
    congr 1
    by_cases hh : c < i ∧ c = r <;> simp [hh]
  rw [Finset.sum_congr rfl fun r _ => hsplit r, Finset.sum_add_distrib]
  congr 1
  · rw [← Matrix.mul_apply, Matrix.one_mul]
  · rw [Finset.sum_eq_single c]
    · by_cases hh : c < i <;> simp [hh]
    · intro r _ hr
      have : ¬ (c < i ∧ c = r) := by rintro ⟨-, rfl⟩; exact hr rfl
      rw [if_neg this]
    · intro hnot; exact absurd (Finset.mem_univ c) hnot

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {N : ℕ} {k : Type*} [Field k]

theorem diag_mul_of_lower {A B : Matrix (Fin N) (Fin N) k}
    (hA : ∀ i j : Fin N, i < j → A i j = 0) (hB : ∀ i j : Fin N, i < j → B i j = 0) (i : Fin N) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro r _ hr
    rcases lt_or_gt_of_ne hr with h | h
    · rw [hB r i h, mul_zero]
    · rw [hA i r h, zero_mul]
  · intro hnot; exact absurd (Finset.mem_univ i) hnot

theorem IsLowerUni.inv {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L) :
    IsLowerUni L⁻¹ := by
  haveI : Invertible L.det := by rw [hL.det_eq_one]; exact invertibleOne
  haveI : Invertible L := Matrix.invertibleOfDetInvertible _
  have hinv : L⁻¹.BlockTriangular (OrderDual.toDual : Fin N → (Fin N)ᵒᵈ) :=
    Matrix.blockTriangular_inv_of_blockTriangular hL.blockTriangular
  have hlow : ∀ i j : Fin N, i < j → L⁻¹ i j = 0 := fun i j hij => hinv (by simpa using hij)
  refine ⟨hlow, fun i => ?_⟩
  have hmul : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_of_invertible _)
  have := congrFun (congrFun hmul i) i
  rw [diag_mul_of_lower hL.1 hlow i, hL.2 i, one_mul, Matrix.one_apply_eq] at this
  exact this

/-- The leading principal minor of a matrix whose first `c` columns are already cleared below the
diagonal is the product of its first `j` diagonal entries, for `j ≤ c + 1`. -/
theorem leadingMinorMat_eq_prod_diag {h : Matrix (Fin N) (Fin N) k} {c : ℕ}
    (hc : ∀ r s : Fin N, (s : ℕ) < c → s < r → h r s = 0) {j : ℕ} (hj : j ≤ c + 1) :
    leadingMinorMat j h = ∏ i : Fin N, (if (i : ℕ) < j then h i i else 1) := by
  have htri : (truncate j h).BlockTriangular id := by
    intro r s hrs
    have hrs' : (s : ℕ) < (r : ℕ) := Fin.lt_def.mp hrs
    have hne : r ≠ s := fun hcon => by simp [hcon] at hrs'
    by_cases h1 : (r : ℕ) < j
    · by_cases h2 : (s : ℕ) < j
      · rw [truncate_apply_of_both h1 h2]
        rcases Nat.lt_or_ge (s : ℕ) c with hsc | hsc
        · exact hc r s hsc hrs
        · exact absurd hrs' (by omega)
      · rw [truncate_apply_of_not_right h2, if_neg hne]
    · rw [truncate_apply_of_not_left h1, if_neg hne]
  rw [leadingMinorMat, Matrix.det_of_upperTriangular htri]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < j
  · rw [truncate_apply_of_both hi hi, if_pos hi]
  · rw [truncate_apply_of_not_left hi, if_pos rfl, if_neg hi]

theorem exists_clear_columns (g : Matrix (Fin N) (Fin N) k)
    (hg : ∀ j : Fin N, leadingMinorMat ((j : ℕ) + 1) g ≠ 0) :
    ∀ c : ℕ, c ≤ N → ∃ L : Matrix (Fin N) (Fin N) k, IsLowerUni L ∧
      ∀ r s : Fin N, (s : ℕ) < c → s < r → (L * g) r s = 0 := by
  classical
  intro c
  induction c with
  | zero => intro _; exact ⟨1, IsLowerUni.one, by intro r s hs _; omega⟩
  | succ c ih =>
    intro hcN
    obtain ⟨L, hL, hclear⟩ := ih (by omega)
    have hcN' : c < N := by omega
    set cc : Fin N := ⟨c, hcN'⟩ with hcc
    set h := L * g with hh
    have hprod : (∏ i : Fin N, (if (i : ℕ) < c + 1 then h i i else 1))
        = h cc cc * ∏ i : Fin N, (if (i : ℕ) < c then h i i else 1) := by
      rw [← Finset.mul_prod_erase Finset.univ
          (fun i : Fin N => if (i : ℕ) < c + 1 then h i i else 1) (Finset.mem_univ cc),
        ← Finset.mul_prod_erase Finset.univ
          (fun i : Fin N => if (i : ℕ) < c then h i i else 1) (Finset.mem_univ cc)]
      rw [if_pos (by simp [hcc]), if_neg (by simp [hcc]), one_mul]
      refine congrArg _ (Finset.prod_congr rfl fun i hi => ?_)
      have hnec : (i : ℕ) ≠ c := fun hcon => (Finset.mem_erase.mp hi).1 (Fin.ext hcon)
      by_cases hlt : (i : ℕ) < c
      · rw [if_pos (by omega), if_pos hlt]
      · rw [if_neg (by omega), if_neg hlt]
    have hne : leadingMinorMat (c + 1) h ≠ 0 := by
      rw [hh, leadingMinorMat_lowerUni_mul _ hL]
      exact hg cc
    have hpivot : h cc cc ≠ 0 := by
      intro hzero
      apply hne
      rw [leadingMinorMat_eq_prod_diag hclear (le_refl (c + 1)), hprod, hzero, zero_mul]
    refine ⟨clearCol cc (fun r => -(h r cc) / (h cc cc)) * L,
      (isLowerUni_clearCol _ _).mul hL, ?_⟩
    intro r s hs hrs
    have hassoc : (clearCol cc (fun r => -(h r cc) / (h cc cc)) * L) * g
        = clearCol cc (fun r => -(h r cc) / (h cc cc)) * h := by rw [hh, Matrix.mul_assoc]
    rw [hassoc, clearCol_mul_apply]
    rcases Nat.lt_or_ge (s : ℕ) c with hsc | hsc
    · rw [hclear r s hsc hrs]
      by_cases hcr : cc < r
      · rw [if_pos hcr, hclear cc s hsc (by exact Fin.lt_def.mpr (by simpa [hcc] using hsc)),
          mul_zero, add_zero]
      · rw [if_neg hcr, add_zero]
    · have hsval : (s : ℕ) = c := by omega
      have hsceq : s = cc := Fin.ext hsval
      subst hsceq
      rw [if_pos hrs]
      field_simp
      ring

/-- **LU decomposition / the big cell.**  A matrix whose leading principal minors are all nonzero
factors as a lower unitriangular matrix times an invertible upper triangular matrix. -/
theorem exists_lu_of_leadingMinor_ne_zero (g : Matrix (Fin N) (Fin N) k)
    (hg : ∀ j : Fin N, leadingMinorMat ((j : ℕ) + 1) g ≠ 0) :
    ∃ L B : Matrix (Fin N) (Fin N) k, IsLowerUni L ∧ IsBorelMat B ∧ g = L * B := by
  classical
  obtain ⟨M, hM, hclear⟩ := exists_clear_columns g hg N (le_refl N)
  refine ⟨M⁻¹, M * g, hM.inv, ⟨fun r s hrs => hclear r s s.isLt hrs, fun i => ?_⟩, ?_⟩
  · have hmin : leadingMinorMat ((i : ℕ) + 1) (M * g)
        = ∏ i' : Fin N, (if (i' : ℕ) < (i : ℕ) + 1 then (M * g) i' i' else 1) :=
      leadingMinorMat_eq_prod_diag (c := N) (fun r s _ hrs => hclear r s s.isLt hrs)
        (by have := i.isLt; omega)
    have hne : leadingMinorMat ((i : ℕ) + 1) (M * g) ≠ 0 := by
      rw [leadingMinorMat_lowerUni_mul _ hM]; exact hg i
    rw [hmin] at hne
    have := Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
    rwa [if_pos (Nat.lt_succ_self _)] at this
  · haveI : Invertible M.det := by rw [hM.det_eq_one]; exact invertibleOne
    haveI : Invertible M := Matrix.invertibleOfDetInvertible _
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_invertible _), Matrix.one_mul]

end GaloisForLFunctions.HTGeometry.BorelWeil
