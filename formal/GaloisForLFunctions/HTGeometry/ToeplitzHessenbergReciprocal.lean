import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityOrderK

/-!
# Hessenberg minors are the coefficients of the alternating reciprocal

Let `F(y) = Σ_k a_k y^k` with `a₀ ≠ 0`, and let `β` be the coefficients of `1/F(−y)`, i.e. the
solution of `Σ_{k ≤ m} (−1)^k a_k β_{m−k} = [m = 0]`.  Then
(`pow_mul_eq_toeplitzMinor_hessenberg`)

  `a₀^{n+1} β_n = det (a_{c + 1 − r})_{r,c < n}`,

the Toeplitz minor with rows `0, …, n−1` and columns `1, …, n` (a Hessenberg matrix).  In
particular a `PF_n` sequence with `a₀ > 0` has `β_n ≥ 0` (`hessenberg_reciprocal_nonneg`).

Proof.  The truncated lower-triangular Toeplitz matrix `L = ((−1)^{i−j} a_{i−j})` has determinant
`a₀^{n+1}` and sends `β` to the first unit vector.  By Cramer's rule `a₀^{n+1} β_n` is the
determinant of `L` with its last column replaced by `e₀`.  Expanding along that column leaves
`(−1)^n det ((−1)^{r+1−c} a_{r+1−c})`.  Transposing and pulling the signs `(−1)^r (−1)^{c+1}` out
of rows and columns contributes another `(−1)^n`.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The signed Hessenberg determinant equals `(−1)^n` times the Hessenberg Toeplitz minor. -/
theorem det_hessenberg_alternating (a : ℕ → ℝ) (n : ℕ) :
    (Matrix.of fun r c : Fin n =>
        zext (fun k => (-1 : ℝ) ^ k * a k) (((r : ℕ) + 1 : ℤ) - (c : ℕ))).det =
      (-1) ^ n * toeplitzMinor a n (fun r => (r : ℕ)) (fun c => (c : ℕ) + 1) := by
  rw [← Matrix.det_transpose]
  have hentry : (Matrix.of fun r c : Fin n =>
        zext (fun k => (-1 : ℝ) ^ k * a k) (((r : ℕ) + 1 : ℤ) - (c : ℕ)))ᵀ =
      Matrix.of fun r c : Fin n => (-1 : ℝ) ^ (r : ℕ) *
        ((-1 : ℝ) ^ ((c : ℕ) + 1) * zext a ((((c : ℕ) + 1 : ℕ) : ℤ) - (r : ℕ))) := by
    ext r c
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    by_cases h : (r : ℕ) ≤ (c : ℕ) + 1
    · obtain ⟨m, hm⟩ : ∃ m, (c : ℕ) + 1 = r + m := ⟨c + 1 - r, by omega⟩
      rw [show (((c : ℕ) + 1 : ℤ) - (r : ℕ)) = (m : ℤ) by omega,
        show ((((c : ℕ) + 1 : ℕ) : ℤ) - (r : ℕ)) = (m : ℤ) by push_cast; omega,
        zext_natCast, zext_natCast, hm, pow_add]
      have h1 : ((-1 : ℝ) ^ (r : ℕ)) * (-1 : ℝ) ^ (r : ℕ) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      linear_combination (-(-1 : ℝ) ^ m * a m) * h1
    · rw [zext_of_neg _ (by omega), zext_of_neg _ (by push_cast; omega)]
      ring
  rw [hentry]
  have hfac : (Matrix.of fun r c : Fin n => (-1 : ℝ) ^ (r : ℕ) *
        ((-1 : ℝ) ^ ((c : ℕ) + 1) * zext a ((((c : ℕ) + 1 : ℕ) : ℤ) - (r : ℕ)))).det =
      (∏ r : Fin n, (-1 : ℝ) ^ (r : ℕ)) * ((∏ c : Fin n, (-1 : ℝ) ^ ((c : ℕ) + 1)) *
        toeplitzMinor a n (fun r => (r : ℕ)) (fun c => (c : ℕ) + 1)) := by
    calc _ = (Matrix.of fun r c : Fin n => (-1 : ℝ) ^ (r : ℕ) *
          (Matrix.of fun r c : Fin n => (-1 : ℝ) ^ ((c : ℕ) + 1) *
            zext a ((((c : ℕ) + 1 : ℕ) : ℤ) - (r : ℕ))) r c).det := rfl
      _ = (∏ r : Fin n, (-1 : ℝ) ^ (r : ℕ)) * (Matrix.of fun r c : Fin n =>
          (-1 : ℝ) ^ ((c : ℕ) + 1) * zext a ((((c : ℕ) + 1 : ℕ) : ℤ) - (r : ℕ))).det :=
          Matrix.det_mul_column _ _
      _ = _ := by
          rw [Matrix.det_mul_row]
          rfl
  rw [hfac]
  have hsign : (∏ r : Fin n, (-1 : ℝ) ^ (r : ℕ)) * (∏ c : Fin n, (-1 : ℝ) ^ ((c : ℕ) + 1)) =
      (-1) ^ n := by
    rw [← Finset.prod_mul_distrib]
    have : ∀ r : Fin n, (-1 : ℝ) ^ (r : ℕ) * (-1 : ℝ) ^ ((r : ℕ) + 1) = -1 := by
      intro r
      rw [← pow_add, show (r : ℕ) + ((r : ℕ) + 1) = 2 * r + 1 by ring, pow_succ, pow_mul]
      norm_num
    rw [Finset.prod_congr rfl fun r _ => this r, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [← mul_assoc, hsign]

/-- **Hessenberg–Wronski identity.**  If `Σ_{k ≤ m} (−1)^k a_k β_{m−k} = [m = 0]` for all `m`, then
`a₀^{n+1} β_n` is the Toeplitz minor of `a` with rows `0, …, n−1` and columns `1, …, n`. -/
theorem pow_mul_eq_toeplitzMinor_hessenberg {a β : ℕ → ℝ}
    (hβ : ∀ m, ∑ k ∈ range (m + 1), (-1 : ℝ) ^ k * a k * β (m - k) = if m = 0 then 1 else 0)
    (n : ℕ) :
    a 0 ^ (n + 1) * β n = toeplitzMinor a n (fun r => (r : ℕ)) (fun c => (c : ℕ) + 1) := by
  classical
  set s : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * a k with hs
  set L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => zext s ((i : ℕ) - ((j : ℕ) : ℤ)) with hL
  set v : Fin (n + 1) → ℝ := fun j => β j with hv
  have hLv : L *ᵥ v = Pi.single 0 1 := by
    funext i
    have hsum : (L *ᵥ v) i = ∑ k ∈ range ((i : ℕ) + 1), s k * β ((i : ℕ) - k) := by
      simp only [Matrix.mulVec, dotProduct, hL, hv, Matrix.of_apply]
      rw [Fin.sum_univ_eq_sum_range (fun j => zext s ((i : ℕ) - (j : ℤ)) * β j) (n + 1)]
      rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show (i : ℕ) + 1 ≤ n + 1 by omega))
        (fun j hj hji => by
          have hj' : j < n + 1 := Finset.mem_range.mp hj
          have hji' : ¬ j < (i : ℕ) + 1 := fun h => hji (Finset.mem_range.mpr h)
          rw [zext_of_neg s (by omega), zero_mul])]
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < (i : ℕ) + 1 := Finset.mem_range.mp hk
      rw [show ((i : ℕ) : ℤ) - (((i : ℕ) + 1 - 1 - k : ℕ) : ℤ) = (k : ℤ) by push_cast [show k ≤ (i : ℕ) by omega, show (i : ℕ) + 1 - 1 - k = (i : ℕ) - k by omega]; omega,
        zext_natCast, show (i : ℕ) + 1 - 1 - k = (i : ℕ) - k by omega]
    rw [hsum]
    have h := hβ i
    simp only [hs] at h ⊢
    rw [h]
    by_cases hi : i = 0
    · subst hi
      simp
    · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      rw [if_neg hi', Pi.single_eq_of_ne hi]
  have hdetL : L.det = a 0 ^ (n + 1) := by
    rw [Matrix.det_of_lowerTriangular L ?_]
    · have hdiag : ∀ i : Fin (n + 1), L i i = a 0 := by
        intro i
        simp only [hL, Matrix.of_apply, sub_self]
        rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, zext_natCast]
        simp [hs]
      rw [Finset.prod_congr rfl fun i _ => hdiag i, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    · intro i j hij
      have hij' : i < j := by simpa using hij
      simp only [hL, Matrix.of_apply]
      apply zext_of_neg
      have : (i : ℕ) < j := hij'
      omega
  have hcr : Matrix.cramer L (Pi.single 0 1) = L.det • v := by
    rw [← hLv, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hlast := congrFun hcr (Fin.last n)
  rw [Matrix.cramer_apply, Pi.smul_apply, smul_eq_mul, hdetL] at hlast
  have hvl : v (Fin.last n) = β n := by simp [hv]
  rw [hvl] at hlast
  rw [← hlast, Matrix.det_succ_column _ (Fin.last n), Finset.sum_eq_single (0 : Fin (n + 1))]
  · rw [Matrix.updateCol_self, Pi.single_eq_same, mul_one, Fin.val_zero, zero_add,
      Fin.val_last, Fin.succAbove_zero, Fin.succAbove_last]
    have hsub : (L.updateCol (Fin.last n) (Pi.single 0 1)).submatrix Fin.succ Fin.castSucc =
        Matrix.of fun r c : Fin n => zext s (((r : ℕ) + 1 : ℤ) - (c : ℕ)) := by
      ext r c
      simp only [Matrix.submatrix_apply, Matrix.of_apply]
      rw [Matrix.updateCol_ne (Fin.castSucc_lt_last c).ne]
      simp only [hL, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
        Nat.cast_one]
    rw [hsub, hs, det_hessenberg_alternating, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  · intro i _ hi
    rw [Matrix.updateCol_self, Pi.single_eq_of_ne hi, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **`PF_n` makes the alternating reciprocal coefficient `β_n` nonnegative.** -/
theorem hessenberg_reciprocal_nonneg {k : ℕ} {a β : ℕ → ℝ} (ha : PFSeq k a) (ha0 : 0 < a 0)
    (hβ : ∀ m, ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * a j * β (m - j) = if m = 0 then 1 else 0)
    {n : ℕ} (hn : n ≤ k) : 0 ≤ β n := by
  have h := pow_mul_eq_toeplitzMinor_hessenberg hβ n
  have hmin := ha n hn (fun r => (r : ℕ)) (fun c => (c : ℕ) + 1) Fin.val_strictMono
    (fun c c' hcc' => by simpa using Fin.val_strictMono hcc')
  rw [← h] at hmin
  exact (mul_nonneg_iff_of_pos_left (pow_pos ha0 _)).mp hmin

end

end GaloisForLFunctions.HTGeometry
