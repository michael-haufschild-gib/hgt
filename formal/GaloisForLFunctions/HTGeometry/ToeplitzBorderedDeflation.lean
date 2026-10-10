import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityOrderK

/-!
# Deflating a totally positive sequence along its ratio limit

Call `b : ℕ → ℝ` *consecutive-row totally positive* (`ConsecutiveRowTP`) when every Toeplitz minor
with consecutive rows `i₀, …, i₀ + m − 1` and arbitrary increasing columns is nonnegative.  For
`ρ : ℝ` let `b'_n = b_n − ρ b_{n−1}` (`deflateSeq`): the coefficients of `(1 − ρy) Σ b_n yⁿ`.

**Bordered limit** (`tendsto_toeplitzMinor_bordered`).  If `b_N > 0` and `b_{N+1}/b_N → ρ`, then for
consecutive rows `i₀, …, i₀ + m − 1` and columns `j`,

  `det (b'_{j_c − i₀ − r})_{r,c < m} = lim_N det (b_{col_c − i₀ − r})_{r,c ≤ m} / b_{N − i₀ − m}`,

where `col = (j, N)` borders the minor by one far column and the next consecutive row.  Indeed the
bordered minor divided by `b_{N−i₀−m}` has last column `b_{N−i₀−r}/b_{N−i₀−m} → ρ^{m−r}`.  For the
limiting matrix, the row operations `row_r ← row_r − ρ row_{r+1}` (an upper unitriangular factor)
clear the last column down to `e_m`, and the remaining block is the Toeplitz block of `b'`.

Consequently consecutive-row total positivity passes from `b` to `b'`
(`ConsecutiveRowTP.deflate`).  This is the deflation step of the Aissen–Schoenberg–Whitney–Edrei
mechanism: removing the leading pole `1/ρ` of `Σ b_n yⁿ` keeps the consecutive-row minors
nonnegative.
-/

open Finset Filter Topology Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every Toeplitz minor with consecutive rows and increasing columns is nonnegative. -/
def ConsecutiveRowTP (b : ℕ → ℝ) : Prop :=
  ∀ (m i₀ : ℕ) (j : Fin m → ℕ), StrictMono j →
    0 ≤ toeplitzMinor b m (fun r => i₀ + (r : ℕ)) j

/-- The deflated sequence `b'_n = b_n − ρ b_{n−1}`: coefficients of `(1 − ρy) Σ b_n yⁿ`. -/
def deflateSeq (b : ℕ → ℝ) (ρ : ℝ) (n : ℕ) : ℝ := b n - ρ * zext b ((n : ℤ) - 1)

theorem zext_deflateSeq (b : ℕ → ℝ) (ρ : ℝ) (z : ℤ) :
    zext (deflateSeq b ρ) z = zext b z - ρ * zext b (z - 1) := by
  rcases lt_or_ge z 0 with hz | hz
  · rw [zext_of_neg _ hz, zext_of_neg _ hz, zext_of_neg _ (by omega)]
    ring
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [zext_natCast, zext_natCast]
    rfl

/-- The upper bidiagonal row-operation matrix `1 − ρ S`. -/
def rowOpMatrix (m : ℕ) (ρ : ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun r k => if k = r then 1 else if (k : ℕ) = (r : ℕ) + 1 then -ρ else 0

theorem det_rowOpMatrix (m : ℕ) (ρ : ℝ) : (rowOpMatrix m ρ).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun r _ => ?_
    simp [rowOpMatrix]
  · intro r k hkr
    have hk : (k : ℕ) < r := hkr
    simp only [rowOpMatrix, Matrix.of_apply]
    rw [if_neg (by intro h; rw [h] at hk; exact lt_irrefl _ hk), if_neg (by omega)]

theorem rowOpMatrix_mul_apply (m : ℕ) (ρ : ℝ) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (r c : Fin (m + 1)) :
    (rowOpMatrix m ρ * M) r c =
      M r c - (if h : (r : ℕ) + 1 < m + 1 then ρ * M ⟨(r : ℕ) + 1, h⟩ c else 0) := by
  rw [Matrix.mul_apply]
  simp only [rowOpMatrix, Matrix.of_apply]
  have hsplit : ∀ k : Fin (m + 1), (if k = r then (1 : ℝ) else if (k : ℕ) = (r : ℕ) + 1 then -ρ
      else 0) * M k c =
      (if k = r then M k c else 0) +
        (if (k : ℕ) = (r : ℕ) + 1 then -ρ * M k c else 0) := by
    intro k
    by_cases hkr : k = r
    · subst hkr
      simp
    · by_cases hk1 : (k : ℕ) = (r : ℕ) + 1
      · simp [hkr, hk1]
      · simp [hkr, hk1]
  rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  split_ifs with h
  · have : ∑ k : Fin (m + 1), (if (k : ℕ) = (r : ℕ) + 1 then -ρ * M k c else 0) =
        -ρ * M ⟨(r : ℕ) + 1, h⟩ c := by
      rw [Finset.sum_eq_single ⟨(r : ℕ) + 1, h⟩]
      · simp
      · intro k _ hk
        rw [if_neg]
        intro hk'
        exact hk (Fin.ext hk')
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    rw [this]
    ring
  · have : ∑ k : Fin (m + 1), (if (k : ℕ) = (r : ℕ) + 1 then -ρ * M k c else 0) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg]
      intro hk'
      have := k.2
      omega
    rw [this]
    ring

/-- The limiting bordered matrix: Toeplitz columns of `b` and last column `ρ^{m−r}`. -/
def borderedLimitMatrix (b : ℕ → ℝ) (ρ : ℝ) {m : ℕ} (i₀ : ℕ) (j : Fin m → ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun r c => Fin.lastCases (ρ ^ (m - (r : ℕ)))
    (fun c' : Fin m => zext b ((j c' : ℤ) - ((i₀ + (r : ℕ) : ℕ) : ℤ))) c

/-- **The row-operation identity.**  The bordered limiting determinant is the consecutive-row
Toeplitz minor of the deflated sequence. -/
theorem det_borderedLimitMatrix (b : ℕ → ℝ) (ρ : ℝ) {m : ℕ} (i₀ : ℕ) (j : Fin m → ℕ) :
    (borderedLimitMatrix b ρ i₀ j).det =
      toeplitzMinor (deflateSeq b ρ) m (fun r => i₀ + (r : ℕ)) j := by
  set M := borderedLimitMatrix b ρ i₀ j with hM
  have hdet : (rowOpMatrix m ρ * M).det = M.det := by
    rw [Matrix.det_mul, det_rowOpMatrix, one_mul]
  rw [← hdet, Matrix.det_succ_column _ (Fin.last m), Finset.sum_eq_single (Fin.last m)]
  · have hlast : (rowOpMatrix m ρ * M) (Fin.last m) (Fin.last m) = 1 := by
      rw [rowOpMatrix_mul_apply, dif_neg (by simp)]
      simp [hM, borderedLimitMatrix]
    rw [hlast, mul_one, Fin.succAbove_last, Fin.val_last, ← two_mul, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul]
    unfold toeplitzMinor
    congr 1
    ext r c
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    rw [rowOpMatrix_mul_apply, dif_pos (by simp only [Fin.val_castSucc]; omega)]
    simp only [hM, borderedLimitMatrix, Matrix.of_apply, Fin.lastCases_castSucc]
    rw [zext_deflateSeq]
    congr 2
    all_goals first
      | (push_cast; done)
      | (congr 1; push_cast [Fin.val_castSucc]; ring)
  · intro r _ hr
    have hr' : (r : ℕ) < m := by
      have := r.2
      have hne : (r : ℕ) ≠ m := fun h => hr (Fin.ext (by simpa using h))
      omega
    rw [rowOpMatrix_mul_apply, dif_pos (by omega)]
    simp only [hM, borderedLimitMatrix, Matrix.of_apply, Fin.lastCases_last]
    have : ρ ^ (m - (r : ℕ)) - ρ * ρ ^ (m - ((r : ℕ) + 1)) = 0 := by
      rw [← pow_succ', show m - ((r : ℕ) + 1) + 1 = m - (r : ℕ) by omega, sub_self]
    rw [this, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Ratios along a shift: `b_{K+s}/b_K → ρ^s` when consecutive ratios tend to `ρ`. -/
theorem tendsto_ratio_shift {b : ℕ → ℝ} {ρ : ℝ} (hpos : ∀ N, 0 < b N)
    (hratio : Tendsto (fun N => b (N + 1) / b N) atTop (𝓝 ρ)) (s : ℕ) :
    Tendsto (fun K => b (K + s) / b K) atTop (𝓝 (ρ ^ s)) := by
  induction s with
  | zero =>
    simp only [add_zero, pow_zero]
    exact tendsto_const_nhds.congr fun K => (div_self (hpos K).ne').symm
  | succ s ih =>
    have hshift : Tendsto (fun K => b (K + s + 1) / b (K + s)) atTop (𝓝 ρ) :=
      hratio.comp (tendsto_add_atTop_nat s)
    have := hshift.mul ih
    rw [pow_succ']
    refine this.congr fun K => ?_
    rw [show K + (s + 1) = K + s + 1 by ring]
    field_simp [(hpos (K + s)).ne', (hpos K).ne']

/-- **Bordered limit.**  If `b > 0` and `b_{N+1}/b_N → ρ`, the consecutive-row Toeplitz minors of the
deflated sequence are limits of bordered minors of `b` divided by `b_{N − i₀ − m}`. -/
theorem tendsto_toeplitzMinor_bordered {b : ℕ → ℝ} {ρ : ℝ} (hpos : ∀ N, 0 < b N)
    (hratio : Tendsto (fun N => b (N + 1) / b N) atTop (𝓝 ρ)) (m i₀ : ℕ) (j : Fin m → ℕ) :
    Tendsto (fun N => toeplitzMinor b (m + 1) (fun r => i₀ + (r : ℕ))
        (Fin.lastCases (motive := fun _ => ℕ) N j) / b (N - i₀ - m)) atTop
      (𝓝 (toeplitzMinor (deflateSeq b ρ) m (fun r => i₀ + (r : ℕ)) j)) := by
  rw [← det_borderedLimitMatrix]
  -- the bordered minor divided by `b_{N−i₀−m}` is the determinant with a rescaled last column
  have hcol : ∀ r : Fin (m + 1), Tendsto (fun N : ℕ => zext b ((N : ℤ) - ((i₀ + (r : ℕ) : ℕ) : ℤ)) /
      b (N - i₀ - m)) atTop (𝓝 (ρ ^ (m - (r : ℕ)))) := by
    intro r
    have hr : (r : ℕ) ≤ m := Nat.lt_succ_iff.mp r.2
    have h := (tendsto_ratio_shift hpos hratio (m - (r : ℕ))).comp
      (tendsto_sub_atTop_nat (i₀ + m))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (i₀ + m)] with N hN
    simp only [Function.comp_apply]
    rw [show ((N : ℤ) - ((i₀ + (r : ℕ) : ℕ) : ℤ)) = ((N - (i₀ + (r : ℕ)) : ℕ) : ℤ) by
        push_cast [show i₀ + (r : ℕ) ≤ N by omega]; ring, zext_natCast,
      show N - (i₀ + m) + (m - (r : ℕ)) = N - (i₀ + (r : ℕ)) by omega,
      show N - i₀ - m = N - (i₀ + m) by omega]
  have hmat : Tendsto (fun N : ℕ => (Matrix.of fun r c => Fin.lastCases
      (zext b ((N : ℤ) - ((i₀ + (r : ℕ) : ℕ) : ℤ)) / b (N - i₀ - m))
      (fun c' : Fin m => zext b ((j c' : ℤ) - ((i₀ + (r : ℕ) : ℕ) : ℤ))) c :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) atTop (𝓝 (borderedLimitMatrix b ρ i₀ j)) := by
    refine tendsto_pi_nhds.2 fun r => tendsto_pi_nhds.2 fun c => ?_
    refine Fin.lastCases ?_ (fun c' => ?_) c
    · simp only [Matrix.of_apply, Fin.lastCases_last, borderedLimitMatrix]
      exact hcol r
    · simp only [Matrix.of_apply, Fin.lastCases_castSucc, borderedLimitMatrix]
      exact tendsto_const_nhds
  have hdet := ((continuous_id.matrix_det).tendsto _).comp hmat
  refine hdet.congr fun N => ?_
  simp only [Function.comp_apply, id]
  -- identify the rescaled determinant with the bordered minor divided by `b_{N−i₀−m}`
  set A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of fun r c =>
    zext b (((Fin.lastCases (motive := fun _ => ℕ) N j c : ℕ) : ℤ) - ((i₀ + (r : ℕ) : ℕ) : ℤ))
    with hA
  have hupd : (Matrix.of fun r c => Fin.lastCases
      (zext b ((N : ℤ) - ((i₀ + (r : ℕ) : ℕ) : ℤ)) / b (N - i₀ - m))
      (fun c' : Fin m => zext b ((j c' : ℤ) - ((i₀ + (r : ℕ) : ℕ) : ℤ))) c :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
      A.updateCol (Fin.last m) ((b (N - i₀ - m))⁻¹ • fun r => A r (Fin.last m)) := by
    ext r c
    refine Fin.lastCases ?_ (fun c' => ?_) c
    · simp only [Matrix.of_apply, Fin.lastCases_last, Matrix.updateCol_self, Pi.smul_apply,
        smul_eq_mul, hA]
      ring
    · rw [Matrix.updateCol_ne (Fin.castSucc_lt_last c').ne]
      simp only [Matrix.of_apply, Fin.lastCases_castSucc, hA]
  show (Matrix.of fun r c => Fin.lastCases
      (zext b ((N : ℤ) - ((i₀ + (r : ℕ) : ℕ) : ℤ)) / b (N - i₀ - m))
      (fun c' : Fin m => zext b ((j c' : ℤ) - ((i₀ + (r : ℕ) : ℕ) : ℤ))) c :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det =
    toeplitzMinor b (m + 1) (fun r => i₀ + (r : ℕ)) (Fin.lastCases (motive := fun _ => ℕ) N j) /
      b (N - i₀ - m)
  rw [hupd, Matrix.det_updateCol_smul, Matrix.updateCol_eq_self, div_eq_inv_mul]
  rfl

/-- **Deflation preserves consecutive-row total positivity.** -/
theorem ConsecutiveRowTP.deflate {b : ℕ → ℝ} {ρ : ℝ} (hb : ConsecutiveRowTP b)
    (hpos : ∀ N, 0 < b N) (hratio : Tendsto (fun N => b (N + 1) / b N) atTop (𝓝 ρ)) :
    ConsecutiveRowTP (deflateSeq b ρ) := by
  intro m i₀ j hj
  refine ge_of_tendsto (tendsto_toeplitzMinor_bordered hpos hratio m i₀ j) ?_
  have hbound : ∀ c : Fin m, j c < (∑ c, j c) + 1 := fun c =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
  filter_upwards [eventually_gt_atTop ((∑ c, j c) + 1)] with N hN
  refine div_nonneg (hb (m + 1) i₀ _ ?_) (hpos _).le
  intro c c' hcc'
  refine Fin.lastCases (motive := fun c' => c < c' →
    Fin.lastCases (motive := fun _ => ℕ) N j c < Fin.lastCases (motive := fun _ => ℕ) N j c')
    ?_ (fun c₂ => ?_) c' hcc'
  · intro hlt
    refine Fin.lastCases (motive := fun c => c < Fin.last m →
      Fin.lastCases (motive := fun _ => ℕ) N j c < Fin.lastCases (motive := fun _ => ℕ) N j
        (Fin.last m)) (fun h => absurd h (lt_irrefl _)) (fun c₁ _ => ?_) c hlt
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    have := hbound c₁
    omega
  · intro hlt
    refine Fin.lastCases (motive := fun c => c < Fin.castSucc c₂ →
      Fin.lastCases (motive := fun _ => ℕ) N j c < Fin.lastCases (motive := fun _ => ℕ) N j
        (Fin.castSucc c₂)) (fun h => ?_) (fun c₁ h => ?_) c hlt
    · exact absurd h (not_lt.mpr (Fin.castSucc_lt_last c₂).le)
    · simp only [Fin.lastCases_castSucc]
      exact hj (Fin.castSucc_lt_castSucc_iff.mp h)

/-- Consecutive-row total positivity up to order `k`. -/
def ConsecutiveRowTPUpTo (k : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ m ≤ k, ∀ (i₀ : ℕ) (j : Fin m → ℕ), StrictMono j →
    0 ≤ toeplitzMinor b m (fun r => i₀ + (r : ℕ)) j

theorem ConsecutiveRowTP.upTo {b : ℕ → ℝ} (hb : ConsecutiveRowTP b) (k : ℕ) :
    ConsecutiveRowTPUpTo k b := fun m _ i₀ j hj => hb m i₀ j hj

theorem consecutiveRowTP_of_forall_upTo {b : ℕ → ℝ} (hb : ∀ k, ConsecutiveRowTPUpTo k b) :
    ConsecutiveRowTP b := fun m i₀ j hj => hb m m le_rfl i₀ j hj

/-- **Deflation lowers the order of consecutive-row total positivity by one.** -/
theorem ConsecutiveRowTPUpTo.deflate {k : ℕ} {b : ℕ → ℝ} {ρ : ℝ}
    (hb : ConsecutiveRowTPUpTo (k + 1) b) (hpos : ∀ N, 0 < b N)
    (hratio : Tendsto (fun N => b (N + 1) / b N) atTop (𝓝 ρ)) :
    ConsecutiveRowTPUpTo k (deflateSeq b ρ) := by
  intro m hm i₀ j hj
  refine ge_of_tendsto (tendsto_toeplitzMinor_bordered hpos hratio m i₀ j) ?_
  have hbound : ∀ c : Fin m, j c < (∑ c, j c) + 1 := fun c =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
  filter_upwards [eventually_gt_atTop ((∑ c, j c) + 1)] with N hN
  refine div_nonneg (hb (m + 1) (by omega) i₀ _ ?_) (hpos _).le
  intro c c' hcc'
  refine Fin.lastCases (motive := fun c' => c < c' →
    Fin.lastCases (motive := fun _ => ℕ) N j c < Fin.lastCases (motive := fun _ => ℕ) N j c')
    ?_ (fun c₂ => ?_) c' hcc'
  · intro hlt
    refine Fin.lastCases (motive := fun c => c < Fin.last m →
      Fin.lastCases (motive := fun _ => ℕ) N j c < Fin.lastCases (motive := fun _ => ℕ) N j
        (Fin.last m)) (fun h => absurd h (lt_irrefl _)) (fun c₁ _ => ?_) c hlt
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    have := hbound c₁
    omega
  · intro hlt
    refine Fin.lastCases (motive := fun c => c < Fin.castSucc c₂ →
      Fin.lastCases (motive := fun _ => ℕ) N j c < Fin.lastCases (motive := fun _ => ℕ) N j
        (Fin.castSucc c₂)) (fun h => ?_) (fun c₁ h => ?_) c hlt
    · exact absurd h (not_lt.mpr (Fin.castSucc_lt_last c₂).le)
    · simp only [Fin.lastCases_castSucc]
      exact hj (Fin.castSucc_lt_castSucc_iff.mp h)

end

end GaloisForLFunctions.HTGeometry
