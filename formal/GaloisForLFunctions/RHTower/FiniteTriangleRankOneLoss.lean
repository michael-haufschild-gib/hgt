import GaloisForLFunctions.RHTower.FiniteSignedTriangleBound

/-!
# Exact loss of triangle averaging on a positive rank-one form

The constant matrix is positive semidefinite. Its triangle-corrected separate
bound nevertheless becomes negative in dimension greater than three. All sums
are evaluated symbolically, by diagonal subtraction rather than enumeration.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_distinct_triple_weight (f : ι → ℝ) :
    (∑ i, ∑ j, ∑ k, if i = j ∨ i = k ∨ j = k then 0 else f i + f j + f k) =
      3 * ((Fintype.card ι : ℝ) - 1) * ((Fintype.card ι : ℝ) - 2) * ∑ i, f i := by
  have hpoint (i j k : ι) :
      (if i = j ∨ i = k ∨ j = k then 0 else f i + f j + f k) =
        (f i + f j + f k) - (if i = j then f i + f j + f k else 0) -
        (if i = k then f i + f j + f k else 0) -
        (if j = k then f i + f j + f k else 0) +
        2 * (if i = j ∧ j = k then f i + f j + f k else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k; simp; ring
      · simp [hik]
    · by_cases hik : i = k
      · subst k; simp [hij, Ne.symm hij]
      · by_cases hjk : j = k
        · subst k; simp [hij]
        · simp [hij, hik, hjk]
  have hfull : (∑ i, ∑ j, ∑ k, (f i + f j + f k)) =
      3 * (Fintype.card ι : ℝ) ^ 2 * ∑ i, f i := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  have h₁ : (∑ i, ∑ j, ∑ k, if i = j then f i + f j + f k else 0) =
      3 * Fintype.card ι * ∑ i, f i := by
    calc
      _ = ∑ i, ∑ k, ∑ j, if i = j then f i + f j + f k else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
        ring
  have h₂ : (∑ i, ∑ j, ∑ k, if i = k then f i + f j + f k else 0) =
      3 * Fintype.card ι * ∑ i, f i := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have h₃ : (∑ i, ∑ j, ∑ k, if j = k then f i + f j + f k else 0) =
      3 * Fintype.card ι * ∑ i, f i := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have h₄ : (∑ i, ∑ j, ∑ k, if i = j ∧ j = k then f i + f j + f k else 0) =
      3 * ∑ i, f i := by
    have he (i j : ι) : (∑ k, if i = j ∧ j = k then f i + f j + f k else 0) =
        if i = j then 3 * f i else 0 := by
      by_cases h : i = j
      · subst j; simp; ring
      · simp [h]
    simp only [he, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib] at hfull
  rw [hfull, h₁, h₂, h₃, h₄]
  ring

theorem signedTriangleGain_constant {p : ℝ} (hp : 0 ≤ p) : signedTriangleGain p p p = p := by
  simp only [signedTriangleGain, max_eq_left hp, max_eq_right (neg_nonpos.mpr hp),
    min_self, min_eq_left hp, min_eq_right hp, max_self]

omit [Fintype ι] in
theorem signedTriangleGain_off_constant {p : ℝ} (hp : 0 ≤ p) (i j k : ι) :
    signedTriangleGain (finiteSignedOffDiagonal (fun _ _ : ι => p) i j)
      (finiteSignedOffDiagonal (fun _ _ : ι => p) i k)
      (finiteSignedOffDiagonal (fun _ _ : ι => p) j k) =
      if i = j ∨ i = k ∨ j = k then 0 else p := by
  by_cases h : i = j ∨ i = k ∨ j = k
  · rw [if_pos h]
    apply signedTriangleGain_eq_zero_of_zero
    rcases h with rfl | rfl | rfl <;> simp [finiteSignedOffDiagonal]
  · have hij : i ≠ j := fun hij => h (Or.inl hij)
    have hik : i ≠ k := fun hik => h (Or.inr (Or.inl hik))
    have hjk : j ≠ k := fun hjk => h (Or.inr (Or.inr hjk))
    simp [finiteSignedOffDiagonal, hij, hik, hjk, signedTriangleGain_constant hp]

omit [DecidableEq ι] in
theorem finiteSignedQuadratic_constant (p : ℝ) (x : ι → ℝ) :
    finiteSignedQuadratic (fun _ _ : ι => p) x = p * (∑ i, x i) ^ 2 := by
  simp only [finiteSignedQuadratic, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finiteSignedSeparateLower_constant {p : ℝ} (hp : 0 ≤ p) (x : ι → ℝ) :
    finiteSignedSeparateLower (fun _ _ : ι => p) x =
      (2 - (Fintype.card ι : ℝ)) * p * ∑ i, x i ^ 2 := by
  have he (i j : ι) : |finiteSignedOffDiagonal (fun _ _ : ι => p) i j| =
      p - (if i = j then p else 0) := by
    by_cases h : i = j <;> simp [finiteSignedOffDiagonal, h, abs_of_nonneg hp]
  simp only [finiteSignedSeparateLower, he, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finiteSignedTriangleCorrection_constant {p : ℝ} (hp : 0 ≤ p)
    (hn : 3 ≤ Fintype.card ι) (x : ι → ℝ) :
    finiteSignedTriangleCorrection (fun _ _ : ι => p) x =
      ((Fintype.card ι : ℝ) - 1) / 2 * p * ∑ i, x i ^ 2 := by
  have hn' : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have he (i j k : ι) :
      signedTriangleGain (finiteSignedOffDiagonal (fun _ _ : ι => p) i j)
        (finiteSignedOffDiagonal (fun _ _ : ι => p) i k)
        (finiteSignedOffDiagonal (fun _ _ : ι => p) j k) * (x i ^ 2 + x j ^ 2 + x k ^ 2) =
      p * (if i = j ∨ i = k ∨ j = k then 0 else x i ^ 2 + x j ^ 2 + x k ^ 2) := by
    rw [signedTriangleGain_off_constant hp]
    split_ifs <;> ring
  unfold finiteSignedTriangleCorrection
  simp_rw [he]
  simp only [← Finset.mul_sum]
  rw [sum_distinct_triple_weight]
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ (Fintype.card ι : ℝ) - 2)]
  have hd : 0 < (Fintype.card ι : ℝ) - 2 := by linarith
  apply (div_eq_iff (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0) hd.ne')).mpr
  ring

/-- The exact lower bound loses positivity beyond three components, although the form is a square. -/
theorem finiteSignedTriangle_lower_constant_exact {p : ℝ} (hp : 0 ≤ p)
    (hn : 3 ≤ Fintype.card ι) (x : ι → ℝ) :
    finiteSignedSeparateLower (fun _ _ : ι => p) x +
      finiteSignedTriangleCorrection (fun _ _ : ι => p) x =
      (3 - (Fintype.card ι : ℝ)) / 2 * p * ∑ i, x i ^ 2 := by
  rw [finiteSignedSeparateLower_constant hp, finiteSignedTriangleCorrection_constant hp hn]
  ring

end RHTower
