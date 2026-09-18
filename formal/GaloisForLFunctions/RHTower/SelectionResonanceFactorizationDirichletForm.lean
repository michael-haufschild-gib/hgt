import GaloisForLFunctions.RHTower.SelectionResonanceFactorizationBlock

/-!
# The factorized polynomial is a Dirichlet polynomial with bounded coefficients

`D(u) = (2^{iu} + 3^{iu}) Σ_{3m⁴ ≤ k ≤ 4m⁴} (k/4m⁴)^{20} k^{iu}` equals
`Σ_{6m⁴ ≤ n ≤ 12m⁴} a_n n^{iu}` with `a_n = (n/2 / 4m⁴)^{20}` for even `n ≤ 8m⁴`,
`a_n = (n/3 / 4m⁴)^{20}` for `9m⁴ ≤ n ≤ 12m⁴` divisible by three, and `a_n = 0` otherwise;
all `|a_n| ≤ 1`.  So `D` is a Dirichlet polynomial of length `N = 6m⁴` supported on `[N, 2N]`
with coefficients of modulus at most one.
-/

open Complex Finset

namespace RHTower

noncomputable section

/-- The coefficients of the factorized polynomial on `[6m⁴, 12m⁴]`. -/
def resCoeff (m : ℕ) (n : ℕ) : ℂ :=
  if 2 ∣ n ∧ n ≤ 8 * m ^ 4 then ((n / 2 : ℕ) : ℂ) ^ 20 / ((4 * m ^ 4 : ℕ) : ℂ) ^ 20
  else if 3 ∣ n ∧ 9 * m ^ 4 ≤ n ∧ n ≤ 12 * m ^ 4 then
    ((n / 3 : ℕ) : ℂ) ^ 20 / ((4 * m ^ 4 : ℕ) : ℂ) ^ 20
  else 0

theorem norm_resCoeff_le (m n : ℕ) : ‖resCoeff m n‖ ≤ 1 := by
  unfold resCoeff
  split_ifs with h1 h2
  · rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    by_cases hK0 : ((4 * m ^ 4 : ℕ) : ℝ) = 0
    · rw [hK0]; simp
    · rw [div_le_one (by positivity)]
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast (by omega : n / 2 ≤ 4 * m ^ 4)
  · rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    by_cases hK0 : ((4 * m ^ 4 : ℕ) : ℝ) = 0
    · rw [hK0]; simp
    · rw [div_le_one (by positivity)]
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast (by omega : n / 3 ≤ 4 * m ^ 4)
  · simp

theorem filter_even_eq_image (m : ℕ) :
    (Finset.Icc (6 * m ^ 4) (12 * m ^ 4)).filter (fun n => 2 ∣ n ∧ n ≤ 8 * m ^ 4) =
      (Finset.Icc (3 * m ^ 4) (4 * m ^ 4)).image (fun k => 2 * k) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨k, hk⟩, h3⟩
    exact ⟨k, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩, by omega⟩

theorem filter_three_eq_image {m : ℕ} (hm : 1 ≤ m) :
    ((Finset.Icc (6 * m ^ 4) (12 * m ^ 4)).filter (fun n => ¬(2 ∣ n ∧ n ≤ 8 * m ^ 4))).filter
        (fun n => 3 ∣ n ∧ 9 * m ^ 4 ≤ n ∧ n ≤ 12 * m ^ 4) =
      (Finset.Icc (3 * m ^ 4) (4 * m ^ 4)).image (fun k => 3 * k) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, _⟩, ⟨k, hk⟩, h3, h4⟩
    exact ⟨k, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, ⟨k, rfl⟩, by omega, by omega⟩
    rintro ⟨_, h⟩
    have : 0 < m ^ 4 := pow_pos (by omega) 4
    omega

theorem natCast_mul_cpow (a k : ℕ) (u : ℝ) :
    ((a * k : ℕ) : ℂ) ^ ((u : ℂ) * I) = (a : ℂ) ^ ((u : ℂ) * I) * (k : ℂ) ^ ((u : ℂ) * I) := by
  have h := Complex.mul_cpow_ofReal_nonneg (a := (a : ℝ)) (b := (k : ℝ)) (Nat.cast_nonneg a)
    (Nat.cast_nonneg k) ((u : ℂ) * I)
  push_cast at h ⊢
  exact h

/-- **The factorized polynomial as a Dirichlet polynomial.** -/
theorem resPoly_eq_dirichlet {m : ℕ} (hm : 1 ≤ m) (u : ℝ) :
    resPoly m u =
      ∑ n ∈ Finset.Icc (6 * m ^ 4) (12 * m ^ 4), resCoeff m n * (n : ℂ) ^ ((u : ℂ) * I) := by
  -- the right-hand side, split by the two supports
  have hsplit : (∑ n ∈ Finset.Icc (6 * m ^ 4) (12 * m ^ 4), resCoeff m n * (n : ℂ) ^ ((u : ℂ) * I)) =
      ∑ k ∈ Finset.Icc (3 * m ^ 4) (4 * m ^ 4),
          (((k : ℕ) : ℂ) ^ 20 / ((4 * m ^ 4 : ℕ) : ℂ) ^ 20) * ((2 * k : ℕ) : ℂ) ^ ((u : ℂ) * I) +
        ∑ k ∈ Finset.Icc (3 * m ^ 4) (4 * m ^ 4),
          (((k : ℕ) : ℂ) ^ 20 / ((4 * m ^ 4 : ℕ) : ℂ) ^ 20) * ((3 * k : ℕ) : ℂ) ^ ((u : ℂ) * I) := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun n => 2 ∣ n ∧ n ≤ 8 * m ^ 4)]
    rw [← Finset.sum_filter_add_sum_filter_not
      ((Finset.Icc (6 * m ^ 4) (12 * m ^ 4)).filter (fun n => ¬(2 ∣ n ∧ n ≤ 8 * m ^ 4)))
      (fun n => 3 ∣ n ∧ 9 * m ^ 4 ≤ n ∧ n ≤ 12 * m ^ 4)]
    have hzero : ∑ n ∈ ((Finset.Icc (6 * m ^ 4) (12 * m ^ 4)).filter
        (fun n => ¬(2 ∣ n ∧ n ≤ 8 * m ^ 4))).filter
        (fun n => ¬(3 ∣ n ∧ 9 * m ^ 4 ≤ n ∧ n ≤ 12 * m ^ 4)),
        resCoeff m n * (n : ℂ) ^ ((u : ℂ) * I) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp only [Finset.mem_filter] at hn
      unfold resCoeff
      rw [if_neg hn.1.2, if_neg hn.2, zero_mul]
    rw [hzero, add_zero, filter_even_eq_image, filter_three_eq_image hm,
      Finset.sum_image (fun x _ y _ h => by omega), Finset.sum_image (fun x _ y _ h => by omega)]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      unfold resCoeff
      have hk' := Finset.mem_Icc.mp hk
      rw [if_pos ⟨⟨k, rfl⟩, by omega⟩, Nat.mul_div_cancel_left k (by norm_num)]
    · apply Finset.sum_congr rfl
      intro k hk
      unfold resCoeff
      have hk' := Finset.mem_Icc.mp hk
      have hm4 : 0 < m ^ 4 := pow_pos (by omega) 4
      rw [if_neg (by rintro ⟨_, h⟩; omega), if_pos ⟨⟨k, rfl⟩, by omega, by omega⟩,
        Nat.mul_div_cancel_left k (by norm_num)]
  rw [hsplit]
  -- the left-hand side
  unfold resPoly resBlock blockSum
  rw [add_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := by
    have h1 := (Finset.mem_Icc.mp hk).1
    have : 0 < m ^ 4 := pow_pos (by omega) 4
    omega
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hs : (k : ℂ) ^ blockExponent 20 u = (k : ℂ) ^ 20 * (k : ℂ) ^ ((u : ℂ) * I) := by
    unfold blockExponent
    rw [Complex.cpow_add _ _ hk0, Complex.cpow_natCast]
  rw [hs, natCast_mul_cpow, natCast_mul_cpow]
  push_cast
  ring

end

end RHTower
