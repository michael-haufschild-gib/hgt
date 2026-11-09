import Mathlib

/-!
# The point count of `Spec ℤ` is logarithmic

The Lefschetz number of the degree-`n` Frobenius graph of `Spec ℤ` is
`N(n) = Λ(n) + 1 + 1/(n² − 1)`.

* `N(n)` is not a natural number when `n ≥ 2` is not a prime power, so no family of sets has
  cardinalities `N(n)` (`specPointCount_ne_natCast`, `not_exists_card_eq_specPointCount`).
* `Λ(n) = log Φ_n(1)` for `n ≥ 2`: the prime part of the count is the logarithm of the order of
  `ℤ[X]/(Φ_n, X − 1)`, the intersection of the primitive `n`-torsion with the fixed point `1`
  (`vonMangoldt_eq_log_eval_one_cyclotomic`).
* Modulo `p` the primitive `p^k`-torsion collapses onto the fixed point:
  `Φ_{p^k} ≡ (X − 1)^{p^k − p^{k−1}}` (`cyclotomic_prime_pow_zmod`).
-/

open Polynomial ArithmeticFunction

namespace GaloisForLFunctions.SignFreePurityMechanisms

/-- The point count of `Spec ℤ` at degree `n`: prime part, pole and trivial zeros. -/
noncomputable def specPointCount (n : ℕ) : ℝ := Λ n + 1 + 1 / ((n : ℝ) ^ 2 - 1)

/-- Away from prime powers the count lies strictly between `1` and `2`. -/
theorem specPointCount_mem_Ioo {n : ℕ} (hn : 2 ≤ n) (hpp : ¬IsPrimePow n) :
    specPointCount n ∈ Set.Ioo (1 : ℝ) 2 := by
  have hΛ : Λ n = 0 := vonMangoldt_eq_zero_iff.mpr hpp
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (1 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hfrac : 1 / ((n : ℝ) ^ 2 - 1) < 1 := by
    rw [div_lt_one (by linarith)]; exact hden
  have hpos : 0 < 1 / ((n : ℝ) ^ 2 - 1) := by positivity
  rw [specPointCount, hΛ]
  constructor <;> linarith

/-- The count is not a natural number away from prime powers. -/
theorem specPointCount_ne_natCast {n : ℕ} (hn : 2 ≤ n) (hpp : ¬IsPrimePow n) (k : ℕ) :
    specPointCount n ≠ k := by
  obtain ⟨h1, h2⟩ := specPointCount_mem_Ioo hn hpp
  intro h
  rw [h] at h1 h2
  have h1' : 1 < k := by exact_mod_cast h1
  have h2' : k < 2 := by exact_mod_cast h2
  omega

theorem not_isPrimePow_six : ¬IsPrimePow 6 := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, -, h⟩
  have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow (h ▸ (by norm_num : 2 ∣ 6)))
  have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow (h ▸ (by norm_num : 3 ∣ 6)))
  omega

/-- No family of finite sets has the point counts of `Spec ℤ` as cardinalities. -/
theorem not_exists_card_eq_specPointCount :
    ¬∃ Fix : ℕ → Type, ∀ n, 2 ≤ n → (Nat.card (Fix n) : ℝ) = specPointCount n := by
  rintro ⟨Fix, h⟩
  exact specPointCount_ne_natCast (by norm_num) not_isPrimePow_six _ (h 6 (by norm_num)).symm

/-- The von Mangoldt function is the logarithm of the value of the cyclotomic polynomial at the
fixed point `1`. -/
theorem vonMangoldt_eq_log_eval_one_cyclotomic {n : ℕ} (hn : 2 ≤ n) :
    Λ n = Real.log ((cyclotomic n ℤ).eval 1) := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    haveI : Fact p.Prime := ⟨hp⟩
    rw [vonMangoldt_apply_pow j.succ_ne_zero, vonMangoldt_apply_prime hp,
      eval_one_cyclotomic_prime_pow]
    norm_cast
  · have h1 : (cyclotomic n ℤ).eval 1 = 1 :=
      eval_one_cyclotomic_not_prime_pow fun {p} hp k hpk => by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [pow_zero] at hpk; omega
        · exact hpp ((isPrimePow_nat_iff n).mpr ⟨p, k, hp, hk, hpk⟩)
    rw [vonMangoldt_eq_zero_iff.mpr hpp, h1]
    simp

/-- Modulo `p` the primitive `p^k`-torsion is the fixed point `1` with multiplicity
`p^k − p^{k−1}`. -/
theorem cyclotomic_prime_pow_zmod (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    cyclotomic (p ^ k) (ZMod p) = (X - 1) ^ (p ^ k - p ^ (k - 1)) := by
  have h := cyclotomic_mul_prime_pow_eq (ZMod p) (m := 1)
    (by simpa using (Fact.out : p.Prime).ne_one) hk
  rwa [mul_one, cyclotomic_one] at h

end GaloisForLFunctions.SignFreePurityMechanisms
