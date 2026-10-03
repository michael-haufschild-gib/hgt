import GaloisForLFunctions.HTGeometry.BeukersZetaTwoArithmetic
import GaloisForLFunctions.HTGeometry.IrrationalityExponentOfLinearForms
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# `π` has finite irrationality exponent

Beukers' linear forms `aₙ π²/6 + bₙ = dₙ² Iₙ` (with `dₙ = lcm(1, …, n)`) satisfy
`(9/256)ⁿ/4 ≤ dₙ² Iₙ ≤ 2 (9/10)ⁿ` and `|aₙ| ≤ 2 · 288ⁿ` once `dₙ ≤ 3ⁿ`, which the prime number
theorem `ψ(x) ~ x` gives for all large `n` (as `log 3 > 1`).  The abstract criterion then bounds the
irrationality exponent of `π²/6`, and `|π² − u²| ≤ 9 |π − u|` transfers the bound to `π`.

* `eventually_lcmUpto_le_three_pow` : `lcm(1, …, n) ≤ 3ⁿ` for all large `n`.
* `exists_not_liouvilleWith_pi_sq_div_six` : `∃ K, ∀ p > K, ¬ LiouvilleWith p (π²/6)`.
* `exists_not_liouvilleWith_pi` : `∃ K, ∀ p > K, ¬ LiouvilleWith p π`.
* `not_liouville_pi` : `π` is not a Liouville number.
-/

open Filter Topology Finset Asymptotics

namespace GaloisForLFunctions.HTGeometry.BeukersZetaTwo

theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- **`lcm(1, …, n) ≤ 3ⁿ` eventually**, from the prime number theorem. -/
theorem eventually_lcmUpto_le_three_pow :
    ∀ᶠ n : ℕ in atTop, (Nat.lcmUpto n : ℝ) ≤ 3 ^ n := by
  set ε : ℝ := Real.log 3 - 1 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith [one_lt_log_three]
  have hbound := WeakPNT''.isLittleO.bound hεpos
  have hnat := tendsto_natCast_atTop_atTop.eventually hbound
  filter_upwards [hnat, eventually_gt_atTop 0] with n hn hn0
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_pos hnr] at hn
  have hpsi : Chebyshev.psi n ≤ Real.log 3 * n := by
    have := (abs_le.mp hn).2
    rw [hε] at this
    linarith
  rw [Chebyshev.psi_eq_log_lcmUpto] at hpsi
  have hpos : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  have h3 : Real.log ((3 : ℝ) ^ n) = n * Real.log 3 := by rw [Real.log_pow]
  rw [← Real.log_le_log_iff hpos (by positivity), h3]
  linarith

theorem pi_sq_div_six_le_two : Real.pi ^ 2 / 6 ≤ 2 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- **Finite irrationality exponent of `π²/6`.** -/
theorem exists_not_liouvilleWith_pi_sq_div_six :
    ∃ K : ℕ, ∀ p > (K : ℝ), ¬ LiouvilleWith p (Real.pi ^ 2 / 6) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp eventually_lcmUpto_le_three_pow
  set a : ℕ → ℤ := fun n => (-1) ^ n * beukersA n with ha
  set b : ℕ → ℤ := fun n => (-1) ^ n * beukersB n with hb
  have hform : ∀ n : ℕ, (a n : ℝ) * (Real.pi ^ 2 / 6) + b n =
      (Nat.lcmUpto n : ℝ) ^ 2 * ∫ y in Set.Ioc (0 : ℝ) 1, beukersIntegrand n y := by
    intro n
    rw [(integrable_and_integral_beukersIntegrand n).2]
    have h := lcm_sq_mul_sum_eq n
    simp only [ha, hb]
    push_cast
    have hsq : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-1 : ℝ) ^ n * h.symm + 0 * hsq
  have hd1 : ∀ n : ℕ, (1 : ℝ) ≤ (Nat.lcmUpto n : ℝ) ^ 2 := fun n => by
    have : (1 : ℝ) ≤ Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
    nlinarith
  refine IrrationalityExponent.exists_not_liouvilleWith (l := 9 / 10) (L := 288)
    (g := 9 / 256) (C := 2) (c := 1 / 4) (a := a) (b := b) (n₀ := n₀)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_ ?_
  · intro n hn
    rw [hform]
    have hI0 := integral_beukersIntegrand_ge n
    have hI := integral_beukersIntegrand_le n
    have hd := hn₀ n hn
    have hIpos : 0 ≤ ∫ y in Set.Ioc (0 : ℝ) 1, beukersIntegrand n y :=
      le_trans (by positivity) hI0
    rw [abs_of_nonneg (mul_nonneg (by positivity) hIpos)]
    have hd2 : (Nat.lcmUpto n : ℝ) ^ 2 ≤ 9 ^ n := by
      calc (Nat.lcmUpto n : ℝ) ^ 2 ≤ (3 ^ n) ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
        _ = 9 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc (Nat.lcmUpto n : ℝ) ^ 2 * ∫ y in Set.Ioc (0 : ℝ) 1, beukersIntegrand n y ≤
        9 ^ n * ((1 / 10) ^ n * (Real.pi ^ 2 / 6)) :=
          mul_le_mul hd2 hI hIpos (by positivity)
      _ = (9 / 10) ^ n * (Real.pi ^ 2 / 6) := by rw [← mul_assoc, ← mul_pow]; norm_num
      _ ≤ (9 / 10) ^ n * 2 := mul_le_mul_of_nonneg_left pi_sq_div_six_le_two (by positivity)
      _ = 2 * (9 / 10) ^ n := by ring
  · intro n hn
    rw [hform]
    have hI0 := integral_beukersIntegrand_ge n
    have hIpos : 0 ≤ ∫ y in Set.Ioc (0 : ℝ) 1, beukersIntegrand n y :=
      le_trans (by positivity) hI0
    rw [abs_of_nonneg (mul_nonneg (by positivity) hIpos)]
    calc 1 / 4 * (9 / 256 : ℝ) ^ n ≤ ∫ y in Set.Ioc (0 : ℝ) 1, beukersIntegrand n y := hI0
      _ ≤ (Nat.lcmUpto n : ℝ) ^ 2 * ∫ y in Set.Ioc (0 : ℝ) 1, beukersIntegrand n y :=
          le_mul_of_one_le_left hIpos (hd1 n)
  · intro n hn
    have hd := hn₀ n hn
    have hA := abs_beukersA_le n
    have hd2 : (Nat.lcmUpto n : ℝ) ^ 2 ≤ 9 ^ n := by
      calc (Nat.lcmUpto n : ℝ) ^ 2 ≤ (3 ^ n) ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
        _ = 9 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hn2 : ((n : ℝ) + 1) ≤ 2 ^ n := by
      have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
      exact_mod_cast this
    simp only [ha]
    push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    calc |(beukersA n : ℝ)| ≤ (Nat.lcmUpto n : ℝ) ^ 2 * ((n + 1) * 16 ^ n) := hA
      _ ≤ 9 ^ n * (2 ^ n * 16 ^ n) := by gcongr
      _ = 288 ^ n := by rw [← mul_pow, ← mul_pow]; norm_num
      _ ≤ 2 * 288 ^ n := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 288) n]

/-- **Finite irrationality exponent of `π`.** -/
theorem exists_not_liouvilleWith_pi : ∃ K : ℝ, ∀ p > K, ¬ LiouvilleWith p Real.pi := by
  obtain ⟨K, hK⟩ := exists_not_liouvilleWith_pi_sq_div_six
  refine ⟨2 * K + 2, fun p hp hL => ?_⟩
  set r : ℝ := 2 * K + 2 with hr
  have hrp : r < p := hp
  have hrpos : 0 < r := by rw [hr]; positivity
  have hfreq := hL.frequently_lt_rpow_neg hrp
  refine hK (r / 2) (by rw [hr]; linarith) ⟨2 * 6 ^ (r / 2), ?_⟩
  rw [frequently_atTop] at hfreq ⊢
  intro A
  obtain ⟨n, hnA, m, hne, hlt⟩ := hfreq (A + 1)
  have hn1 : 1 ≤ n := by omega
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  refine ⟨6 * n ^ 2, by nlinarith, m ^ 2, ?_, ?_⟩
  · intro heq
    apply hne
    have hsmall : |Real.pi - m / n| < 1 := by
      refine hlt.trans_le ?_
      rw [Real.rpow_neg hnpos.le]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow hnr hrpos.le)
    have hu : (0 : ℝ) < m / n := by
      have := (abs_lt.mp hsmall).2
      linarith [Real.pi_gt_three]
    push_cast at heq
    have hsq : Real.pi ^ 2 = ((m : ℝ) / n) ^ 2 := by
      rw [div_pow]; field_simp at heq ⊢; linarith
    exact (pow_left_inj₀ Real.pi_pos.le hu.le two_ne_zero).mp hsq
  · push_cast
    have hsmall : |Real.pi - m / n| ≤ 1 := by
      refine hlt.le.trans ?_
      rw [Real.rpow_neg hnpos.le]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow hnr hrpos.le)
    have hdiff : Real.pi ^ 2 / 6 - (m : ℝ) ^ 2 / (6 * (n : ℝ) ^ 2) =
        (Real.pi - m / n) * (Real.pi + m / n) / 6 := by
      field_simp; ring
    have hsum : |Real.pi + m / n| ≤ 9 := by
      have := abs_le.mp hsmall
      rw [abs_le]
      constructor <;> nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hrpow : (n : ℝ) ^ (-r) = 6 ^ (r / 2) / (6 * (n : ℝ) ^ 2) ^ (r / 2) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_neg hnpos.le,
        ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      have : (6 : ℝ) ^ (r / 2) ≠ 0 := by positivity
      field_simp
      norm_num
    rw [hdiff, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    calc |Real.pi - m / n| * |Real.pi + m / n| / 6 ≤ |Real.pi - m / n| * 9 / 6 := by
          gcongr
      _ < (n : ℝ) ^ (-r) * 9 / 6 := by gcongr
      _ ≤ 2 * (n : ℝ) ^ (-r) := by
          have : 0 ≤ (n : ℝ) ^ (-r) := by positivity
          linarith
      _ = 2 * 6 ^ (r / 2) / (6 * (n : ℝ) ^ 2) ^ (r / 2) := by rw [hrpow]; ring

/-- **`π` is not a Liouville number.** -/
theorem not_liouville_pi : ¬ Liouville Real.pi := by
  obtain ⟨K, hK⟩ := exists_not_liouvilleWith_pi
  exact fun h => hK (K + 1) (by linarith) (h.liouvilleWith (K + 1))

end GaloisForLFunctions.HTGeometry.BeukersZetaTwo
