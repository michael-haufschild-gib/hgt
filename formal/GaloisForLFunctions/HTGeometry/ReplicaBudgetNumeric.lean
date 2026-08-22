import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The replica budget follows from a small spectral collision

`(43)` of the arithmetic hardness–recurrence card.  With `r ≤ (a₀²/128)(3/2)ⁿ` and a spectral
collision below `4(2/3)ⁿ`, the replica moment `r!(16C/a₀²)^r` is below `2^{-r}`; a target family of
size at most `2^{r/4}` then makes the whole budget `(22)` smaller than one.

## Main results

* `factorial_mul_pow_le` — `r!(16C/a₀²)^r ≤ 2^{-r}`.
* `replica_budget_of_small_collision` — **`(42)`–`(43)`.**
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- **`(43)`.**  A collision below `4(2/3)ⁿ` and a replica order below `(a₀²/128)(3/2)ⁿ` make the
replica moment at most `2^{-r}`. -/
theorem factorial_mul_pow_le {a₀ Cn : ℝ} (ha₀ : 0 < a₀) (hCnn : 0 ≤ Cn) {n r : ℕ}
    (hC : Cn < 4 * (2 / 3 : ℝ) ^ n)
    (hrle : (r : ℝ) ≤ (a₀ ^ 2 / 128) * (3 / 2 : ℝ) ^ n) :
    (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r ≤ (1 / 2 : ℝ) ^ r := by
  have ha2 : (0 : ℝ) < a₀ ^ 2 := by positivity
  have hXnn : (0 : ℝ) ≤ 16 * Cn / a₀ ^ 2 := by positivity
  have hprod : (3 / 2 : ℝ) ^ n * (2 / 3 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hkey : (r : ℝ) * (16 * Cn / a₀ ^ 2) ≤ 1 / 2 := by
    have h1 : 16 * Cn / a₀ ^ 2 ≤ 64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2 := by
      rw [div_le_div_iff_of_pos_right ha2]
      linarith
    have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h2 : (r : ℝ) * (16 * Cn / a₀ ^ 2) ≤ (r : ℝ) * (64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2) :=
      mul_le_mul_of_nonneg_left h1 hrnn
    have hqnn : (0 : ℝ) ≤ 64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2 := by positivity
    have h3 : (r : ℝ) * (64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2)
        ≤ ((a₀ ^ 2 / 128) * (3 / 2 : ℝ) ^ n) * (64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2) :=
      mul_le_mul_of_nonneg_right hrle hqnn
    have h4 : ((a₀ ^ 2 / 128) * (3 / 2 : ℝ) ^ n) * (64 * (2 / 3 : ℝ) ^ n / a₀ ^ 2) = 1 / 2 := by
      field_simp
      nlinarith [hprod]
    linarith
  have hfac : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by
    have := Nat.factorial_le_pow r
    exact_mod_cast this
  calc (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r
      ≤ ((r : ℝ) ^ r) * (16 * Cn / a₀ ^ 2) ^ r :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = ((r : ℝ) * (16 * Cn / a₀ ^ 2)) ^ r := by rw [mul_pow]
    _ ≤ (1 / 2 : ℝ) ^ r := by
        refine pow_le_pow_left₀ (by positivity) hkey r

/-- **`(42)`–`(43)`.**  A target family of size at most `2^{r/4}` satisfies the replica budget `(22)`
as soon as the spectral collision is below `4(2/3)ⁿ` and `r ≤ (a₀²/128)(3/2)ⁿ`. -/
theorem replica_budget_of_small_collision {a₀ Cn hcardC : ℝ} (ha₀ : 0 < a₀) (hCnn : 0 ≤ Cn)
    {n r : ℕ} (hr1 : 1 ≤ r) (hC : Cn < 4 * (2 / 3 : ℝ) ^ n)
    (hrle : (r : ℝ) ≤ (a₀ ^ 2 / 128) * (3 / 2 : ℝ) ^ n)
    (hcard0 : 0 ≤ hcardC) (hcardle : hcardC ^ 4 ≤ (2 : ℝ) ^ r) :
    hcardC * (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r < 1 := by
  have hmom := factorial_mul_pow_le ha₀ hCnn hC hrle
  have hAnn : (0 : ℝ) ≤ hcardC * (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r := by positivity
  have hAle : hcardC * (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r
      ≤ hcardC * (1 / 2 : ℝ) ^ r := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmom hcard0
  have hpow4 : (hcardC * (1 / 2 : ℝ) ^ r) ^ 4 ≤ (1 / 8 : ℝ) ^ r := by
    have hexp : (hcardC * (1 / 2 : ℝ) ^ r) ^ 4 = hcardC ^ 4 * ((1 / 2 : ℝ) ^ r) ^ 4 := by
      rw [mul_pow]
    have hswap : ((1 / 2 : ℝ) ^ r) ^ 4 = ((1 / 16 : ℝ)) ^ r := by
      rw [← pow_mul, mul_comm r 4, pow_mul]
      norm_num
    have hnn : (0 : ℝ) ≤ ((1 : ℝ) / 16) ^ r := by positivity
    calc (hcardC * (1 / 2 : ℝ) ^ r) ^ 4 = hcardC ^ 4 * ((1 / 16 : ℝ)) ^ r := by
          rw [hexp, hswap]
      _ ≤ (2 : ℝ) ^ r * ((1 / 16 : ℝ)) ^ r := mul_le_mul_of_nonneg_right hcardle hnn
      _ = (1 / 8 : ℝ) ^ r := by rw [← mul_pow]; norm_num
  have hsmall : ((1 : ℝ) / 8) ^ r ≤ 1 / 8 := by
    calc ((1 : ℝ) / 8) ^ r ≤ ((1 : ℝ) / 8) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hr1
      _ = 1 / 8 := by norm_num
  have hA4 : (hcardC * (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r) ^ 4 < 1 := by
    have h1 : (hcardC * (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r) ^ 4
        ≤ (hcardC * (1 / 2 : ℝ) ^ r) ^ 4 := by
      refine pow_le_pow_left₀ hAnn hAle 4
    linarith
  by_contra hcon
  push Not at hcon
  have : (1 : ℝ) ≤ (hcardC * (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r) ^ 4 := by
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ (hcardC * (r.factorial : ℝ) * (16 * Cn / a₀ ^ 2) ^ r) ^ 4 :=
          pow_le_pow_left₀ (by norm_num) hcon 4
  linarith

end GaloisForLFunctions.HTGeometry
