import GaloisForLFunctions.RHTower.Sieve.ZetaLineLittleOh
import GaloisForLFunctions.RHTower.Sieve.DirichletOrderRate

/-!
# `ζ` on the line `Re s = 1`, with the rate

The truncation of `ζ(1 + it)` has a head, which the derivative-test chain bounds, and two tail terms
`1/t` and `‖1 + it‖ / M`.  Feeding the rate rather than the accuracy-indexed estimate into the head
gives Littlewood's bound for `ζ` itself.

The two tail terms are bounded by an absolute constant — the truncation point exceeds `(t/8π)³ - 1`,
so the second is `O(1/t²)` — which turns the estimate into

```text
‖ζ(1 + it)‖  ≤  32 + 2 log(t/2π) / (orderLowerBound (log (t/2π)) - 4/3),
```

a clean `O(log t / log log t)`.
-/

namespace RHTower.Sieve

open Finset

/-- **`ζ(1 + it)` at Littlewood's rate.** -/
theorem norm_riemannZeta_line_rate {t : ℝ} (ht16 : 16 * Real.pi ≤ t)
    (ht2 : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi)))
    (hd : 4 / 3 < orderLowerBound (Real.log (t / (2 * Real.pi)))) :
    ‖riemannZeta (1 + Complex.I * (t : ℂ))‖
      ≤ 1 + Real.log 2
        + 2 * Real.log (t / (2 * Real.pi))
            / (orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3)
        + 1 / t + (1 + t) / ((t / (8 * Real.pi)) ^ (3 : ℕ) - 1) := by
  have hπ := Real.pi_pos
  have ht8 : 8 * Real.pi ≤ t := by linarith
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  have hM1 : 1 ≤ lineTruncation t := one_le_lineTruncation t
  have htrunc := norm_riemannZeta_one_add_I_mul_le ht hM1
  have hhead : ∑ k ∈ Finset.Icc 1 (lineTruncation t),
        ((k : ℝ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))
      = ∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
          (n : ℂ) ^ (-1 - Complex.I * (t : ℂ)) := by
    rw [sum_Icc_cpow_eq_sum_Ico t (lineTruncation t), lineTruncation_add_one t]
  rw [hhead] at htrunc
  refine le_trans htrunc ?_
  have hrate := norm_dirichlet_partial_littlewood_rate ht16 ht2 hd
  have hcube : (1 : ℝ) < (t / (8 * Real.pi)) ^ (3 : ℕ) := by
    have h2 : (2 : ℝ) ≤ t / (8 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    calc (1 : ℝ) < 2 ^ (3 : ℕ) := by norm_num
      _ ≤ (t / (8 * Real.pi)) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) h2 3
  have hden : (0 : ℝ) < (t / (8 * Real.pi)) ^ (3 : ℕ) - 1 := by linarith
  have hMpos : (0 : ℝ) < ((lineTruncation t : ℕ) : ℝ) :=
    lt_of_lt_of_le hden (cube_sub_one_le_lineTruncation ht8)
  have hnorm : ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ ≤ 1 + t := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
  have htail : ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ / ((lineTruncation t : ℕ) : ℝ)
      ≤ (1 + t) / ((t / (8 * Real.pi)) ^ (3 : ℕ) - 1) := by
    have hA : ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ / ((lineTruncation t : ℕ) : ℝ)
        ≤ (1 + t) / ((lineTruncation t : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hnorm hMpos.le
    have hB : (1 + t) / ((lineTruncation t : ℕ) : ℝ)
        ≤ (1 + t) / ((t / (8 * Real.pi)) ^ (3 : ℕ) - 1) :=
      div_le_div_of_nonneg_left (by linarith) hden (cube_sub_one_le_lineTruncation ht8)
    linarith
  linarith [hrate, htail]

/-- The two tail terms of the truncation are bounded by an absolute constant. -/
theorem zeta_line_tail_le {t : ℝ} (ht16 : 16 * Real.pi ≤ t) :
    1 / t + (1 + t) / ((t / (8 * Real.pi)) ^ (3 : ℕ) - 1) ≤ 30 := by
  have hπ := Real.pi_pos
  have hπlt : Real.pi < 3.15 := Real.pi_lt_d2
  have hπgt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have ht50 : (50 : ℝ) ≤ t := by linarith
  have hsq : (2500 : ℝ) ≤ t ^ 2 := by nlinarith
  have htpos : (0 : ℝ) < t := by linarith
  have h8ne : (8 : ℝ) * Real.pi ≠ 0 := by positivity
  have hπ2 : Real.pi ^ 2 < 10 := by nlinarith
  have hπ3 : Real.pi ^ 3 < 32 := by
    have h : Real.pi ^ 3 = Real.pi * Real.pi ^ 2 := by ring
    rw [h]
    calc Real.pi * Real.pi ^ 2 < 3.15 * 10 :=
          mul_lt_mul' hπlt.le hπ2 (by positivity) (by norm_num)
      _ < 32 := by norm_num
  have hcube : (t / (8 * Real.pi)) ^ (3 : ℕ) = t ^ 3 / (512 * Real.pi ^ 3) := by
    field_simp
    ring
  have ht3 : (0 : ℝ) < t ^ 3 := by positivity
  have hden0 : t ^ 3 / 16384 ≤ (t / (8 * Real.pi)) ^ (3 : ℕ) := by
    rw [hcube, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have ht2500 : (2500 : ℝ) * t ≤ t ^ 3 := by nlinarith [hsq, htpos]
  have ht32768 : (32768 : ℝ) ≤ t ^ 3 := by nlinarith [ht2500, ht50]
  have hden1 : t ^ 3 / 32768 ≤ (t / (8 * Real.pi)) ^ (3 : ℕ) - 1 := by
    have : (1 : ℝ) ≤ t ^ 3 / 32768 := by linarith [ht32768]
    nlinarith [hden0]
  have hdenpos : (0 : ℝ) < t ^ 3 / 32768 := by positivity
  have hratio : (1 + t) / ((t / (8 * Real.pi)) ^ (3 : ℕ) - 1) ≤ (1 + t) / (t ^ 3 / 32768) :=
    div_le_div_of_nonneg_left (by linarith) hdenpos hden1
  have hfin : (1 + t) / (t ^ 3 / 32768) ≤ 27 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith
  have h1t : 1 / t ≤ 1 := by
    rw [div_le_one htpos]
    linarith
  linarith

/-- **Littlewood's bound for `ζ` on the line, in closed form.** -/
theorem norm_riemannZeta_line_rate_clean {t : ℝ} (ht16 : 16 * Real.pi ≤ t)
    (ht2 : orderThreshold 2 ≤ Real.log (t / (2 * Real.pi)))
    (hd : 4 / 3 < orderLowerBound (Real.log (t / (2 * Real.pi)))) :
    ‖riemannZeta (1 + Complex.I * (t : ℂ))‖
      ≤ 32 + 2 * Real.log (t / (2 * Real.pi))
          / (orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3) := by
  have hmain := norm_riemannZeta_line_rate ht16 ht2 hd
  have htail := zeta_line_tail_le ht16
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  linarith

end RHTower.Sieve
