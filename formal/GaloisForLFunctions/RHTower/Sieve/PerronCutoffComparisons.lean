import Mathlib

/-!
# The two logarithmic comparisons at a Perron cutoff

Splitting the truncated Perron error at `1/2 ≤ x/n ≤ 2` needs exactly two pointwise facts: near the
cutoff the logarithm is comparable to the displacement, `|y − 1| ≤ 2|log y|`; far from it the
logarithm is bounded below by `log 2`.  The Lorentzian cell comparison
`1/(1+t²) ≤ 4/(1+h²)` is the analogous statement for the Cauchy weight on a unit cell.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- **The near-cutoff logarithmic comparison.**  On `[1/2, 2]` the logarithm is comparable to the
displacement from `1`. -/
theorem abs_sub_one_le_two_mul_abs_log {y : ℝ} (hy1 : 1 / 2 ≤ y) (hy2 : y ≤ 2) :
    |y - 1| ≤ 2 * |Real.log y| := by
  have hy0 : (0 : ℝ) < y := by linarith
  rcases le_or_gt 1 y with h | h
  · have hlog : (1 : ℝ) - 1 / y ≤ Real.log y := by
      have hinv : Real.log (1 / y) ≤ 1 / y - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div one_ne_zero (ne_of_gt hy0), Real.log_one] at hinv
      linarith
    have hlog0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hlog0]
    have hkey : (1 : ℝ) - 1 / y = (y - 1) / y := by field_simp
    rw [hkey] at hlog
    have hdiv : (y - 1) / 2 ≤ (y - 1) / y := by
      rw [div_le_div_iff₀ (by norm_num) hy0]
      nlinarith
    linarith
  · have hlog : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
    have hlog0 : Real.log y ≤ 0 := Real.log_nonpos hy0.le h.le
    rw [abs_of_nonpos (by linarith), abs_of_nonpos hlog0]
    linarith

/-- **The far-cutoff logarithmic bound.** -/
theorem log_two_le_abs_log {y : ℝ} (hy0 : 0 < y) (h : y ≤ 1 / 2 ∨ 2 ≤ y) :
    Real.log 2 ≤ |Real.log y| := by
  rcases h with h | h
  · have hlog : Real.log y ≤ Real.log (1 / 2) := Real.log_le_log hy0 h
    have hval : Real.log (1 / 2) = -Real.log 2 := by
      rw [Real.log_div one_ne_zero (by norm_num), Real.log_one]
      ring
    rw [hval] at hlog
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hlog : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) h
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [abs_of_nonneg (by linarith)]
    exact hlog

/-- **The Lorentzian cell comparison.**  On a unit cell centred at `h` the Cauchy weight is
comparable to its value at the centre. -/
theorem inv_one_add_sq_le_cell {t h : ℝ} (hth : |t - h| ≤ 1 / 2) :
    1 / (1 + t ^ (2 : ℕ)) ≤ 4 / (1 + h ^ (2 : ℕ)) := by
  have habs : |h| ≤ |t| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub h t
    have h2 : |h - t| = |t - h| := abs_sub_comm h t
    linarith [h2 ▸ this]
  have ht : |t| ≤ (t ^ (2 : ℕ) + 1) / 2 := by
    nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  have hh : h ^ (2 : ℕ) ≤ (|t| + 1 / 2) ^ (2 : ℕ) := by
    have habs0 : (0 : ℝ) ≤ |h| := abs_nonneg h
    nlinarith [sq_abs h, habs, habs0]
  have hkey : 1 + h ^ (2 : ℕ) ≤ 4 * (1 + t ^ (2 : ℕ)) := by
    nlinarith [hh, ht, sq_abs t, abs_nonneg t]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

end

end RHTower.Sieve
