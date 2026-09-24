import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic spacing of positive integers

The mean-value theory of Dirichlet polynomials estimates the off-diagonal through the logarithmic
separations `log m − log n`.  Two-sided linear comparison,

```text
(m − n)/m  ≤  log m − log n  ≤  (m − n)/n ,
```

turns the linear separation of distinct integers into the logarithmic spacing

```text
δ_n  =  min_{m ≠ n} |log m − log n|  ≥  1/max(m,n) ,
```

which is the `δ_n ≍ 1/n` input of Montgomery–Vaughan and of any affine-error mean value theorem.
-/

namespace HTGeometry

/-- Two-sided linear comparison for a logarithmic difference. -/
theorem sub_div_le_log_sub_log {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    (m - n) / m ≤ Real.log m - Real.log n := by
  have hdiv : (0 : ℝ) < n / m := div_pos hn hm
  have h := Real.log_le_sub_one_of_pos hdiv
  rw [Real.log_div hn.ne' hm.ne'] at h
  have hnm : n / m - 1 = -((m - n) / m) := by field_simp; ring
  rw [hnm] at h
  linarith

theorem log_sub_log_le_sub_div {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    Real.log m - Real.log n ≤ (m - n) / n := by
  have hdiv : (0 : ℝ) < m / n := div_pos hm hn
  have h := Real.log_le_sub_one_of_pos hdiv
  rw [Real.log_div hm.ne' hn.ne'] at h
  have hmn : m / n - 1 = (m - n) / n := by field_simp
  rw [hmn] at h
  linarith

/-- **The logarithmic spacing bound.**  For positive reals the logarithmic separation is at least
the linear separation divided by the larger argument.  This is the elementary input that converts
the integer spacing `|m − n| ≥ 1` into the logarithmic spacing `δ_n ≍ 1/n` used by every
mean-value estimate for Dirichlet polynomials. -/
theorem abs_sub_div_max_le_abs_log_sub_log {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    |m - n| / max m n ≤ |Real.log m - Real.log n| := by
  rcases le_total n m with h | h
  · have hmax : max m n = m := max_eq_left h
    rw [hmax, abs_of_nonneg (by linarith : (0:ℝ) ≤ m - n),
      abs_of_nonneg (by
        have := Real.log_le_log hn h
        linarith)]
    exact sub_div_le_log_sub_log hm hn
  · have hmax : max m n = n := max_eq_right h
    rw [hmax, abs_of_nonpos (by linarith : m - n ≤ 0),
      abs_of_nonpos (by
        have := Real.log_le_log hm h
        linarith)]
    have hkey := sub_div_le_log_sub_log hn hm
    have hrw : -(m - n) / n = (n - m) / n := by ring
    rw [hrw]
    linarith

/-- **The logarithmic spacing of distinct positive integers.**  Distinct positive integers are
separated by at least `1` linearly, hence by at least `1/max(m,n)` logarithmically.  This is the
`δ_n ≍ 1/n` input of Montgomery–Vaughan. -/
theorem inv_max_le_abs_log_sub_log_nat {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    (1 : ℝ) / max (m : ℝ) (n : ℝ) ≤ |Real.log m - Real.log n| := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
    rcases lt_or_gt_of_ne (show (m : ℤ) ≠ (n : ℤ) by exact_mod_cast hmn) with h | h
    · have : ((m : ℤ) : ℝ) + 1 ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at this ⊢
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have : ((n : ℤ) : ℝ) + 1 ≤ ((m : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at this ⊢
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hmax : (0 : ℝ) < max (m : ℝ) (n : ℝ) := lt_max_of_lt_left hmR
  refine le_trans ?_ (abs_sub_div_max_le_abs_log_sub_log hmR hnR)
  exact div_le_div_of_nonneg_right hone hmax.le

/-- Uniform form: distinct positive integers below `N` are logarithmically `1/N` apart. -/
theorem inv_le_abs_log_sub_log_nat_of_le {m n N : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (hmN : m ≤ N) (hnN : n ≤ N) :
    (1 : ℝ) / (N : ℝ) ≤ |Real.log m - Real.log n| := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmaxN : max (m : ℝ) (n : ℝ) ≤ (N : ℝ) := by
    refine max_le ?_ ?_ <;> exact_mod_cast ‹_›
  have hmax : (0 : ℝ) < max (m : ℝ) (n : ℝ) := lt_max_of_lt_left hmR
  refine le_trans ?_ (inv_max_le_abs_log_sub_log_nat hm hn hmn)
  exact one_div_le_one_div_of_le hmax hmaxN

end HTGeometry
