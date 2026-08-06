import GaloisForLFunctions.RHTower.Sieve.DirichletLittlewoodCapstone

/-!
# The right-hand side in closed form

Writing `L = log (t / 2π)`, the head of the capstone bound is at most `L/(K - 4/3) + log 2`, and the
canonical target is at most `2560 · exp (- (L - K log 2) / (3 · 2^K · (K - 4/3)))`, since the split
exponent is at least the balance point.  Substituting both leaves a bound in `t` and `K` with no
auxiliary definitions:

```text
1 + log 2 + L/(K - 4/3) + (3 (L - 2 log 2)/log 2) · 2560 · exp (- (L - K log 2)/(3·2^K·(K - 4/3))).
```

The first term is decreasing in `K` and the second increasing, and their balance is what fixes
`K ≈ log₂ log t`.
-/

namespace RHTower.Sieve

open Finset

/-- The canonical target at the chosen split exponent, bounded in `t` and `K` alone. -/
theorem targetEps_splitExponent_le {t : ℝ} {K : ℕ} (hK : 2 ≤ K) :
    targetEps (splitExponent t K) K
      ≤ 2560 * Real.exp (-((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
          / (3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3)))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hden : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
  have hpow : (0 : ℝ) < 3 * (2 : ℝ) ^ K := by positivity
  have hceil : (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
      / (((K : ℝ) - 4 / 3) * Real.log 2) ≤ ((splitExponent t K : ℕ) : ℝ) := Nat.le_ceil _
  have hkey : (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
        / (3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3))
      ≤ ((splitExponent t K : ℕ) : ℝ) * Real.log 2 / (3 * (2 : ℝ) ^ K) := by
    have hstep := mul_le_mul_of_nonneg_right hceil (by positivity : (0 : ℝ) ≤ Real.log 2)
    have heq : (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
        / (((K : ℝ) - 4 / 3) * Real.log 2) * Real.log 2
        = (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2) / ((K : ℝ) - 4 / 3) := by
      have h1 : Real.log 2 ≠ 0 := hlog2.ne'
      have h2 : ((K : ℝ) - 4 / 3) ≠ 0 := hden.ne'
      field_simp
    rw [heq] at hstep
    rw [div_le_div_iff₀ (by positivity) hpow]
    have hexpand : (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2) / ((K : ℝ) - 4 / 3)
        * (3 * (2 : ℝ) ^ K)
        ≤ ((splitExponent t K : ℕ) : ℝ) * Real.log 2 * (3 * (2 : ℝ) ^ K) :=
      mul_le_mul_of_nonneg_right hstep hpow.le
    have h3 : ((K : ℝ) - 4 / 3) ≠ 0 := hden.ne'
    have h4 : ((K : ℝ) * 3 - 4) ≠ 0 := ne_of_gt (by linarith)
    calc (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2) * (3 * (2 : ℝ) ^ K)
        = ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2) / ((K : ℝ) - 4 / 3)
            * (3 * (2 : ℝ) ^ K)) * ((K : ℝ) - 4 / 3) := by
          field_simp
      _ ≤ (((splitExponent t K : ℕ) : ℝ) * Real.log 2 * (3 * (2 : ℝ) ^ K)) * ((K : ℝ) - 4 / 3) :=
          mul_le_mul_of_nonneg_right hexpand hden.le
      _ = ((splitExponent t K : ℕ) : ℝ) * Real.log 2 * (3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3)) := by
          ring
  rw [targetEps]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  have hsplit : ((splitExponent t K : ℕ) : ℝ) * Real.log 2 / (3 * (2 : ℝ) ^ K)
      = ((splitExponent t K : ℕ) : ℝ) * Real.log 2 / (3 * (2 : ℝ) ^ K) := rfl
  linarith [hkey]

/-- **Closed-form bound.**  No auxiliary definition survives on the right. -/
theorem norm_dirichlet_partial_littlewood_explicit {t : ℝ} (ht16 : 16 * Real.pi ≤ t) {K : ℕ}
    (hK : 2 ≤ K)
    (hcond : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
      + (K : ℝ) * Real.log 2 < Real.log (t / (2 * Real.pi))) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + Real.log 2 + Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3)
        + 3 * Real.log (t / (8 * Real.pi)) / Real.log 2
          * (2560 * Real.exp (-((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
              / (3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3))))) := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hden : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
  have hlt := two_pow_lt_of_factorial_cond hK ht hcond
  have hcap := norm_dirichlet_partial_littlewood_capstone ht16 hK hcond
  refine le_trans hcap ?_
  -- head
  have hhead : ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
        / (((K : ℝ) - 4 / 3) * Real.log 2) + 1) * Real.log 2
      ≤ Real.log 2 + Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3) := by
    have heq : (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
        / (((K : ℝ) - 4 / 3) * Real.log 2) * Real.log 2
        = (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2) / ((K : ℝ) - 4 / 3) := by
      have h1 : Real.log 2 ≠ 0 := hlog2.ne'
      have h2 : ((K : ℝ) - 4 / 3) ≠ 0 := hden.ne'
      field_simp
    have hmono : (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2) / ((K : ℝ) - 4 / 3)
        ≤ Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3) := by
      refine div_le_div_of_nonneg_right ?_ hden.le
      nlinarith [hlog2, hKR]
    rw [add_mul, one_mul, heq]
    linarith
  -- tail
  have hlogtail : 0 ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 := by
    have h8π : (0 : ℝ) < 8 * Real.pi := by positivity
    have hone : (1 : ℝ) ≤ t / (8 * Real.pi) := by
      rw [le_div_iff₀ h8π]
      linarith
    have := Real.log_nonneg hone
    positivity
  have htail := mul_le_mul_of_nonneg_left (targetEps_splitExponent_le (t := t) hK) hlogtail
  linarith

end RHTower.Sieve
