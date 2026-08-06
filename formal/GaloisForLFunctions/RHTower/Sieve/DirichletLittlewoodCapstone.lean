import GaloisForLFunctions.RHTower.Sieve.DirichletFactorialHypothesis

/-!
# The capstone of the structural chain

Every hypothesis of the estimate is now a consequence of two conditions on `t` and the order `K`:
`16π ≤ t`, and

```text
(K-1)(K - 4/3) log (K-1) + K log 2  <  log (t / 2π).
```

The second implies `2π·2^K < t`, so it subsumes the positivity of the split exponent as well as the
factorial bound.  What is left of the Littlewood programme at this point is the choice of `K` as a
function of `t`, and reading the resulting size of the right-hand side.
-/

namespace RHTower.Sieve

open Finset

/-- The largeness condition forces `t` past `2π · 2^K`. -/
theorem two_pow_lt_of_factorial_cond {t : ℝ} {K : ℕ} (hK : 2 ≤ K) (ht : 0 < t)
    (hcond : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
      + (K : ℝ) * Real.log 2 < Real.log (t / (2 * Real.pi))) :
    2 * Real.pi * (2 : ℝ) ^ (K : ℕ) < t := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ (K : ℝ) - 1 := by linarith
  have hnn : 0 ≤ ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1) := by
    have hlog : 0 ≤ Real.log ((K : ℝ) - 1) := Real.log_nonneg hK1
    have h1 : (0 : ℝ) ≤ (K : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) ≤ (K : ℝ) - 4 / 3 := by linarith
    positivity
  have hKlog : (K : ℝ) * Real.log 2 < Real.log (t / (2 * Real.pi)) := by linarith
  have hlt : Real.log ((2 : ℝ) ^ (K : ℕ)) < Real.log (t / (2 * Real.pi)) := by
    rw [Real.log_pow]
    exact_mod_cast hKlog
  have hquot : (2 : ℝ) ^ (K : ℕ) < t / (2 * Real.pi) :=
    (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlt
  rw [lt_div_iff₀ h2π] at hquot
  linarith

/-- **Capstone.**  Two explicit conditions on `t` and `K` give the estimate outright. -/
theorem norm_dirichlet_partial_littlewood_capstone {t : ℝ} (ht16 : 16 * Real.pi ≤ t) {K : ℕ}
    (hK : 2 ≤ K)
    (hcond : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
      + (K : ℝ) * Real.log 2 < Real.log (t / (2 * Real.pi))) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
            / (((K : ℝ) - 4 / 3) * Real.log 2) + 1) * Real.log 2
        + 3 * Real.log (t / (8 * Real.pi)) / Real.log 2
            * targetEps (splitExponent t K) K := by
  have hπ := Real.pi_pos
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  have hlt := two_pow_lt_of_factorial_cond hK ht hcond
  have hσ1 : 1 ≤ splitExponent t K := one_le_splitExponent hK hlt
  have hSR : splitExponent t K - 1 < topExponent t :=
    splitExponent_sub_one_lt_topExponent hK ht16 hlt.le hσ1
  have hfac : Nat.factorial (K - 1) ≤ 2 ^ (splitExponent t K) :=
    factorial_le_two_pow_splitExponent hK hcond.le
  exact norm_dirichlet_partial_littlewood_canonical (by linarith) hK hlt.le hσ1 hSR hfac

end RHTower.Sieve
