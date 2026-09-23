import GaloisForLFunctions.RHTower.Sieve.DirichletStructuralHypotheses

/-!
# The factorial hypothesis

The last structural hypothesis of the assembled bound is `(K-1)! ≤ 2^σ`.  Since `σ` is at least the
balance point and `(K-1)! ≤ (K-1)^(K-1)`, it is enough that

```text
(K-1)(K - 4/3) log (K-1) + K log 2  ≤  log (t / 2π),
```

an explicit largeness condition on `t` in terms of `K` alone.  In the intended regime
`K ≈ log₂ log t` the left side is `(log log t)^(2 : ℕ) · log log log t`, far below `log t`.
-/

namespace RHTower.Sieve

open Finset

/-- **The factorial hypothesis from an explicit largeness condition.** -/
theorem factorial_le_two_pow_splitExponent {t : ℝ} {K : ℕ} (hK : 2 ≤ K)
    (hcond : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
      + (K : ℝ) * Real.log 2 ≤ Real.log (t / (2 * Real.pi))) :
    Nat.factorial (K - 1) ≤ 2 ^ (splitExponent t K) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ (K : ℝ) - 1 := by linarith
  have hK1pos : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
  have hcast : (((K - 1 : ℕ)) : ℝ) = (K : ℝ) - 1 := by
    have h1 : 1 ≤ K := by omega
    push_cast [Nat.cast_sub h1]
    ring
  -- `(K-1)! ≤ (K-1)^(K-1)` in the reals
  have hfacnat : Nat.factorial (K - 1) ≤ (K - 1) ^ (K - 1) := Nat.factorial_le_pow (K - 1)
  have hfacR : ((Nat.factorial (K - 1) : ℕ) : ℝ) ≤ ((K : ℝ) - 1) ^ (K - 1) := by
    have := (Nat.cast_le (α := ℝ)).mpr hfacnat
    rwa [Nat.cast_pow, hcast] at this
  -- rewrite the power as an exponential
  have hpowexp : ((K : ℝ) - 1) ^ (K - 1) = Real.exp ((((K - 1 : ℕ)) : ℝ) * Real.log ((K : ℝ) - 1)) := by
    rw [← Real.rpow_natCast ((K : ℝ) - 1) (K - 1), Real.rpow_def_of_pos hK1pos]
    ring_nf
  -- the balance point dominates `(K-1) log (K-1)`
  have hx : (((K : ℝ) - 1)) * Real.log ((K : ℝ) - 1)
      ≤ (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
          / (((K : ℝ) - 4 / 3) * Real.log 2) * Real.log 2 := by
    have h1 : Real.log 2 ≠ 0 := hlog2.ne'
    have h2 : ((K : ℝ) - 4 / 3) ≠ 0 := hden.ne'
    have heq : (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
        / (((K : ℝ) - 4 / 3) * Real.log 2) * Real.log 2
        = (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2) / ((K : ℝ) - 4 / 3) := by
      field_simp
    rw [heq, le_div_iff₀ hden]
    nlinarith [hcond]
  have hceil : (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
      / (((K : ℝ) - 4 / 3) * Real.log 2) ≤ ((splitExponent t K : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hmain : ((Nat.factorial (K - 1) : ℕ) : ℝ) ≤ ((2 ^ (splitExponent t K) : ℕ) : ℝ) := by
    have htwo : ((2 ^ (splitExponent t K) : ℕ) : ℝ)
        = Real.exp (((splitExponent t K : ℕ) : ℝ) * Real.log 2) := by
      push_cast
      rw [← Real.rpow_natCast (2 : ℝ) (splitExponent t K), Real.rpow_def_of_pos (by norm_num)]
      ring_nf
    rw [htwo]
    refine le_trans (hfacR.trans (le_of_eq hpowexp)) ?_
    refine Real.exp_le_exp.mpr ?_
    rw [hcast]
    have := mul_le_mul_of_nonneg_right hceil hlog2.le
    linarith [hx, this]
  exact_mod_cast hmain

end RHTower.Sieve
