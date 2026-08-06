import GaloisForLFunctions.RHTower.Sieve.DirichletTopExponentChoice

/-!
# The assembled bound

With both exponents chosen from `t` — the split point as the ceiling of the balance point, the top
of the range as the floor of `3 log(t/8π)/log 2` — the estimate becomes a bound in `t`, the order
`K` and the target `ε` alone:

```text
‖∑_{n < 2^(R+1)} n^(-1-it)‖
  ≤ 1 + [ (log(t/2π) - K log 2)/(K - 4/3) + log 2 ] + [ 3 log(t/8π)/log 2 ] · ε.
```

Both bracketed terms are `O(log t / K)` when `ε` is of size `1/K`, which is the shape the depth
criterion permits.
-/

namespace RHTower.Sieve

open Finset

/-- **Assembled bound.**  Both exponents are the canonical choices, so only `K` and `ε` remain
free. -/
theorem norm_dirichlet_partial_littlewood_assembled {t : ℝ} (ht8 : 8 * Real.pi ≤ t) {K : ℕ}
    (hK : 2 ≤ K) (hbig : 2 * Real.pi * (2 : ℝ) ^ (K : ℕ) ≤ t)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 2560)
    (hσ1 : 1 ≤ splitExponent t K)
    (hSR : splitExponent t K - 1 < topExponent t)
    (hfac : Nat.factorial (K - 1) ≤ 2 ^ (splitExponent t K))
    (hdeep : 3 * (2 : ℝ) ^ K * Real.log (2560 / ε)
      ≤ ((splitExponent t K : ℕ) : ℝ) * Real.log 2) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
            / (((K : ℝ) - 4 / 3) * Real.log 2) + 1) * Real.log 2
        + 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 * ε := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht8
  set σ : ℕ := splitExponent t K with hσdef
  set R : ℕ := topExponent t with hRdef
  have hScast : ((σ - 1 : ℕ) : ℝ) + 1 = (σ : ℝ) := by
    have : ((σ - 1 : ℕ) : ℝ) = (σ : ℝ) - 1 := by
      have : (1 : ℕ) ≤ σ := hσ1
      push_cast [Nat.cast_sub this]
      ring
    rw [this]; ring
  -- the upper bound on `t`, in the form the exponent shape wants
  have hhigh : t ≤ 2 * Real.pi
      * (2 : ℝ) ^ ((((σ - 1 : ℕ) : ℝ) + 1) * ((K : ℝ) - 1) - (((σ - 1 : ℕ) : ℝ) + 1) / 3)
        * (2 : ℝ) ^ K := by
    have hform : 2 * Real.pi
        * (2 : ℝ) ^ ((((σ - 1 : ℕ) : ℝ) + 1) * ((K : ℝ) - 1) - (((σ - 1 : ℕ) : ℝ) + 1) / 3)
          * (2 : ℝ) ^ K
        = 2 * Real.pi * (2 : ℝ) ^ ((σ : ℝ) * ((K : ℝ) - 4 / 3) + (K : ℝ)) := by
      rw [hScast, ← Real.rpow_natCast (2 : ℝ) K, mul_assoc (2 * Real.pi),
        ← Real.rpow_add (by norm_num)]
      congr 2
      ring
    rw [hform]
    exact le_two_pow_splitExponent ht hK
  have hmain := norm_dirichlet_partial_littlewood_exponent (t := t) ht (S := σ - 1) (R := R)
    (K := K) hSR hε hε' hK (by rwa [Nat.sub_add_cancel hσ1]) (topExponent_bound ht8) hhigh
    (by rw [hScast]; exact hdeep)
  refine le_trans hmain ?_
  have hxnn := splitExponent_arg_nonneg hK hbig
  have hσle : (σ : ℝ)
      ≤ (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
          / (((K : ℝ) - 4 / 3) * Real.log 2) + 1 := splitExponent_le hxnn
  have hRle : (R : ℝ) ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 := topExponent_le ht8
  have hRS : ((R - (σ - 1) : ℕ) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast Nat.sub_le R (σ - 1)
  have hhead : (((σ - 1 : ℕ) : ℝ) + 1) * Real.log 2
      ≤ ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
          / (((K : ℝ) - 4 / 3) * Real.log 2) + 1) * Real.log 2 := by
    rw [hScast]
    exact mul_le_mul_of_nonneg_right hσle hlog2.le
  have htail : ((R - (σ - 1) : ℕ) : ℝ) * ε
      ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 * ε :=
    mul_le_mul_of_nonneg_right (le_trans hRS hRle) hε.le
  linarith

end RHTower.Sieve
