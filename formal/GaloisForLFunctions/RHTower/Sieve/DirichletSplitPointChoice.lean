import GaloisForLFunctions.RHTower.Sieve.DirichletExponentConsistency

/-!
# Choosing the split point

The upper bound on `t` in the exponent form reads `t ≤ 2π · 2^(σ(K - 4/3) + K)` with `σ = S + 1`,
so the least admissible `σ` is the ceiling of

```text
x = (log (t / 2π) - K log 2) / ((K - 4/3) log 2).
```

Taking that ceiling gives both directions at once: the upper bound holds, and `σ` exceeds `x` by
less than one, so the harmonic head `σ log 2` is at most `(log(t/2π) - K log 2)/(K - 4/3) + log 2`.
For `K` of size `m` that is `log t / m` up to bounded terms, which is where the `log log` saving in
the final estimate comes from.
-/

namespace RHTower.Sieve

open Finset

/-- The least admissible split exponent: the ceiling of the balance point. -/
noncomputable def splitExponent (t : ℝ) (K : ℕ) : ℕ :=
  ⌈(Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
    / (((K : ℝ) - 4 / 3) * Real.log 2)⌉₊

/-- **The chosen split exponent satisfies the upper bound on `t`.** -/
theorem le_two_pow_splitExponent {t : ℝ} (ht : 0 < t) {K : ℕ} (hK : 2 ≤ K) :
    t ≤ 2 * Real.pi
      * (2 : ℝ) ^ (((splitExponent t K : ℕ) : ℝ) * ((K : ℝ) - 4 / 3) + (K : ℝ)) := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
  have hden : (0 : ℝ) < ((K : ℝ) - 4 / 3) * Real.log 2 := by positivity
  set x : ℝ := (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
    / (((K : ℝ) - 4 / 3) * Real.log 2) with hxdef
  have hceil : x ≤ ((splitExponent t K : ℕ) : ℝ) := Nat.le_ceil x
  have hkey : Real.log (t / (2 * Real.pi))
      ≤ (((splitExponent t K : ℕ) : ℝ) * ((K : ℝ) - 4 / 3) + (K : ℝ)) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hceil hden.le
    rw [hxdef, div_mul_cancel₀ _ hden.ne'] at this
    nlinarith [this]
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hrpow : (2 : ℝ) ^ (((splitExponent t K : ℕ) : ℝ) * ((K : ℝ) - 4 / 3) + (K : ℝ))
      = Real.exp ((((splitExponent t K : ℕ) : ℝ) * ((K : ℝ) - 4 / 3) + (K : ℝ)) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  rw [hrpow]
  have hexp : t / (2 * Real.pi)
      ≤ Real.exp ((((splitExponent t K : ℕ) : ℝ) * ((K : ℝ) - 4 / 3) + (K : ℝ)) * Real.log 2) := by
    have hle := Real.exp_le_exp.mpr hkey
    rwa [Real.exp_log (by positivity)] at hle
  rw [div_le_iff₀ hpos] at hexp
  linarith [hexp]

/-- The balance point is nonnegative once `t` clears `2π · 2^K`. -/
theorem splitExponent_arg_nonneg {t : ℝ} {K : ℕ} (hK : 2 ≤ K)
    (hbig : 2 * Real.pi * (2 : ℝ) ^ (K : ℕ) ≤ t) :
    0 ≤ (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
      / (((K : ℝ) - 4 / 3) * Real.log 2) := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hden : (0 : ℝ) < ((K : ℝ) - 4 / 3) * Real.log 2 := by
    have : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
    positivity
  refine div_nonneg ?_ hden.le
  have hquot : (2 : ℝ) ^ (K : ℕ) ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hbig]
  have hpow : Real.log ((2 : ℝ) ^ (K : ℕ)) = (K : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hmono : Real.log ((2 : ℝ) ^ (K : ℕ)) ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_le_log (by positivity) hquot
  rw [hpow] at hmono
  linarith

/-- **The chosen split exponent is not much larger than the balance point.** -/
theorem splitExponent_le {t : ℝ} {K : ℕ}
    (hx : 0 ≤ (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
      / (((K : ℝ) - 4 / 3) * Real.log 2)) :
    ((splitExponent t K : ℕ) : ℝ)
      ≤ (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
          / (((K : ℝ) - 4 / 3) * Real.log 2) + 1 :=
  (Nat.ceil_lt_add_one hx).le

end RHTower.Sieve
