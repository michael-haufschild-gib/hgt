import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum

/-!
# The prime cosine sum from above

The passage between the prime series at `σ = 1 + 1/log z` and the finite cosine sum over `p ≤ z` costs
two absolute constants — the truncation `∑_{p > z} p^{-σ}` and the abscissa shift — and both are
two-sided.  The lower-bound direction is what the damped Euler estimate consumes; the upper-bound
direction is what a *lower* bound for the distance between two characters needs, since

`D(n^{it}, n^{iu}; z)² = ∑_{p ≤ z} 1/p − ∑_{p ≤ z} cos((t−u) log p)/p`.

So an upper bound for the cosine sum, obtained from an upper bound for `|ζ|` on the line, turns Mertens'
second theorem into a lower bound for the character distance — the ingredient that makes the close
frequency unique over a whole range rather than only inside one window.
-/

namespace RHTower.Sieve

open Complex

/-- **The passage from the prime series to the finite cosine sum, from above.**  Mirror of
`sum_cos_div_prime_ge_of_le`: whatever upper bound the Euler comparison supplies for the series at
`σ = 1 + 1/log z`, the finite sum inherits it up to the truncation and the abscissa shift. -/
theorem sum_cos_div_prime_le_of_ge {z : ℕ} {t L : ℝ} (hz : 3 ≤ z)
    (hL : (∑' p : Nat.Primes,
        (((p : ℕ) : ℂ) ^ (-(((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I))).re)
      ≤ L) :
    ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ)
      ≤ L + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
          + (1 + Real.log 4) := by
  classical
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  set σ : ℝ := 1 + 1 / Real.log (z : ℝ) with hσdef
  have hσ1 : (1 : ℝ) < σ := by
    rw [hσdef]
    have : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
    linarith
  have hsplit := tsum_re_prime_cpow_split (z := z) (t := t) hσ1
  have htail := abs_le.1 (abs_tsum_prime_tail_re_le (z := z) (t := t) hσ1)
  have htailC := tsum_primeTailTerm_le hz
  rw [← hσdef] at htailC
  have hshift := abs_le.1 (abs_sum_weight_shift_le (z := z) (by omega) hσ1.le
    (w := fun p : ℕ => Real.cos (t * Real.log (p : ℝ)))
    (fun p => Real.abs_cos_le_one _))
  have hident : ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)
      = (∑ n ∈ Nat.primesLE z, ((n : ℝ)) ^ (-σ) * Real.cos (t * Real.log n))
        + ∑ p ∈ Nat.primesLE z,
            Real.cos (t * Real.log (p : ℝ)) * (1 / (p : ℝ) - ((p : ℝ)) ^ (-σ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  have hshiftC : (σ - 1) * (Real.log z + Real.log 4) ≤ 1 + Real.log 4 := by
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hval : (σ - 1) * (Real.log z + Real.log 4)
        = 1 + Real.log 4 / Real.log (z : ℝ) := by
      rw [hσdef]
      field_simp
      ring
    have hdiv : Real.log 4 / Real.log (z : ℝ) ≤ Real.log 4 := by
      rw [div_le_iff₀ hlogz0]
      nlinarith
    rw [hval]
    linarith
  rw [hident]
  linarith [hL, hsplit, htail.1, htail.2, htailC, hshift.1, hshift.2, hshiftC]

end RHTower.Sieve
