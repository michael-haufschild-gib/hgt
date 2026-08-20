import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# The Mertens mass of a prime range, sharply

Mertens' second theorem in the corpus carries two different additive constants at the two ends, so
the difference `mertensS z − mertensS z₀` inherits their sum — useless for a *narrow* range, where
the true mass `log(log z / log z₀)` is small.  Mertens' *first* theorem gives the sharp bound
directly: for `z₀ < p` one has `1/p ≤ (log p / p)/log z₀`, so

```text
   ∑_{z₀ < p ≤ z} 1/p ≤ (𝔄(z) − 𝔄(z₀))/log z₀ ≤ (log z − log z₀ + 2c)/log z₀ ,
```

with `c = mertensFirstConst` the single constant of `|𝔄(N) − log N| ≤ c`.  For a polylogarithmic
band `[V^{a₀}, 2V^{a₁}]` this tends to `(a₁ − a₀)/a₀`, which is what the Route E cofactor card needs
in order to discharge the band hypothesis of its unsigned squarefree estimates.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The log-weighted mass of a range of primes. -/
theorem sum_logDiv_primesRange {z₀ z : ℕ} (hz : z₀ ≤ z) :
    ∑ p ∈ primesRange z₀ z, Real.log (p : ℝ) / (p : ℝ) = mertensA z - mertensA z₀ := by
  rw [primesRange, Finset.sum_sdiff_eq_sub (primesLE_subset hz), mertensA, mertensA]

/-- **The Mertens mass of a prime range.**  Sharp: the constant does not depend on the range. -/
theorem sum_inv_primesRange_le {z₀ z : ℕ} (h2 : 2 ≤ z₀) (hz : z₀ ≤ z) :
    ∑ p ∈ primesRange z₀ z, 1 / (p : ℝ)
      ≤ (Real.log (z : ℝ) - Real.log (z₀ : ℝ) + 2 * mertensFirstConst) / Real.log (z₀ : ℝ) := by
  have hz₀R : (2 : ℝ) ≤ (z₀ : ℝ) := by exact_mod_cast h2
  have hlog0 : 0 < Real.log (z₀ : ℝ) := Real.log_pos (by linarith)
  have hterm : ∀ p ∈ primesRange z₀ z,
      1 / (p : ℝ) ≤ (Real.log (p : ℝ) / (p : ℝ)) / Real.log (z₀ : ℝ) := by
    intro p hp
    have hprime : p.Prime := primesRange_prime hp
    have hpz₀ : z₀ < p := by
      rw [primesRange, Finset.mem_sdiff] at hp
      have hnot := hp.2
      rw [mem_primesLE] at hnot
      by_contra hle
      exact hnot ⟨by omega, hprime⟩
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have : (0 : ℕ) < p := by omega
      exact_mod_cast this
    have hlogle : Real.log (z₀ : ℝ) ≤ Real.log (p : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast hpz₀.le
    rw [div_div, div_le_div_iff₀ hp0 (by positivity)]
    nlinarith [hlogle, hp0]
  have hsum : ∑ p ∈ primesRange z₀ z, 1 / (p : ℝ)
      ≤ ∑ p ∈ primesRange z₀ z, (Real.log (p : ℝ) / (p : ℝ)) / Real.log (z₀ : ℝ) :=
    Finset.sum_le_sum hterm
  have hfac : ∑ p ∈ primesRange z₀ z, (Real.log (p : ℝ) / (p : ℝ)) / Real.log (z₀ : ℝ)
      = (mertensA z - mertensA z₀) / Real.log (z₀ : ℝ) := by
    rw [← Finset.sum_div, sum_logDiv_primesRange hz]
  rw [hfac] at hsum
  refine le_trans hsum ?_
  refine div_le_div_of_nonneg_right ?_ hlog0.le
  have hA1 := abs_mertensA_sub_log_le (N := z) (by omega)
  have hA0 := abs_mertensA_sub_log_le (N := z₀) (by omega)
  rw [abs_le] at hA1 hA0
  linarith [hA1.2, hA0.1]

end

end RHTower.Sieve
