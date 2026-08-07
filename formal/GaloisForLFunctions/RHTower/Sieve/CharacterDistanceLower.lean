import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSumUpper
import GaloisForLFunctions.RHTower.Sieve.MertensSecond
import GaloisForLFunctions.RHTower.Sieve.DistanceTriangle

/-!
# The distance between two characters

The Granville–Soundararajan distance between the characters `n^{it}` and `n^{iu}` is

`D(n^{it}, n^{iu}; z)² = ∑_{p ≤ z} 1/p − ∑_{p ≤ z} cos((t−u) log p)/p`,

so Mertens' second theorem bounds it below by `log log z` minus whatever upper bound is available for
the cosine sum at frequency `t − u`.  The upper bound comes from the prime series through the
truncation and abscissa-shift passages, and ultimately from an upper bound for `|ζ|` on the line.

The point of this direction is that it is *window-free*: the estimate holds for every pair `t, u`,
with no restriction of the form `|t − u| log z ≤ π`.  It is therefore what makes a close frequency
unique over a whole range rather than only inside one cell.
-/

namespace RHTower.Sieve

open Complex

theorem charFn_mul_conj_re (t u : ℝ) (p : ℕ) :
    (charFn t p * (starRingEnd ℂ) (charFn u p)).re
      = Real.cos ((t - u) * Real.log (p : ℝ)) := by
  have hconj : (starRingEnd ℂ) (charFn u p)
      = Complex.exp ((((-(u * Real.log (p : ℝ))) : ℝ) : ℂ) * Complex.I) := by
    rw [charFn, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [charFn, hconj, ← Complex.exp_add]
  have harg : (((t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I
      + (((-(u * Real.log (p : ℝ))) : ℝ) : ℂ) * Complex.I
      = ((((t - u) * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

/-- **The character distance as a difference of two prime sums.** -/
theorem mulDistSqPair_charFn_eq_sub (t u : ℝ) (P : Finset ℕ) :
    mulDistSqPair (charFn t) (charFn u) P
      = (∑ p ∈ P, 1 / (p : ℝ)) - ∑ p ∈ P, Real.cos ((t - u) * Real.log (p : ℝ)) / (p : ℝ) := by
  rw [mulDistSqPair, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [charFn_mul_conj_re]
  ring

/-- **The window-free lower bound for the character distance.**  Mertens' second theorem against any
upper bound for the prime series at the standard abscissa. -/
theorem le_mulDistSqPair_charFn {z : ℕ} (hz : 3 ≤ z) {t u L : ℝ}
    (hL : (∑' p : Nat.Primes,
        (((p : ℕ) : ℂ) ^
          (-(((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * Complex.I))).re)
      ≤ L) :
    logLog z - mertensSecondLowerConst - L
        - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
        - (1 + Real.log 4)
      ≤ mulDistSqPair (charFn t) (charFn u) (Nat.primesLE z) := by
  have hcos := sum_cos_div_prime_le_of_ge hz hL
  have hmert := le_mertensS (N := z) (by omega)
  rw [mulDistSqPair_charFn_eq_sub]
  have hS : (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) = mertensS z := rfl
  rw [hS]
  linarith

end RHTower.Sieve
