import GaloisForLFunctions.RHTower.Sieve.CircleOrthogonality

/-!
# The squared modulus of a trigonometric polynomial

Writing `S(t) = ∑_{n < N} c_n e(nt)`, the identity `|z|² = z conj(z)` expands the squared modulus
into the double sum

`|S(t)|² = ∑_m ∑_n c_m conj(c_n) e((m-n)t)`,

whose cross terms integrate to `1` on the diagonal and `0` off it by the orthogonality of
`CircleOrthogonality.lean`.  Those are the two ingredients of Parseval; only the interchange of the
integral with the finite sums is left.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The trigonometric polynomial as a sum of characters. -/
theorem expSum_eq_sum (N : ℕ) (c : Fin N → ℂ) (t : ℝ) :
    expSum N c t = ∑ n : Fin N, c n * circleFreq (((n : ℕ) : ℝ) * t) := by
  rw [expSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [circleFreq_pow]

/-- **The squared modulus expanded.** -/
theorem normSq_expSum_eq (N : ℕ) (c : Fin N → ℂ) (t : ℝ) :
    ((‖expSum N c t‖ ^ 2 : ℝ) : ℂ)
      = ∑ m : Fin N, ∑ n : Fin N,
          (c m * (starRingEnd ℂ) (c n))
            * circleFreq (((m : ℕ) : ℝ) * t - ((n : ℕ) : ℝ) * t) := by
  have hz : ((‖expSum N c t‖ ^ 2 : ℝ) : ℂ)
      = expSum N c t * (starRingEnd ℂ) (expSum N c t) := by
    rw [mul_comm, conj_mul_self]
  rw [hz, expSum_eq_sum, map_sum]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  have hchar : circleFreq (((m : ℕ) : ℝ) * t)
      * (starRingEnd ℂ) (circleFreq (((n : ℕ) : ℝ) * t))
      = circleFreq (((m : ℕ) : ℝ) * t - ((n : ℕ) : ℝ) * t) := by
    rw [mul_comm, conj_circleFreq_mul]
  rw [map_mul]
  calc c m * circleFreq (((m : ℕ) : ℝ) * t)
        * ((starRingEnd ℂ) (c n) * (starRingEnd ℂ) (circleFreq (((n : ℕ) : ℝ) * t)))
      = (c m * (starRingEnd ℂ) (c n))
        * (circleFreq (((m : ℕ) : ℝ) * t)
          * (starRingEnd ℂ) (circleFreq (((n : ℕ) : ℝ) * t))) := by ring
    _ = (c m * (starRingEnd ℂ) (c n))
        * circleFreq (((m : ℕ) : ℝ) * t - ((n : ℕ) : ℝ) * t) := by rw [hchar]

/-- **The cross terms are orthogonal.** -/
theorem integral_cross_term (m n : ℕ) :
    (∫ t in (0 : ℝ)..1, circleFreq ((m : ℝ) * t - (n : ℝ) * t))
      = if m = n then 1 else 0 := by
  have hrw : ∀ t : ℝ, circleFreq ((m : ℝ) * t - (n : ℝ) * t)
      = circleFreq (((((m : ℤ) - (n : ℤ) : ℤ)) : ℝ) * t) := by
    intro t
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_congr (g := fun t => circleFreq (((((m : ℤ) - (n : ℤ) : ℤ)) : ℝ) * t))
    (fun t _ => hrw t)]
  rw [integral_circleFreq_intCast]
  by_cases h : m = n
  · rw [if_pos h, if_pos]
    omega
  · rw [if_neg h, if_neg]
    omega

end RHTower.Sieve
