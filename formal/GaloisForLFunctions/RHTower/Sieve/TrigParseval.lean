import GaloisForLFunctions.RHTower.Sieve.TrigExpansion

/-!
# Parseval for trigonometric polynomials

`∫_0^1 |S(t)|² dt = ∑_{n < N} |c_n|²`  for  `S(t) = ∑_{n < N} c_n e(nt)`.

The expansion of `TrigExpansion.lean` writes the integrand as a finite double sum of characters;
interchanging the integral with the sums and applying orthogonality kills every off-diagonal term
and leaves `c_n conj(c_n) = |c_n|²` on the diagonal.

This is the energy identity Gallagher's route to the sharp large sieve consumes: it converts the
local averages produced by `GallagherSobolev.lean` into the coefficient energy.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- Characters with a difference frequency are interval-integrable. -/
theorem intervalIntegrable_circleFreq_sub (m n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => circleFreq ((m : ℝ) * t - (n : ℝ) * t)) volume a b := by
  refine Continuous.intervalIntegrable ?_ a b
  unfold circleFreq
  fun_prop

/-- **Parseval for trigonometric polynomials.** -/
theorem integral_normSq_expSum (N : ℕ) (c : Fin N → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖expSum N c t‖ ^ 2) = ∑ n : Fin N, ‖c n‖ ^ 2 := by
  classical
  -- each cross term integrates to a Kronecker delta
  have hterm : ∀ m n : Fin N,
      (∫ t in (0 : ℝ)..1, (c m * (starRingEnd ℂ) (c n))
          * circleFreq (((m : ℕ) : ℝ) * t - ((n : ℕ) : ℝ) * t))
        = if m = n then c m * (starRingEnd ℂ) (c n) else 0 := by
    intro m n
    rw [intervalIntegral.integral_const_mul, integral_cross_term]
    by_cases h : m = n
    · subst h
      simp
    · have hval : ((m : ℕ)) ≠ ((n : ℕ)) := fun hcon => h (Fin.val_injective hcon)
      rw [if_neg hval, if_neg h, mul_zero]
  -- interchange the integral with the two finite sums
  have hinner : ∀ m : Fin N,
      (∫ t in (0 : ℝ)..1, ∑ n : Fin N, (c m * (starRingEnd ℂ) (c n))
          * circleFreq (((m : ℕ) : ℝ) * t - ((n : ℕ) : ℝ) * t))
        = ∑ n : Fin N, (if m = n then c m * (starRingEnd ℂ) (c n) else 0) := by
    intro m
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun n _ => hterm m n
    · exact fun n _ => (intervalIntegrable_circleFreq_sub _ _ 0 1).const_mul _
  have hcomplex : (∫ t in (0 : ℝ)..1, ((‖expSum N c t‖ ^ 2 : ℝ) : ℂ))
      = ∑ m : Fin N, ((‖c m‖ ^ 2 : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_congr (fun t _ => normSq_expSum_eq N c t)]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [hinner m, Finset.sum_ite_eq Finset.univ m
        (fun n => c m * (starRingEnd ℂ) (c n))]
      rw [if_pos (Finset.mem_univ m)]
      rw [mul_comm, conj_mul_self]
    · intro m _
      have hsum := IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (Finset.univ : Finset (Fin N))
        (f := fun n t => (c m * (starRingEnd ℂ) (c n))
          * circleFreq (((m : ℕ) : ℝ) * t - ((n : ℕ) : ℝ) * t))
        (fun n _ => (intervalIntegrable_circleFreq_sub _ _ 0 1).const_mul _)
      have heq : (∑ i : Fin N, fun t : ℝ => (c m * (starRingEnd ℂ) (c i))
            * circleFreq (((m : ℕ) : ℝ) * t - ((i : ℕ) : ℝ) * t))
          = fun t : ℝ => ∑ n : Fin N, (c m * (starRingEnd ℂ) (c n))
            * circleFreq (((m : ℕ) : ℝ) * t - ((n : ℕ) : ℝ) * t) := by
        funext t
        simp [Finset.sum_apply]
      rw [heq] at hsum
      exact hsum
  -- descend to the real statement
  rw [intervalIntegral.integral_ofReal] at hcomplex
  rw [← Complex.ofReal_sum] at hcomplex
  exact_mod_cast hcomplex

end RHTower.Sieve
