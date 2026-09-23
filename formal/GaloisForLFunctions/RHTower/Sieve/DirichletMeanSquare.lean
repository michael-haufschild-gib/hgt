import GaloisForLFunctions.RHTower.Sieve.DirichletExpansion

/-!
# The mean square of a Dirichlet polynomial

Integrating the expansion of `DirichletExpansion.lean` term by term,

`∫_0^T |F(t)|² dt = ∑_m ∑_n a_m conj(a_n) ∫_0^T e^{it(log m - log n)} dt`,

and the inner integrals are `T` on the diagonal and at most `2/|log(m/n)|` off it.  The diagonal
therefore contributes `T ∑_n |a_n|²` and the rest is an off-diagonal sum of reciprocal logarithmic
separations.

Bounding that off-diagonal sum by `∑_n |a_n|² · O(n)` is the Montgomery–Vaughan mean value theorem
and is *not* proved here: it is a Hilbert inequality for the frequencies `log n`, the same
obstruction `sum_inv_abs_dist_le` identifies.  What this module supplies is the exact reduction to
it.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The cross-term phases are interval-integrable. -/
theorem intervalIntegrable_dirPhase (u : ℝ) (A B : ℝ) :
    IntervalIntegrable (fun t : ℝ => Complex.exp (((t * u : ℝ) : ℂ) * Complex.I))
      volume A B := intervalIntegrable_exp_phase u A B

/-- **The mean square as a double sum of phase integrals.** -/
theorem integral_normSq_dirPoly_eq (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ((‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ))
      = ∑ m : Fin N, ∑ n : Fin N, (a m * (starRingEnd ℂ) (a n))
          * (∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
              - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)) := by
  classical
  rw [intervalIntegral.integral_congr (fun t _ => normSq_dirPoly_eq N a t)]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      exact intervalIntegral.integral_const_mul _ _
    · exact fun n _ => (intervalIntegrable_dirPhase _ 0 T).const_mul _
  · intro m _
    have hsum := IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := T)
      (Finset.univ : Finset (Fin N))
      (f := fun n t => (a m * (starRingEnd ℂ) (a n))
        * Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
            - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
      (fun n _ => (intervalIntegrable_dirPhase _ 0 T).const_mul _)
    have heq : (∑ n : Fin N, fun t : ℝ => (a m * (starRingEnd ℂ) (a n))
          * Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
              - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
        = fun t : ℝ => ∑ n : Fin N, (a m * (starRingEnd ℂ) (a n))
          * Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
              - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I) := by
      funext t
      simp [Finset.sum_apply]
    rw [heq] at hsum
    exact hsum

/-- The diagonal phase integral is the length of the interval. -/
theorem integral_dirPhase_diag (m : ℕ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log ((m : ℝ) + 1)
        - Real.log ((m : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)) = (T : ℂ) := by
  have hzero : Real.log ((m : ℝ) + 1) - Real.log ((m : ℝ) + 1) = 0 := by ring
  rw [hzero]
  exact integral_exp_phase_zero T

/-- The off-diagonal phase integrals are small. -/
theorem norm_integral_dirPhase_off {m n : ℕ} (h : m ≠ n) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log ((m : ℝ) + 1)
        - Real.log ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)‖
      ≤ 2 / |Real.log ((m : ℝ) + 1) - Real.log ((n : ℝ) + 1)| := by
  have hne : Real.log ((m : ℝ) + 1) - Real.log ((n : ℝ) + 1) ≠ 0 :=
    sub_ne_zero_of_ne (log_succ_injective h)
  exact norm_integral_exp_phase_le _ hne T

end RHTower.Sieve
