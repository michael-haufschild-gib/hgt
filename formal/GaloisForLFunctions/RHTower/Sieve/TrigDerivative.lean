import GaloisForLFunctions.RHTower.Sieve.TrigParseval

/-!
# The derivative of a trigonometric polynomial

Differentiating `S(t) = ∑_{n < N} c_n e(nt)` term by term multiplies each coefficient by `2πin`, so
the derivative is again a trigonometric polynomial and Parseval evaluates its energy:

`∫_0^(1 : ℕ) |S'(t)|² dt = ∑_{n < N} (2πn)² |c_n|²`.

Together with `TrigParseval.lean` this supplies both integrals appearing in Gallagher's Sobolev
bound, so the local averages it produces are expressed entirely in the coefficient energy.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The coefficients of the derivative. -/
noncomputable def derivCoeff (N : ℕ) (c : Fin N → ℂ) : Fin N → ℂ :=
  fun n => ((2 * Real.pi * ((n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I * c n

/-- The derivative of a single character. -/
theorem hasDerivAt_circleFreq_mul (a t : ℝ) :
    HasDerivAt (fun s : ℝ => circleFreq (a * s))
      (circleFreq (a * t) * (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I)) t := by
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) ((1 : ℝ) : ℂ) t := (hasDerivAt_id t).ofReal_comp
  have hg := (hid.const_mul (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I)).cexp
  have hfun : ∀ s : ℝ,
      Complex.exp ((((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) * (s : ℂ)) = circleFreq (a * s) := by
    intro s
    rw [circleFreq]
    congr 1
    push_cast
    ring
  simp only [hfun] at hg
  have hval : circleFreq (a * t) * ((((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) * ((1 : ℝ) : ℂ))
      = circleFreq (a * t) * (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hval] at hg
  exact hg

/-- **The derivative of a trigonometric polynomial is a trigonometric polynomial.** -/
theorem hasDerivAt_expSum (N : ℕ) (c : Fin N → ℂ) (t : ℝ) :
    HasDerivAt (expSum N c) (expSum N (derivCoeff N c) t) t := by
  have hfun : expSum N c = fun s : ℝ => ∑ n : Fin N, c n * circleFreq (((n : ℕ) : ℝ) * s) := by
    funext s
    exact expSum_eq_sum N c s
  rw [hfun]
  have hd : HasDerivAt (fun s : ℝ => ∑ n : Fin N, c n * circleFreq (((n : ℕ) : ℝ) * s))
      (∑ n : Fin N, c n * (circleFreq (((n : ℕ) : ℝ) * t)
        * (((2 * Real.pi * ((n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))) t := by
    have hsum := HasDerivAt.sum
      (fun (n : Fin N) (_ : n ∈ (Finset.univ : Finset (Fin N))) =>
        (hasDerivAt_circleFreq_mul ((n : ℕ) : ℝ) t).const_mul (c n))
    have heq : (∑ n ∈ (Finset.univ : Finset (Fin N)),
        fun s : ℝ => c n * circleFreq (((n : ℕ) : ℝ) * s))
        = fun s : ℝ => ∑ n : Fin N, c n * circleFreq (((n : ℕ) : ℝ) * s) := by
      funext s
      simp [Finset.sum_apply]
    rw [heq] at hsum
    exact hsum
  have hval : (∑ n : Fin N, c n * (circleFreq (((n : ℕ) : ℝ) * t)
      * (((2 * Real.pi * ((n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)))
      = expSum N (derivCoeff N c) t := by
    rw [expSum_eq_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [derivCoeff]
    ring
  rw [← hval]
  exact hd

/-- **The energy of the derivative.** -/
theorem integral_normSq_derivCoeff (N : ℕ) (c : Fin N → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖expSum N (derivCoeff N c) t‖ ^ (2 : ℕ))
      = ∑ n : Fin N, (2 * Real.pi * ((n : ℕ) : ℝ)) ^ (2 : ℕ) * ‖c n‖ ^ (2 : ℕ) := by
  rw [integral_normSq_expSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn : (0 : ℝ) ≤ 2 * Real.pi * ((n : ℕ) : ℝ) := by positivity
  rw [derivCoeff, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_of_nonneg hn, mul_pow]

end RHTower.Sieve
