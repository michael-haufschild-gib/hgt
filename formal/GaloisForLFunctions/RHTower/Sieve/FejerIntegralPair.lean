import GaloisForLFunctions.RHTower.Sieve.FejerLocalisation

/-!
# The Fejér pairing as an integral

Pairing `F(t)` and its reflection `F(-t)` against the triangular weight on `[0,T]` reproduces the
symmetric Fejér weights of `FejerLocalisation.lean`:

`∫_0^T F(t)(1 - t/T) dt + ∫_0^T F(-t)(1 - t/T) dt = ∑_{n < N} a_n W(T, log n)`.

Reflecting the argument negates the frequencies, which is exactly the second half of the symmetric
weight, so no change of variables and no absolute value is needed.

Combined with the localisation bound this says: the Fejér average of a Dirichlet polynomial over
`[0,T]`, symmetrised, is `a_1 T` up to an error controlled by the remaining coefficients.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- Pairing the reflected polynomial against a kernel negates the frequencies. -/
theorem integral_dirPoly_neg_mul (N : ℕ) (a : Fin N → ℂ) {K : ℝ → ℂ} (hK : Continuous K)
    (A B : ℝ) :
    (∫ t in A..B, dirPoly N a (-t) * K t)
      = ∑ n : Fin N, a n
          * ∫ t in A..B,
              Complex.exp (((t * (-Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I) * K t := by
  classical
  have hcont : ∀ n : Fin N, Continuous (fun t : ℝ =>
      Complex.exp (((t * (-Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I) * K t) := by
    intro n
    exact (Continuous.mul (by fun_prop) hK)
  have hexpand : ∀ t : ℝ, dirPoly N a (-t) * K t
      = ∑ n : Fin N, a n
          * (Complex.exp (((t * (-Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I) * K t) := by
    intro t
    rw [dirPoly, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    have harg : (((-t) * Real.log (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ)
        = ((t * (-Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hexpand t)]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  · exact fun n _ => ((hcont n).intervalIntegrable _ _).const_mul _

/-- **The symmetrised Fejér pairing is the weighted coefficient sum.** -/
theorem integral_fejer_pair_eq (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, dirPoly N a t * ((1 - t / T : ℝ) : ℂ))
      + (∫ t in (0 : ℝ)..T, dirPoly N a (-t) * ((1 - t / T : ℝ) : ℂ))
      = ∑ n : Fin N, a n * fejerWeightAt T (Real.log (((n : ℕ) : ℝ) + 1)) := by
  classical
  rw [integral_fejerHalf_dirPoly N a T,
    integral_dirPoly_neg_mul N a (continuous_fejerWeight T) 0 T, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [fejerWeightAt, ← mul_add]
  congr 1
  rw [integral_fejer_comm, integral_fejer_comm]

end RHTower.Sieve
