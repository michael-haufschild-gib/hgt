import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValuesCount

/-!
# Pairing a Dirichlet polynomial against a kernel

`∫_A^B F(t) K(t) dt = ∑_{n < N} a_n ∫_A^B n^{it} K(t) dt`.

For a finite Dirichlet polynomial this is linearity of the integral — no convergence question
arises — and it is the finite form of the bridge that a short-interval argument uses: choosing `K`
to concentrate near a point turns the left side into a short-interval average and the right side
into the coefficient sum weighted by the transform of `K` at the frequencies `log n`.

The transform of the kernel at `log n` is `∫_A^B e^{it log n} K(t) dt`, so the identity says that
pairing with a kernel evaluates the coefficient sum against that transform.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **Pairing a Dirichlet polynomial against a kernel.** -/
theorem integral_dirPoly_mul (N : ℕ) (a : Fin N → ℂ) {K : ℝ → ℂ} (hK : Continuous K) (A B : ℝ) :
    (∫ t in A..B, dirPoly N a t * K t)
      = ∑ n : Fin N, a n
          * ∫ t in A..B,
              Complex.exp (((t * Real.log (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I) * K t := by
  classical
  have hcont : ∀ n : Fin N, Continuous (fun t : ℝ =>
      Complex.exp (((t * Real.log (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I) * K t) := by
    intro n
    exact (Continuous.mul (by fun_prop) hK)
  have hexpand : ∀ t : ℝ, dirPoly N a t * K t
      = ∑ n : Fin N, a n
          * (Complex.exp (((t * Real.log (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I) * K t) := by
    intro t
    rw [dirPoly, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hexpand t)]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  · exact fun n _ => ((hcont n).intervalIntegrable _ _).const_mul _

end RHTower.Sieve
