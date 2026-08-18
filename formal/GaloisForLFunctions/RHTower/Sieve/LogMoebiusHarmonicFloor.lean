import GaloisForLFunctions.RHTower.Mollifier
import GaloisForLFunctions.RHTower.Sieve.MoebiusDiagonalSupport

/-!
# The logarithmic Möbius sum against the harmonic floor

The tree owns the exact Möbius inversion of the polar unit,
`∑_{d ≤ N} μ(d) H_{⌊N/d⌋}/d = 1`.  Replacing the harmonic floor by its logarithm turns it into an
exact identity for the logarithmic Möbius sum, with the whole remaining content isolated in the
error sum `∑_{d ≤ N} (μ(d)/d)(H_{⌊N/d⌋} − log(N/d))`.  This is the last elementary step of Graham's
evaluation.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

theorem harmonicFloorMoebiusSum_eq_one_real (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N,
        ((μ d : ℤ) : ℝ) / (d : ℝ) * ((harmonic (N / d) : ℚ) : ℝ)) = 1 := by
  have h := RHTower.harmonicFloorMoebiusSum_eq_one N hN
  have hcast : ((∑ d ∈ Finset.Icc 1 N,
      ((μ d : ℤ) : ℚ) / (d : ℚ) * harmonic (N / d) : ℚ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 N,
        ((μ d : ℤ) : ℝ) / (d : ℝ) * ((harmonic (N / d) : ℚ) : ℝ) := by
    push_cast
    ring
  rw [← hcast, h]
  norm_num

/-- **The logarithmic Möbius sum, exactly.**  The whole content is the harmonic-versus-logarithm
error sum. -/
theorem sum_moebius_log_div_eq_one_sub_error (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) * Real.log ((N : ℝ) / (d : ℝ)))
      = 1 - ∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) *
          (((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))) := by
  have hbase := harmonicFloorMoebiusSum_eq_one_real N hN
  have hsplit : (∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) *
        (((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))))
      = (∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) * ((harmonic (N / d) : ℚ) : ℝ))
        - ∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) *
            Real.log ((N : ℝ) / (d : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [hsplit, hbase]
  ring

end RHTower.Sieve
