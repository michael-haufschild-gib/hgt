import GaloisForLFunctions.RHTower.Sieve.CoprimeModulusConstant

/-!
# The exact identity at a general modulus

The coprime inversion of brick 30 gives, for every modulus `e` and every centering weight `c`, the
exact analogue of `sum_moebius_log_div_eq_one_sub_error`: the weighted logarithmic Möbius sum over
the residues coprime to `e` equals `1` minus the coprime harmonic defect sum.  Specialising
`c = φ(e)/e` makes the defect the one bounded by bricks 34–36.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **The exact identity at modulus `e`.** -/
theorem sum_coprime_moebius_log_eq_one_sub_error {e N : ℕ} (hN : 1 ≤ N) (c : ℝ) :
    (∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime e d),
        ((μ d : ℤ) : ℝ) / (d : ℝ) * (c * Real.log ((N : ℝ) / (d : ℝ))))
      = 1 - ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime e d),
          ((μ d : ℤ) : ℝ) / (d : ℝ) *
            (coprimeHarmonic e (N / d) - c * Real.log ((N : ℝ) / (d : ℝ))) := by
  have hbase := sum_moebius_coprime_harmonic_eq_one (e := e) hN
  have hsplit : (∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime e d),
        ((μ d : ℤ) : ℝ) / (d : ℝ) *
          (coprimeHarmonic e (N / d) - c * Real.log ((N : ℝ) / (d : ℝ))))
      = (∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime e d),
          ((μ d : ℤ) : ℝ) / (d : ℝ) * coprimeHarmonic e (N / d))
        - ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime e d),
            ((μ d : ℤ) : ℝ) / (d : ℝ) * (c * Real.log ((N : ℝ) / (d : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [hsplit, hbase]
  ring

end RHTower.Sieve
