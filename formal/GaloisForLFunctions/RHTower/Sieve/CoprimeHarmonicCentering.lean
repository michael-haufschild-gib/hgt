import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation

/-!
# Centering the coprime harmonic decomposition

Subtracting any constant multiple of the totient density from the coprime harmonic sum is the same
as centering each harmonic term of its Möbius decomposition.  With `C = log z + γ` this is the exact
form in which the coprime harmonic asymptotic is proved: the main term is `(φ(e)/e)(log z + γ)` and
the remainder is a divisor-indexed sum of centered harmonic defects.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **Centering the decomposition.**  For every constant `C`, -/
theorem coprimeHarmonic_sub_totient_mul {e : ℕ} (he : 0 < e) (z : ℕ) (C : ℝ) :
    coprimeHarmonic e z - (Nat.totient e : ℝ) / (e : ℝ) * C
      = ∑ f ∈ e.divisors, ((μ f : ℤ) : ℝ) / (f : ℝ) *
          ((∑ j ∈ Finset.Icc 1 (z / f), 1 / (j : ℝ)) - C) := by
  have hdecomp := coprimeHarmonic_eq_sum_divisors (e := e) (z := z) he
  have hnorm := sum_moebius_div_divisors_eq_totient_div he
  have hsplit : ∑ f ∈ e.divisors, ((μ f : ℤ) : ℝ) / (f : ℝ) *
        ((∑ j ∈ Finset.Icc 1 (z / f), 1 / (j : ℝ)) - C)
      = (∑ f ∈ e.divisors, ((μ f : ℤ) : ℝ) / (f : ℝ) *
          ∑ j ∈ Finset.Icc 1 (z / f), 1 / (j : ℝ))
        - (∑ f ∈ e.divisors, ((μ f : ℤ) : ℝ) / (f : ℝ)) * C := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  rw [hsplit, ← hdecomp, hnorm]

end RHTower.Sieve
