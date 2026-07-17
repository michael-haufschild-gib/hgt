import GaloisForLFunctions.RHTower.CCMRectangularAutocorrelation

/-!
# The finite Möbius--log divisor paraproduct

The exact convolution identity `μ * log = Λ` rewrites every finite weighted von Mangoldt sum as a
pair-labelled divisor sum.  Specializing the weight to the critical moving tent gives the precise
Möbius--logarithm paraproduct that must be retained through the prime--polar cancellation.

This file is purely finite and algebraic.  It makes no estimate on either marginal and does not
assert the still-open compensated decomposition or one-sided cutoff-commutator bound.
-/

open Nat ArithmeticFunction Finset
open scoped BigOperators Moebius

namespace RHTower

noncomputable section

/-- The pair-labelled finite divisor paraproduct associated to a weight `w`.  An index
`x ∈ k.divisorsAntidiagonal` records the ordered factorization `x.1 * x.2 = k`. -/
def mobiusLogDivisorParaproduct (w : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K, ∑ x ∈ k.divisorsAntidiagonal,
    (ArithmeticFunction.moebius x.1 : ℝ) * Real.log x.2 * w k

/-- **Exact finite Möbius--log rewrite.** Every finitely weighted von Mangoldt sum is the
label-retaining divisor paraproduct obtained from `μ * log = Λ`. -/
theorem weightedVonMangoldt_eq_mobiusLogDivisorParaproduct
    (w : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 2 K, ArithmeticFunction.vonMangoldt k * w k) =
      mobiusLogDivisorParaproduct w K := by
  rw [mobiusLogDivisorParaproduct]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.log_apply, Finset.sum_mul]

/-- The exact critical half-density paraproduct for the moving multiplicative tent. -/
def rectangularMobiusLogDivisorParaproduct (L N : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K, ∑ x ∈ k.divisorsAntidiagonal,
    (ArithmeticFunction.moebius x.1 : ℝ) * Real.log x.2 / Real.sqrt k *
      rectangularMovingPrimeTent L N k

/-- **Critical Möbius--log divisor identity.** The complete moving von Mangoldt tent is exactly
the finite ordered-factorization paraproduct.  The equality is established before any
scalarization, so the Möbius sign, logarithmic complement, product scale, and cutoff label all
remain present. -/
theorem rectangularMovingPrimeTentSum_eq_mobiusLogDivisorParaproduct
    (L N : ℝ) (K : ℕ) :
    rectangularMovingPrimeTentSum L N K =
      rectangularMobiusLogDivisorParaproduct L N K := by
  rw [rectangularMovingPrimeTentSum,
    rectangularMobiusLogDivisorParaproduct]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.log_apply, Finset.sum_div, Finset.sum_mul]

end

end RHTower
