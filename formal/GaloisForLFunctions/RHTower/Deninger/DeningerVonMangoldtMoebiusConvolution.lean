import Mathlib

/-!
# The von Mangoldt–Möbius convolution identity

The Dirichlet convolution of the von Mangoldt function with the Möbius function is the pointwise
product of Möbius with the logarithm, up to sign:

`Λ * μ = -(μ · log)`.

Convolving with the zeta function turns the left side into `Λ` and the right side into `Λ` by
mathlib's `sum_moebius_mul_log_eq`, and convolution with `ζ` is injective because `μ` inverts it.
This is the arithmetic step that turns the derivative of the adiabatic Möbius lift into the Euler
connection.

* `arithmeticFunction_mul_zeta_injective` : convolution with `ζ` is injective.
* `vonMangoldt_mul_moebius` : **`Λ * μ = -(μ · log)`.**
-/

namespace GaloisForLFunctions

open ArithmeticFunction

open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Convolution with `ζ` is injective on real arithmetic functions. -/
theorem arithmeticFunction_mul_zeta_injective {f g : ArithmeticFunction ℝ}
    (h : f * (ζ : ArithmeticFunction ℝ) = g * (ζ : ArithmeticFunction ℝ)) : f = g := by
  have hmul := congrArg (fun u : ArithmeticFunction ℝ => u * (μ : ArithmeticFunction ℝ)) h
  simpa [mul_assoc, coe_zeta_mul_coe_moebius] using hmul

/-- **`Λ * μ = -(μ · log)`.** -/
theorem vonMangoldt_mul_moebius :
    (Λ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)
      = -(ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) ArithmeticFunction.log) := by
  refine arithmeticFunction_mul_zeta_injective ?_
  have hleft : (Λ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)
      * (ζ : ArithmeticFunction ℝ) = (Λ : ArithmeticFunction ℝ) := by
    rw [mul_assoc, coe_moebius_mul_coe_zeta, mul_one]
  rw [hleft]
  ext n
  rw [coe_mul_zeta_apply]
  have hterm : ∀ d : ℕ,
      (-(ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) ArithmeticFunction.log)) d
        = -((μ d : ℤ) : ℝ) * ArithmeticFunction.log d := by
    intro d
    simp [ArithmeticFunction.pmul_apply]
  rw [Finset.sum_congr rfl fun d _ => hterm d]
  have hsum : (∑ d ∈ n.divisors, -((μ d : ℤ) : ℝ) * ArithmeticFunction.log d)
      = -∑ d ∈ n.divisors, ((μ d : ℤ) : ℝ) * ArithmeticFunction.log d := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hsum, ArithmeticFunction.sum_moebius_mul_log_eq, neg_neg]

end GaloisForLFunctions
