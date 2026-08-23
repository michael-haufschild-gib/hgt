import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open scoped ArithmeticFunction.Moebius

namespace RHTower

noncomputable section

/-- The Möbius sum over all common divisors of two natural numbers. -/
def mobiusCommonDivisorKernel (a b : ℕ) : ℤ :=
  ∑ d ∈ (a.gcd b).divisors, μ d

/-- Möbius inversion turns the common-divisor kernel into the coprimality indicator. -/
theorem mobiusCommonDivisorKernel_eq_coprimeIndicator (a b : ℕ) :
    mobiusCommonDivisorKernel a b = if a.Coprime b then 1 else 0 := by
  unfold mobiusCommonDivisorKernel
  have h := congrArg (fun f : ArithmeticFunction ℤ => f (a.gcd b))
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  change (∑ d ∈ (a.gcd b).divisors, (μ d : ℤ)) =
    if a.gcd b = 1 then 1 else 0 at h
  rw [h]

/-- On positive coordinates, the kernel is exactly the `0`--`1` coprimality matrix entry. -/
theorem mobiusCommonDivisorKernel_succ_eq_coprimeIndicator (a b : ℕ) :
    mobiusCommonDivisorKernel (a + 1) (b + 1) =
      if (a + 1).Coprime (b + 1) then 1 else 0 :=
  mobiusCommonDivisorKernel_eq_coprimeIndicator _ _

end

end RHTower
