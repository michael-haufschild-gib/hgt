import GaloisForLFunctions.HTGeometry.PrimeProfileSeparatedPacketExact

/-!
# Same-prime, same-depth Hadamard fusion

`primeRadialFusion` performs Cauchy convolution along valuation depth.  Replica diagonal
contractions need a different operation: retain one prime and one valuation depth, then multiply
the two coefficients at that exact coordinate.  This module supplies that coefficient-faithful
Hadamard contraction as an arithmetic source supported on positive prime powers.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- Coefficientwise, same-prime and same-depth Hadamard contraction. -/
def primeDepthHadamardFusion
    (u v : PrimePowerClockIndex → ℂ) : ArithmeticFunction ℂ :=
  arithmeticFunctionOfPrimePowerProfile (fun x => u x * v x)

/-- The contraction keeps the literal product at every `(prime, valuation-depth)` coordinate. -/
@[simp] theorem primePowerCoordinateProfile_primeDepthHadamardFusion
    (u v : PrimePowerClockIndex → ℂ) (x : PrimePowerClockIndex) :
    primePowerCoordinateProfile (primeDepthHadamardFusion u v) x = u x * v x := by
  exact primePowerCoordinateProfile_arithmeticFunctionOfPrimePowerProfile _ x

/-- Hadamard contraction introduces no coefficients away from positive prime powers. -/
theorem primeDepthHadamardFusion_supportedOnPositivePrimePowers
    (u v : PrimePowerClockIndex → ℂ) :
    PrimeProfileSupportedOnPositivePrimePowers (primeDepthHadamardFusion u v) :=
  arithmeticFunctionOfPrimePowerProfile_supportedOnPositivePrimePowers _

end


end GaloisForLFunctions.HTGeometry
