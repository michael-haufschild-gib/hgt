import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.CoprimePoleMonomials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalConstantPlaces

/-!
# The actual rational infinity place of the Hermitian field

The normalized infinity place has constant residue field. Its additive
and radical coordinates have pole orders Q+1 and Q respectively. These
are the normalized valuation orders in the actual function field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "η" => kummerTraceConstant p s
local notation "H" => HermitianKummerField p s

/-- The normalized infinity valuation of the actual Hermitian function field. -/
abbrev hermitianInfinityValuation : Valuation H (WithZero (Multiplicative ℤ)) :=
  squareKummerInfinityValuation p s η⁻¹ s 1

/-- Nonzero constants are units at the Hermitian infinity place. -/
theorem hermitianInfinityValuation_constant (a : K) (ha : a ≠ 0) :
    hermitianInfinityValuation p s (algebraMap K H a) = 1 :=
  squareKummerInfinityValuation_constant p s η⁻¹ s 1 a ha

/-- The additive Hermitian coordinate has pole order Q+1 at infinity. -/
theorem hermitianInfinityValuation_additive :
    hermitianInfinityValuation p s (hermitianKummerAdditiveCoordinate p s) =
      WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
  rw [hermitianKummerAdditiveCoordinate, map_mul,
    hermitianInfinityValuation_constant p s ((η : K)⁻¹) (inv_ne_zero (kummerTraceConstant p s).ne_zero), one_mul]
  exact squareKummerInfinityValuation_coordinate p s η⁻¹ s 1

/-- The radical Hermitian coordinate has pole order Q at infinity. -/
theorem hermitianInfinityValuation_radical :
    hermitianInfinityValuation p s (hermitianKummerRadicalCoordinate p s) =
      WithZero.exp ((Q : ℕ) : ℤ) := by
  exact (squareKummerInfinityValuation_root p s η⁻¹ s 1).trans
    (congrArg (fun n : ℕ => WithZero.exp (n : ℤ)) (pow_one Q))

/-- The Hermitian infinity place is rational over the specified square constant field. -/
def hermitianInfinityRationalPlace : RationalConstantFieldPlaces K H :=
  squareKummerRationalInfinityPlace p s η⁻¹ s 1

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
