import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOriginFunctionOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerConstantField
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalConstantPlaces

/-!
# The actual rational origin of the Hermitian function field

The normalized origin has residue field equal to the stated constants.
Its additive coordinate has zero order Q+1, while its radical coordinate
is a uniformizer. These are orders of the actual valuation, rather than
intersection multiplicities in the affine polynomial equation alone.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "η" => kummerTraceConstant p s
local notation "H" => HermitianKummerField p s
local notation "w" => squareKummerOriginPlace p s η⁻¹ (Q - 2) 1

/-- The normalized origin valuation of the actual Hermitian function field. -/
abbrev hermitianOriginValuation : Valuation H (WithZero (Multiplicative ℤ)) :=
  squareKummerOriginValuation p s η⁻¹ (Q - 2) 1

/-- Every nonzero stated constant is a unit at the normalized Hermitian origin. -/
theorem hermitianOriginValuation_constant (a : K) (ha : a ≠ 0) :
    hermitianOriginValuation p s (algebraMap K H a) = 1 :=
  heightOne_valuation_constant w a ha

/-- The additive coordinate has zero order Q+1 at the actual rational origin. -/
theorem hermitianOriginValuation_additive :
    hermitianOriginValuation p s (hermitianKummerAdditiveCoordinate p s) =
      WithZero.exp (-((Q + 1 : ℕ) : ℤ)) := by
  rw [hermitianKummerAdditiveCoordinate, map_mul,
    hermitianOriginValuation_constant p s ((η : K)⁻¹) (inv_ne_zero (kummerTraceConstant p s).ne_zero), one_mul]
  exact squareKummerOriginValuation_coordinate p s η⁻¹ (Q - 2) 1

/-- The radical coordinate has a simple zero and is a uniformizer at the Hermitian origin. -/
theorem hermitianOriginValuation_radical :
    hermitianOriginValuation p s (hermitianKummerRadicalCoordinate p s) = WithZero.exp (-1 : ℤ) :=
  squareKummerOriginValuation_root p s η⁻¹ (Q - 2) 1

/-- The Hermitian origin is an actual rational constant-field valuation place. -/
def hermitianOriginRationalPlace : RationalConstantFieldPlaces K H :=
  squareKummerRationalFinitePlace p s η⁻¹ s 1 w
    (squareKummerOrigin_residue_surjective p s η⁻¹ (Q - 2) 1)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
