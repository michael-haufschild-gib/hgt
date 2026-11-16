import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerLiteralConstantExtensions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionCount

/-!
# Intrinsic extension counts for the original Kummer equation

The constant-field isomorphism with the three-point presentation
transfers its complete normalized count back to the original equation.
The genus term is the dimension of the actual regular differentials
over the original stated square field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "c₀" => (kummerTraceConstant p s)⁻¹ ^ R
local notation "g" => Module.finrank K
  (globalRegularDifferentials K (SquareKummerField p s c₀ (q - 2) R))
variable (E : Type*) [Field E] [Fintype E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
local notation "η" => Units.map (RingHom.toMonoidHom (algebraMap K E)) (kummerTraceConstant p s)

/-- The original fixed equation has the exact intrinsic rational-place count over every finite extension of its constants. -/
theorem primePowerKummer_literal_extension_rationalPlaces_card :
    (Nat.card (RationalConstantFieldPlaces E
      (PrimePowerKummerLiteralExtensionField p d n r E η)) : ℂ) =
      (Fintype.card E : ℂ) + 1 +
        (-1 : ℂ) ^ (Module.finrank K E + 1) *
          (p : ℂ) ^ ((s + 1) * Module.finrank K E) * (2 * g : ℕ) := by
  rw [primePowerKummerLiteralExtension_rationalPlaces_card_congr]
  exact primePowerKummer_threePoint_extension_rationalPlaces_card p d n r E

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

