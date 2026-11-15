import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTraceConstants

/-!
# Characteristic of the actual Kummer function field

The constant-field embedding is injective, so the constructed radical
field has the same characteristic as its finite constants.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The actual radical function field retains the characteristic of its constants. -/
instance squareKummerField_charP (p : ℕ) [Fact p.Prime] (s : ℕ)
    (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    CharP (SquareKummerField p s c b R) p :=
  charP_of_injective_algebraMap
    (algebraMap (SquareConstantField p s) (SquareKummerField p s c b R)).injective p

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
