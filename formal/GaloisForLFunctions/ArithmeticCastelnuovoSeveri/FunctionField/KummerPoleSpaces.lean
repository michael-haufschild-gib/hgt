import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationConstantBounds
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPlaceClassification

/-!
# Functions with a bounded pole at Kummer infinity

The affine normalization consists of functions regular at every finite
place. Intersecting it with an infinity valuation ball gives the actual
space of functions whose sole allowed pole is at infinity, with bounded order.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- Functions regular away from infinity, with pole order at infinity at most `m`. -/
def squareKummerPoleSpace (m : ℕ) :
    Submodule (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) :=
  ((SquareKummerNormalization p s c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r)).toSubmodule.restrictScalars (SquareConstantField p s)) ⊓
      valuationConstantBound (squareKummerInfinityValuation p s c d r)
        (squareKummerInfinityConstantPlace p s c d r).property.2 (WithZero.exp (m : ℤ))

/-- The one-point pole space uses the actual normalization and normalized infinity valuation. -/
theorem mem_squareKummerPoleSpace_iff (m : ℕ)
    (x : SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) :
    x ∈ squareKummerPoleSpace p s c d r m ↔
      IsIntegral (SquareConstantField p s)[X] x ∧
        squareKummerInfinityValuation p s c d r x ≤ WithZero.exp (m : ℤ) := Iff.rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
