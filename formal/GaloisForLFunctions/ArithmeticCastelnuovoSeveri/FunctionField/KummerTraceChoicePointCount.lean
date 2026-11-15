import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerTraceChoice
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.IntrinsicPlaceEquivalences
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntrinsicRationalCount

/-!
# Rational places for every trace-zero coefficient

Radical rescaling identifies every nonzero trace-zero coefficient choice
with the canonical one over the same constant field. Transport of actual
rational valuation places therefore gives the exact count for all choices.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)

/-- Intrinsic rational places with an arbitrary nonzero trace-zero coefficient choice. -/
abbrev TraceChoiceKummerRationalPlaces (η : KummerTraceChoices p (kummerSquareIndex d n)) :=
  RationalConstantFieldPlaces (SquareConstantField p (kummerSquareIndex d n))
    (SquareKummerField p (kummerSquareIndex d n)
      (η.val⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1)))

/-- Every allowed trace-zero choice has the same intrinsic rational-place count as the canonical choice. -/
theorem traceChoiceKummerRationalPlaces_card_eq_normalized
    (η : KummerTraceChoices p (kummerSquareIndex d n)) :
    Nat.card (TraceChoiceKummerRationalPlaces p d n r η) =
      Nat.card (NormalizedKummerRationalPlaces p d n r) :=
  (rationalConstantFieldPlaces_card_congr
    (kummerTraceChoiceEquiv p (kummerSquareIndex d n) η
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1)))).symm

/-- The exact intrinsic rational-place count holds for every nonzero trace-zero coefficient. -/
theorem traceChoiceKummerRationalPlaces_card
    (η : KummerTraceChoices p (kummerSquareIndex d n)) :
    Nat.card (TraceChoiceKummerRationalPlaces p d n r η) =
      (p ^ (kummerSquareIndex d n + 1)) ^ 2 + 1 +
        (p ^ (d + 1) - 1) * p ^ (kummerSquareIndex d n + 1) *
          (p ^ (kummerSquareIndex d n + 1) + 1 -
            Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
              (kummerExponent (p ^ (d + 1)) (r + 1))) := by
  rw [traceChoiceKummerRationalPlaces_card_eq_normalized, normalizedKummerRationalPlaces_card]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
