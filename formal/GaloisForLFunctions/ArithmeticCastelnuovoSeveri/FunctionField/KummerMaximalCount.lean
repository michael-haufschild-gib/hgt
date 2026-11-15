import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularDifferentialDimension
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntrinsicRationalCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerConstantField
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerTraceChoicePointCount

/-!
# The maximal rational-place identity

The intrinsic rational-place count and the dimension of actual global
regular Kähler differentials satisfy `#C = Q²+1+2Qg`. Thus the normalized
trace-constant family attains the Hasse–Weil upper-bound expression over
its stated square constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)

/-- Actual global regular differentials of the normalized trace-constant function field. -/
abbrev NormalizedKummerRegularDifferentials :=
  globalRegularDifferentials (SquareConstantField p (kummerSquareIndex d n))
    (NormalizedKummerField p (kummerSquareIndex d n) d r)

/-- Twice the normalized field's regular differential dimension is its explicit ramification defect. -/
theorem normalizedKummer_regularDifferential_finrank_twice :
    2 * Module.finrank (SquareConstantField p (kummerSquareIndex d n))
      (NormalizedKummerRegularDifferentials p d n r) =
      (p ^ (d + 1) - 1) *
        (p ^ (kummerSquareIndex d n + 1) + 1 -
          Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
            (kummerExponent (p ^ (d + 1)) (r + 1))) :=
  squareKummer_regularDifferential_finrank_twice p (kummerSquareIndex d n)
    ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
    d (r + 1)

/-- The normalized field's genus is the dimension of its actual global regular differential space. -/
theorem normalizedKummer_regularDifferential_finrank :
    Module.finrank (SquareConstantField p (kummerSquareIndex d n))
      (NormalizedKummerRegularDifferentials p d n r) =
      ((p ^ (d + 1) - 1) *
        (p ^ (kummerSquareIndex d n + 1) + 1 -
          Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
            (kummerExponent (p ^ (d + 1)) (r + 1)))) / 2 :=
  squareKummer_regularDifferential_finrank p (kummerSquareIndex d n)
    ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
    d (r + 1)

/-- The actual rational places and actual regular differentials attain the maximal Hasse–Weil expression. -/
theorem normalizedKummerRationalPlaces_card_maximal :
    Nat.card (NormalizedKummerRationalPlaces p d n r) =
      (p ^ (kummerSquareIndex d n + 1)) ^ 2 + 1 +
        2 * p ^ (kummerSquareIndex d n + 1) *
          Module.finrank (SquareConstantField p (kummerSquareIndex d n))
            (NormalizedKummerRegularDifferentials p d n r) := by
  rw [normalizedKummerRationalPlaces_card]
  have h := normalizedKummer_regularDifferential_finrank_twice p d n r
  let Q := p ^ (kummerSquareIndex d n + 1)
  let m := p ^ (d + 1) - 1
  let D := p ^ (kummerSquareIndex d n + 1) + 1 -
    Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1) (kummerExponent (p ^ (d + 1)) (r + 1))
  let g := Module.finrank (SquareConstantField p (kummerSquareIndex d n))
    (NormalizedKummerRegularDifferentials p d n r)
  change 2 * g = m * D at h
  change Q ^ 2 + 1 + m * Q * D = Q ^ 2 + 1 + 2 * Q * g
  calc
    Q ^ 2 + 1 + m * Q * D = Q ^ 2 + 1 + Q * (m * D) := by ring
    _ = Q ^ 2 + 1 + 2 * Q * g := by rw [← h]; ring

/-- The specified square field is the full constant field, and the intrinsic place count attains the maximal expression. -/
theorem normalizedKummer_maximal :
    integralClosure (SquareConstantField p (kummerSquareIndex d n))
      (NormalizedKummerField p (kummerSquareIndex d n) d r) = ⊥ ∧
    Nat.card (NormalizedKummerRationalPlaces p d n r) =
      (p ^ (kummerSquareIndex d n + 1)) ^ 2 + 1 +
        2 * p ^ (kummerSquareIndex d n + 1) *
          Module.finrank (SquareConstantField p (kummerSquareIndex d n))
            (NormalizedKummerRegularDifferentials p d n r) :=
  ⟨squareKummer_integralConstants p (kummerSquareIndex d n)
    ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
    (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1)),
    normalizedKummerRationalPlaces_card_maximal p d n r⟩

/-- Every nonzero trace-zero coefficient gives the full stated constant field and the maximal intrinsic place count. -/
theorem traceChoiceKummer_maximal (η : KummerTraceChoices p (kummerSquareIndex d n)) :
    integralClosure (SquareConstantField p (kummerSquareIndex d n))
      (SquareKummerField p (kummerSquareIndex d n)
        (η.val⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
        (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))) = ⊥ ∧
    Nat.card (TraceChoiceKummerRationalPlaces p d n r η) =
      (p ^ (kummerSquareIndex d n + 1)) ^ 2 + 1 +
        2 * p ^ (kummerSquareIndex d n + 1) *
          Module.finrank (SquareConstantField p (kummerSquareIndex d n))
            (globalRegularDifferentials (SquareConstantField p (kummerSquareIndex d n))
              (SquareKummerField p (kummerSquareIndex d n)
                (η.val⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
                (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1)))) := by
  constructor
  · exact squareKummer_integralConstants p (kummerSquareIndex d n) _ _ _
  · rw [traceChoiceKummerRationalPlaces_card]
    have h := squareKummer_regularDifferential_finrank_twice p (kummerSquareIndex d n)
      (η.val⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1)) d (r + 1)
    let Q := p ^ (kummerSquareIndex d n + 1)
    let m := p ^ (d + 1) - 1
    let D := Q + 1 - Nat.gcd (Q + 1) (kummerExponent (p ^ (d + 1)) (r + 1))
    let g := Module.finrank (SquareConstantField p (kummerSquareIndex d n))
      (globalRegularDifferentials (SquareConstantField p (kummerSquareIndex d n))
        (SquareKummerField p (kummerSquareIndex d n)
          (η.val⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
          (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))))
    change 2 * g = m * D at h
    change Q ^ 2 + 1 + m * Q * D = Q ^ 2 + 1 + 2 * Q * g
    calc
      Q ^ 2 + 1 + m * Q * D = Q ^ 2 + 1 + Q * (m * D) := by ring
      _ = Q ^ 2 + 1 + 2 * Q * g := by rw [← h]; ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
