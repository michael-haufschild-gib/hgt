import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularDifferentialDimension
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntrinsicRationalCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerConstantField

/-!
# Intrinsic invariants of the Hermitian function field

The Hermitian source has genus `Q(Q-1)/2`, measured by its actual global
regular differential space, and `Q³+1` intrinsic rational places. Its
stated square field is its full constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime]

/-- The regular differential dimension of the actual Hermitian function field is `Q(Q-1)/2`. -/
theorem hermitianKummer_regularDifferential_finrank (s : ℕ) :
    Module.finrank (SquareConstantField p s)
      (globalRegularDifferentials (SquareConstantField p s) (HermitianKummerField p s)) =
        p ^ (s + 1) * (p ^ (s + 1) - 1) / 2 := by
  have h := squareKummer_regularDifferential_finrank p s (kummerTraceConstant p s)⁻¹ s 1
  apply h.trans
  have hR : kummerExponent (p ^ (s + 1)) 1 = 1 := rfl
  rw [hR, Nat.gcd_one_right, Nat.add_sub_cancel,
    Nat.mul_comm (p ^ (s + 1) - 1) (p ^ (s + 1))]

/-- The actual Hermitian function field has exactly `Q³+1` rational valuation places. -/
theorem hermitianKummerRationalPlaces_card (s : ℕ) :
    Nat.card (RationalConstantFieldPlaces (SquareConstantField p s) (HermitianKummerField p s)) =
      (p ^ (s + 1)) ^ 3 + 1 := by
  let Q := p ^ (s + 1)
  have he : Nat.card (RationalConstantFieldPlaces (SquareConstantField p s) (HermitianKummerField p s)) =
      Nat.card (NormalizedKummerRationalPlaces p s 0 0) :=
    (congrArg (fun c : (SquareConstantField p s)ˣ =>
      Nat.card (RationalConstantFieldPlaces (SquareConstantField p s)
        (SquareKummerField p s c (Q - 2) 1)))
      (pow_one (kummerTraceConstant p s)⁻¹)).symm
  rw [he, normalizedKummerRationalPlaces_card]
  change Q ^ 2 + 1 + (Q - 1) * Q * (Q + 1 - Nat.gcd (Q + 1) (kummerExponent Q 1)) = Q ^ 3 + 1
  have hR : kummerExponent Q 1 = 1 := rfl
  rw [hR, Nat.gcd_one_right, Nat.add_sub_cancel]
  have hQ : Q - 1 + 1 = Q := Nat.sub_add_cancel
    (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
  calc
    Q ^ 2 + 1 + (Q - 1) * Q * Q = (Q - 1 + 1) * Q ^ 2 + 1 := by ring
    _ = Q ^ 3 + 1 := by rw [hQ]; ring

/-- The square field of definition is the full constant field of the Hermitian source. -/
theorem hermitianKummer_integralConstants (s : ℕ) :
    integralClosure (SquareConstantField p s) (HermitianKummerField p s) = ⊥ :=
  squareKummer_integralConstants p s (kummerTraceConstant p s)⁻¹ (p ^ (s + 1) - 2) 1


end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
