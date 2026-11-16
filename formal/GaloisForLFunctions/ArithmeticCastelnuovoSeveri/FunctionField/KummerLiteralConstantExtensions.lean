import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointConstantExtensions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.IntrinsicPlaceEquivalences

/-!
# The original and three-point equations over extended constants

Over any coefficient field, the original equation with radical degree
Q+1 has the same explicit three-point
presentation of degree (Q+1)(q-1). The coefficient, branch exponent,
and radical index agree exactly after the geometric-sum substitution.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (E : Type*) [Field E] (η : Eˣ)
local notation "Q" => p ^ (kummerSquareIndex d n + 1)
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "m" => q - 1
local notation "M" => primePowerKummerCyclicDegree p d n

/-- The original fixed-degree Kummer equation interpreted over the extended constant field. -/
abbrev PrimePowerKummerLiteralExtensionField :=
  KummerBranchField ((η⁻¹) ^ R) (q - 2) R Q

/-- The original equation and its fixed-degree three-point presentation are isomorphic over the coefficient field. -/
def primePowerKummerLiteralExtensionThreePointEquiv :
    PrimePowerKummerLiteralExtensionField p d n r E η ≃ₐ[E]
      PrimePowerThreePointExtensionField p d n E ((η⁻¹) ^ (m * R)) (m * R) := by
  have hq : 2 ≤ q := Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hb : q - 2 + 1 = m := by omega
  have hc : (((η⁻¹) ^ R) ^ (q - 2 + 1)) = (η⁻¹) ^ (m * R) := by
    rw [hb, ← pow_mul, Nat.mul_comm R m]
  have ha : R * (q - 2 + 1) = m * R := by rw [hb, Nat.mul_comm R m]
  have hi : (Q + 1) * (q - 2 + 1) - 1 = M - 1 := by
    rw [hb]
    rfl
  have e : KummerBranchField ((η⁻¹) ^ R) (q - 2) R Q ≃ₐ[E]
      KummerBranchField ((((η⁻¹) ^ R) ^ (q - 2 + 1))) 0
        (R * (q - 2 + 1)) ((Q + 1) * (q - 2 + 1) - 1) :=
    (kummerThreePointEquiv ((η⁻¹) ^ R) (q - 2) R Q).symm
  rw [hc, ha, hi] at e
  exact e

/-- Intrinsic rational-place counts agree for the original and three-point equations over the extended constants. -/
theorem primePowerKummerLiteralExtension_rationalPlaces_card_congr :
    Nat.card (RationalConstantFieldPlaces E (PrimePowerKummerLiteralExtensionField p d n r E η)) =
      Nat.card (RationalConstantFieldPlaces E
        (PrimePowerThreePointExtensionField p d n E ((η⁻¹) ^ (m * R)) (m * R))) :=
  rationalConstantFieldPlaces_card_congr (primePowerKummerLiteralExtensionThreePointEquiv p d n r E η)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

