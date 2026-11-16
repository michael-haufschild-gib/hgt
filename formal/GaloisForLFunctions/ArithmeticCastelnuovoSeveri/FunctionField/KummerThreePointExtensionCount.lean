import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionIntrinsicCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerPuncturedExtensionCount

/-!
# Exact intrinsic point counts over finite extensions

The literal punctured Jacobi count and the three normalized boundary
fibers count all intrinsic rational places. Their branch-gcd terms
cancel, leaving the signed extension-field expression with twice the
actual regular differential dimension as its multiplicity.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "a" => (q - 1) * R
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "c₀" => (kummerTraceConstant p s)⁻¹ ^ R
local notation "g" => Module.finrank K
  (globalRegularDifferentials K (SquareKummerField p s c₀ (q - 2) R))
variable (E : Type*) [Field E] [Fintype E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
local notation "c" => primePowerKummerExtensionCoefficient p d n r E
local notation "L" => PrimePowerThreePointExtensionField p d n E c a

/-- Every finite extension has the exact intrinsic rational-place count with signed genus contribution. -/
theorem primePowerKummer_threePoint_extension_rationalPlaces_card :
    (Nat.card (RationalConstantFieldPlaces E L) : ℂ) =
      (Fintype.card E : ℂ) + 1 +
        (-1 : ℂ) ^ (Module.finrank K E + 1) *
          (p : ℂ) ^ ((s + 1) * Module.finrank K E) * (2 * g : ℕ) := by
  let η := Units.map (algebraMap K E).toMonoidHom (kummerTraceConstant p s)
  have hchart := primePowerKummerExtension_rationalPlaces_card_eq_punctured p d n r E η
  change Nat.card (RationalConstantFieldPlaces E L) =
    Nat.card (PuncturedKummerPoints (M - 1) a c) + 2 +
      (q - 1) * Nat.gcd (p ^ (s + 1) + 1) R at hchart
  have hcast : (Nat.card (RationalConstantFieldPlaces E L) : ℂ) =
      (Nat.card (PuncturedKummerPoints (M - 1) a c) : ℂ) + 2 +
        ((q - 1) * Nat.gcd (p ^ (s + 1) + 1) R : ℕ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using congrArg (fun m : ℕ => (m : ℂ)) hchart
  rw [hcast, primePowerKummer_punctured_extension_points_card]
  ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

