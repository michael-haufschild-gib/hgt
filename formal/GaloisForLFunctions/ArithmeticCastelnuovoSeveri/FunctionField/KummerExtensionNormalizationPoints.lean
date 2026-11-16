import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalizationPoints
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerExtensionCountSequence

/-!
# Extension counts from one fixed normalization ring

Use the three-point affine normalization over the original square field.
Every finite extension point is an algebra map from this fixed ring, apart
from the unique rational place at infinity. Thus the intrinsic counts and
their zeta ghost can be recovered from the closed primes of one ring.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "a" => (q - 1) * R
local notation "η" => kummerTraceConstant p s
local notation "c₀" => η⁻¹ ^ a
local notation "M" => primePowerKummerCyclicDegree p d n

/-- The actual three-point affine normalization over the original square constant field. -/
abbrev PrimePowerKummerThreePointAffineNormalization :=
  PrimePowerThreePointExtensionNormalization p d n K c₀ a

local notation "A" => PrimePowerKummerThreePointAffineNormalization p d n r
section Extension

variable (E : Type*) [Field E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
local notation "ηE" => Units.map (RingHom.toMonoidHom (algebraMap K E)) η
local notation "LE" => PrimePowerThreePointExtensionField p d n E (ηE⁻¹ ^ a) a
local notation "BE" => PrimePowerThreePointExtensionNormalization p d n E (ηE⁻¹ ^ a) a

local instance extensionPointsPolynomialTorsionFree : Module.IsTorsionFree E[X] LE :=
  kummerBranchField_torsionFree (ηE⁻¹ ^ a) 0 a (M - 1)

local instance extensionPointsNormalizationTorsionFree : Module.IsTorsionFree E[X] BE :=
  inferInstanceAs (Module.IsTorsionFree E[X] (integralClosure E[X] LE))

variable [Finite E]

/-- The fixed affine normalization has finitely many algebra points over every finite constant extension. -/
instance primePowerKummerThreePointAffineNormalization_algHom_finite : Finite (A →ₐ[K] E) := by
  have e := kummerNormalizationExtensionPrimeEquiv K E c₀ 0 a (M - 1)
  have hc : Units.map (RingHom.toMonoidHom (algebraMap K E)) c₀ = ηE⁻¹ ^ a := by
    rw [map_pow, map_inv]
  rw [hc] at e
  exact Finite.of_equiv (RationalPolynomialPrimes E BE) e

/-- Every intrinsic extension point is a point of the fixed affine normalization or the unique point at infinity. -/
theorem primePowerKummer_literal_extension_rationalPlaces_card_algHom :
    Nat.card (RationalConstantFieldPlaces E
      (PrimePowerKummerLiteralExtensionField p d n r E ηE)) =
      Nat.card (A →ₐ[K] E) + 1 := by
  have h := kummerNormalizationExtensionPrimes_card K E c₀ 0 a (M - 1)
  have hc : Units.map (RingHom.toMonoidHom (algebraMap K E)) c₀ = ηE⁻¹ ^ a := by
    rw [map_pow, map_inv]
  rw [hc] at h
  rw [primePowerKummerLiteralExtension_rationalPlaces_card_congr,
    primePowerKummerExtension_rationalPlaces_card_eq_finite]
  exact congrArg (fun m : ℕ => m + 1) h

end Extension

/-- The actual extension-count sequence counts maps from the same affine normalization in every positive degree. -/
theorem primePowerKummerExtensionPointCount_eq_algHom (e : ℕ) [NeZero e] :
    primePowerKummerExtensionPointCount p d n r e =
      Nat.card (A →ₐ[K] FiniteField.Extension K p e) + 1 := by
  rw [primePowerKummerExtensionPointCount, dif_neg (NeZero.ne e)]
  exact primePowerKummer_literal_extension_rationalPlaces_card_algHom p d n r
    (FiniteField.Extension K p e)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
