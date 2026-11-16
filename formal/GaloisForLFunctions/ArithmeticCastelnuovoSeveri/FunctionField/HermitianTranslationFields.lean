import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCoordinateHom
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTranslations

/-!
# Rational translations as Hermitian field automorphisms

Translating the generic Hermitian point gives explicit images of both
field generators. The new additive coordinate is transcendental:
otherwise the equation makes the new radical integral over constants,
and the inverse affine formulas make the old coordinate algebraic.
Recovering both generators proves the induced homomorphism surjective.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "η" => kummerTraceConstant p s
local notation "H" => HermitianKummerField p s
local notation "u" => hermitianKummerAdditiveCoordinate p s
local notation "v" => hermitianKummerRadicalCoordinate p s
local notation "HK" => HermitianAffinePoint p s K
local notation "φ" => algebraMap K H

/-- A rational translation applied to the actual generic Hermitian point. -/
def hermitianTranslatedGenericPoint (P : HK) : HermitianAffinePoint p s H :=
  hermitianAffineTranslate p s H P (hermitianKummerGenericPoint p s)

/-- The translated additive coordinate remains transcendental over the constants. -/
theorem hermitianTranslatedGenericPoint_transcendental (P : HK) :
    Transcendental K (hermitianTranslatedGenericPoint p s P).val.2 := by
  intro h
  let T := hermitianTranslatedGenericPoint p s P
  have hpow : IsIntegral K (T.val.1 ^ (Q + 1)) := by
    rw [← T.property]
    exact (h.isIntegral.pow Q).add h.isIntegral
  have hradical : IsIntegral K T.val.1 := IsIntegral.of_pow (Nat.succ_pos Q) hpow
  have hv : IsIntegral K v := by
    have hv' := hradical.sub (show IsIntegral K (φ P.val.1) from isIntegral_algebraMap)
    change IsIntegral K (φ P.val.1 + v - φ P.val.1) at hv'
    have he : φ P.val.1 + v - φ P.val.1 = v := by ring
    rwa [he] at hv'
  have hu := (h.isIntegral.sub
    (show IsIntegral K (φ P.val.2) from isIntegral_algebraMap)).sub
      (((show IsIntegral K (φ P.val.1) from isIntegral_algebraMap).pow Q).mul hv)
  change IsIntegral K (φ P.val.2 + u + (φ P.val.1) ^ Q * v - φ P.val.2 -
    (φ P.val.1) ^ Q * v) at hu
  have he : φ P.val.2 + u + (φ P.val.1) ^ Q * v - φ P.val.2 - (φ P.val.1) ^ Q * v = u := by ring
  rw [he] at hu
  exact hermitianKummerAdditiveCoordinate_transcendental p s hu.isAlgebraic

/-- The translated polynomial coordinate is obtained by restoring the trace constant. -/
def hermitianTranslationPolynomialCoordinate (P : HK) : H :=
  φ (η : K) * (hermitianTranslatedGenericPoint p s P).val.2

/-- The translated polynomial coordinate is a genuine rational parameter. -/
theorem hermitianTranslationPolynomialCoordinate_transcendental (P : HK) :
    Transcendental K (hermitianTranslationPolynomialCoordinate p s P) := by
  intro h
  have hi : IsIntegral K (φ (η : K)⁻¹) := isIntegral_algebraMap
  have hi' := hi.mul h.isIntegral
  have he : φ (η : K)⁻¹ * hermitianTranslationPolynomialCoordinate p s P =
      (hermitianTranslatedGenericPoint p s P).val.2 := by
    rw [hermitianTranslationPolynomialCoordinate, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ (kummerTraceConstant p s).ne_zero, map_one, one_mul]
  rw [he] at hi'
  exact hermitianTranslatedGenericPoint_transcendental p s P hi'.isAlgebraic

private theorem hermitianTranslation_branch (P : HK) :
    (hermitianTranslatedGenericPoint p s P).val.1 ^ (Q + 1) =
      φ (η⁻¹ : Kˣ) * hermitianTranslationPolynomialCoordinate p s P *
        (1 - hermitianTranslationPolynomialCoordinate p s P ^ (Q - 2 + 1)) ^ 1 := by
  let T := hermitianTranslatedGenericPoint p s P
  let w := hermitianTranslationPolynomialCoordinate p s P
  have hQ : 2 ≤ Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hw : w * (1 - w ^ (Q - 2 + 1)) = w - w ^ Q := by
    rw [show Q - 2 + 1 = Q - 1 by omega, mul_sub, mul_one, ← pow_succ',
      Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  change T.val.1 ^ (Q + 1) = φ (η : K)⁻¹ * w * (1 - w ^ (Q - 2 + 1)) ^ 1
  rw [pow_one, mul_assoc, hw]
  have hη : φ (η : K)⁻¹ * φ (η : K) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (kummerTraceConstant p s).ne_zero, map_one]
  have hηQ : (φ (η : K)) ^ Q = -φ (η : K) := by
    rw [← map_pow, kummerTraceConstant_frobenius, map_neg]
  calc
    T.val.1 ^ (Q + 1) = T.val.2 ^ Q + T.val.2 := T.property.symm
    _ = φ (η : K)⁻¹ * w - φ (η : K)⁻¹ * w ^ Q := by
      change _ = φ (η : K)⁻¹ * (φ (η : K) * T.val.2) -
        φ (η : K)⁻¹ * (φ (η : K) * T.val.2) ^ Q
      rw [mul_pow, hηQ]
      calc
        _ = (φ (η : K)⁻¹ * φ (η : K)) * (T.val.2 ^ Q + T.val.2) := by rw [hη, one_mul]
        _ = _ := by ring
    _ = _ := (mul_sub _ _ _).symm

/-- Rational Hermitian translations induce actual constant-field homomorphisms. -/
def hermitianTranslationFieldHom (P : HK) : H →ₐ[K] H :=
  kummerBranchFieldHomOfCoordinates η⁻¹ (Q - 2) 1 Q
    (hermitianTranslationPolynomialCoordinate p s P)
    (hermitianTranslatedGenericPoint p s P).val.1
    (hermitianTranslationPolynomialCoordinate_transcendental p s P)
    (hermitianTranslation_branch p s P)

/-- The polynomial coordinate has its prescribed translated value. -/
theorem hermitianTranslationFieldHom_coordinate (P : HK) :
    hermitianTranslationFieldHom p s P (algebraMap K[X] H X) =
      hermitianTranslationPolynomialCoordinate p s P :=
  kummerBranchFieldHomOfCoordinates_coordinate _ _ _ _ _ _ _ _

/-- The multiplicative coordinate is translated by the first rational parameter. -/
theorem hermitianTranslationFieldHom_radical (P : HK) :
    hermitianTranslationFieldHom p s P v = φ P.val.1 + v :=
  kummerBranchFieldHomOfCoordinates_root _ _ _ _ _ _ _ _

/-- The additive coordinate follows the exact Hermitian translation formula. -/
theorem hermitianTranslationFieldHom_additive (P : HK) :
    hermitianTranslationFieldHom p s P u = φ P.val.2 + u + (φ P.val.1) ^ Q * v := by
  rw [hermitianKummerAdditiveCoordinate, map_mul, AlgHom.commutes,
    hermitianTranslationFieldHom_coordinate, hermitianTranslationPolynomialCoordinate,
    ← mul_assoc, ← map_mul, inv_mul_cancel₀ (kummerTraceConstant p s).ne_zero, map_one, one_mul]
  rfl

/-- Both original generators lie in the image of the translation homomorphism. -/
theorem hermitianTranslationFieldHom_surjective (P : HK) :
    Function.Surjective (hermitianTranslationFieldHom p s P) := by
  let f := hermitianTranslationFieldHom p s P
  have hv : v ∈ f.fieldRange := by
    have h := f.fieldRange.sub_mem
      (show f v ∈ f.fieldRange from ⟨v, rfl⟩) (f.fieldRange.algebraMap_mem P.val.1)
    change hermitianTranslationFieldHom p s P v - φ P.val.1 ∈ f.fieldRange at h
    rw [hermitianTranslationFieldHom_radical] at h
    have he : φ P.val.1 + v - φ P.val.1 = v := by ring
    rwa [he] at h
  have hu : u ∈ f.fieldRange := by
    have h := f.fieldRange.sub_mem
      (f.fieldRange.sub_mem (show f u ∈ f.fieldRange from ⟨u, rfl⟩)
        (f.fieldRange.algebraMap_mem P.val.2))
      (f.fieldRange.mul_mem (pow_mem (f.fieldRange.algebraMap_mem P.val.1) Q) hv)
    change hermitianTranslationFieldHom p s P u - φ P.val.2 - (φ P.val.1) ^ Q * v ∈ f.fieldRange at h
    rw [hermitianTranslationFieldHom_additive] at h
    have he : φ P.val.2 + u + (φ P.val.1) ^ Q * v - φ P.val.2 - (φ P.val.1) ^ Q * v = u := by ring
    rwa [he] at h
  have hy : algebraMap K[X] H X ∈ f.fieldRange := by
    rw [← hermitianKummerAdditiveCoordinate_recover p s]
    exact f.fieldRange.mul_mem (f.fieldRange.algebraMap_mem (η : K)) hu
  have htop := kummerBranchField_eq_top_of_coordinate_root_mem η⁻¹ (Q - 2) 1 Q f.fieldRange hy hv
  intro x
  have hx : x ∈ f.fieldRange := by rw [htop]; trivial
  exact hx

/-- Every rational Hermitian translation is an automorphism of the actual function field. -/
def hermitianTranslationFieldAut (P : HK) : H ≃ₐ[K] H :=
  AlgEquiv.ofBijective (hermitianTranslationFieldHom p s P)
    ⟨(hermitianTranslationFieldHom p s P).injective, hermitianTranslationFieldHom_surjective p s P⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
