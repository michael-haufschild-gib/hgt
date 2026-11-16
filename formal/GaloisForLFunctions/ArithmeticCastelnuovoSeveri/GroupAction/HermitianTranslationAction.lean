import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTranslationFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldHomExt
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GroupAction.HermitianTranslationGroup

/-!
# A faithful p-group of Hermitian function-field automorphisms

Substitution reverses the product of translation parameters. Taking
inverse field automorphisms therefore gives a faithful group
homomorphism. Its image is an actual subgroup of order Q³ in the
constant-field automorphism group of the Hermitian function field.
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
local notation "f" => hermitianTranslationFieldHom p s

local instance hermitianTranslationActionCharP : CharP H p :=
  charP_of_injective_algebraMap (algebraMap K H).injective p

/-- The additive and multiplicative Hermitian coordinates determine every field homomorphism. -/
theorem hermitianKummerAlgHom_ext {E : Type*} [Field E] [Algebra K E]
    (F G : H →ₐ[K] E) (hu : F u = G u) (hv : F v = G v) : F = G := by
  apply kummerBranchField_algHom_ext η⁻¹ (Q - 2) 1 Q F G
  · rw [← hermitianKummerAdditiveCoordinate_recover p s, map_mul, map_mul,
      F.commutes, G.commutes, hu]
  · exact hv

/-- Substitution in the two field generators reverses composition of the translation parameters. -/
theorem hermitianTranslationFieldHom_comp (P U : HK) :
    (f P).comp (f U) = f (U * P) := by
  apply hermitianKummerAlgHom_ext p s
  · change f P (f U u) = f (U * P) u
    rw [hermitianTranslationFieldHom_additive, map_add, map_add, map_mul, map_pow,
      AlgHom.commutes, AlgHom.commutes, hermitianTranslationFieldHom_additive,
      hermitianTranslationFieldHom_radical, hermitianTranslationFieldHom_additive]
    change φ U.val.2 + (φ P.val.2 + u + (φ P.val.1) ^ Q * v) +
      (φ U.val.1) ^ Q * (φ P.val.1 + v) =
        φ (U.val.2 + P.val.2 + U.val.1 ^ Q * P.val.1) + u +
          (φ (U.val.1 + P.val.1)) ^ Q * v
    simp only [map_add, map_mul, map_pow, add_pow_char_pow]
    ring
  · change f P (f U v) = f (U * P) v
    rw [hermitianTranslationFieldHom_radical, map_add, AlgHom.commutes,
      hermitianTranslationFieldHom_radical, hermitianTranslationFieldHom_radical]
    change φ U.val.1 + (φ P.val.1 + v) = φ (U.val.1 + P.val.1) + v
    rw [map_add, add_assoc]

/-- Translation by the origin induces the identity field automorphism. -/
theorem hermitianTranslationFieldAut_one : hermitianTranslationFieldAut p s (1 : HK) = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply hermitianKummerAlgHom_ext p s
  · change f (1 : HK) u = u
    rw [hermitianTranslationFieldHom_additive]
    change φ 0 + u + (φ 0) ^ Q * v = u
    simp only [map_zero, zero_add, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
      zero_mul, add_zero]
  · change f (1 : HK) v = v
    rw [hermitianTranslationFieldHom_radical]
    change φ 0 + v = v
    rw [map_zero, zero_add]

/-- The field automorphisms multiply in the reverse order to the translation parameters. -/
theorem hermitianTranslationFieldAut_mul (P U : HK) :
    hermitianTranslationFieldAut p s (P * U) =
      hermitianTranslationFieldAut p s U * hermitianTranslationFieldAut p s P := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact (hermitianTranslationFieldHom_comp p s U P).symm

/-- Evaluating the two generators recovers both rational translation parameters. -/
theorem hermitianTranslationFieldAut_injective :
    Function.Injective (hermitianTranslationFieldAut p s) := by
  intro P U h
  have hv := congrArg (fun σ : H ≃ₐ[K] H => σ v) h
  change f P v = f U v at hv
  rw [hermitianTranslationFieldHom_radical, hermitianTranslationFieldHom_radical] at hv
  have ha : P.val.1 = U.val.1 := (algebraMap K H).injective (add_right_cancel hv)
  have hu := congrArg (fun σ : H ≃ₐ[K] H => σ u) h
  change f P u = f U u at hu
  rw [hermitianTranslationFieldHom_additive, hermitianTranslationFieldHom_additive, ha] at hu
  have hb : P.val.2 = U.val.2 := (algebraMap K H).injective (add_right_cancel (add_right_cancel hu))
  exact Subtype.ext (Prod.ext ha hb)

/-- Inverse substitution gives a genuine homomorphism into the actual field automorphism group. -/
def hermitianTranslationFieldAutHom : HK →* (H ≃ₐ[K] H) where
  toFun P := (hermitianTranslationFieldAut p s P)⁻¹
  map_one' := by rw [hermitianTranslationFieldAut_one, inv_one]
  map_mul' P U := by rw [hermitianTranslationFieldAut_mul, mul_inv_rev]

/-- The rational translation group acts faithfully on the Hermitian function field. -/
theorem hermitianTranslationFieldAutHom_injective :
    Function.Injective (hermitianTranslationFieldAutHom p s) := by
  intro P U h
  exact hermitianTranslationFieldAut_injective p s (inv_injective h)

/-- The constructed subgroup of actual Hermitian field automorphisms has order Q³. -/
theorem hermitianTranslationFieldAutHom_range_card :
    Nat.card (hermitianTranslationFieldAutHom p s).range = Q ^ 3 := by
  change Nat.card (Set.range (hermitianTranslationFieldAutHom p s)) = Q ^ 3
  rw [← Nat.card_congr (Equiv.ofInjective _ (hermitianTranslationFieldAutHom_injective p s))]
  exact hermitianTranslationGroup_card p s

/-- The image subgroup is a p-group inside the actual constant-field automorphism group. -/
theorem hermitianTranslationFieldAutHom_range_isPGroup :
    IsPGroup p (hermitianTranslationFieldAutHom p s).range := by
  intro x
  obtain ⟨P, hP⟩ := x.property
  obtain ⟨k, hk⟩ := hermitianTranslationGroup_isPGroup p s P
  refine ⟨k, Subtype.ext ?_⟩
  change x.val ^ (p ^ k) = 1
  rw [← hP, ← map_pow, hk, map_one]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
