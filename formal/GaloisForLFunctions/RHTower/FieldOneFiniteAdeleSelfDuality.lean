import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleIntegralBruhatTest
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Finite-adele character self-duality

The standard finite-adele additive character is primitive: every nonzero
finite adele has a multiplicative shift which is nontrivial.  The proof
chooses a nonzero local coordinate and tests it against the inverse coordinate
times the standard local principal part.

Translated characteristic functions of the compact-open integral subgroup
then distinguish different shifted characters inside the finite Bruhat
carrier.  Consequently the finite-adele Weyl multiplier representation is
faithful.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

theorem fieldOneFiniteAdeleStandardAddChar_single_principalPart_ne_one
    (v : HeightOneSpectrum ℤ) :
    fieldOneFiniteAdeleStandardAddChar
        (fieldOneFiniteAdeleSingle v
          (fieldOneFiniteAdeleLocalPrincipalPart v)) ≠ 1 := by
  intro h
  apply fieldOneFiniteAdeleLocalUnitCharacter_principalPart_ne_zero v
  rw [← fieldOneFiniteAdeleStandardUnitAddCircleCharacter_single]
  apply AddCircle.injective_toCircle one_ne_zero
  apply Subtype.ext
  simpa only [fieldOneFiniteAdeleStandardAddChar,
    AddChar.compAddMonoidHom_apply, MonoidHom.compAddChar_apply,
    AddCircle.toCircle_zero] using h

/-- The standard finite-adele additive character is primitive under
multiplicative shifts. -/
theorem fieldOneFiniteAdeleStandardAddChar_isPrimitive :
    fieldOneFiniteAdeleStandardAddChar.IsPrimitive := by
  intro a ha hshift
  have hexists :
      ∃ v : HeightOneSpectrum ℤ, a v ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    exact h v
  obtain ⟨v, hav⟩ := hexists
  let b : FieldOneFiniteAdele :=
    fieldOneFiniteAdeleSingle v
      ((a v)⁻¹ * fieldOneFiniteAdeleLocalPrincipalPart v)
  have hab :
      a * b =
        fieldOneFiniteAdeleSingle v
          (fieldOneFiniteAdeleLocalPrincipalPart v) := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    by_cases hw : w = v
    · subst w
      change
        a v *
            fieldOneFiniteAdeleSingle v
              ((a v)⁻¹ *
                fieldOneFiniteAdeleLocalPrincipalPart v) v =
          fieldOneFiniteAdeleSingle v
            (fieldOneFiniteAdeleLocalPrincipalPart v) v
      rw [fieldOneFiniteAdeleSingle_apply_same,
        fieldOneFiniteAdeleSingle_apply_same,
        ← mul_assoc, mul_inv_cancel₀ hav, one_mul]
    · change
        a w *
            fieldOneFiniteAdeleSingle v
              ((a v)⁻¹ *
                fieldOneFiniteAdeleLocalPrincipalPart v) w =
          fieldOneFiniteAdeleSingle v
            (fieldOneFiniteAdeleLocalPrincipalPart v) w
      rw [fieldOneFiniteAdeleSingle_apply_of_ne hw,
        fieldOneFiniteAdeleSingle_apply_of_ne hw, mul_zero]
  have hvalue := DFunLike.congr_fun hshift b
  have hone :
      fieldOneFiniteAdeleStandardAddChar (a * b) = 1 := by
    simpa only [AddChar.mulShift_apply, Pi.one_apply] using hvalue
  rw [hab] at hone
  exact
    fieldOneFiniteAdeleStandardAddChar_single_principalPart_ne_one v hone

/-- Multiplicative shifts of the standard finite-adele character separate
finite adeles. -/
theorem fieldOneFiniteAdeleStandardAddChar_mulShift_injective :
    Function.Injective fieldOneFiniteAdeleStandardAddChar.mulShift :=
  AddChar.to_mulShift_inj_of_isPrimitive
    fieldOneFiniteAdeleStandardAddChar_isPrimitive

/-- Translate the canonical integral Bruhat test to be nonzero at a
prescribed finite adele. -/
def fieldOneFiniteAdeleIntegralBruhatTestAt
    (x : FieldOneFiniteAdele) :
    FieldOneFiniteBruhatSchwartz :=
  ⟨LocallyConstant.comap
      ⟨fun y => y - x, continuous_sub_right x⟩
      fieldOneFiniteAdeleIntegralBruhatTest.1,
    by
      change HasCompactSupport
        ((fieldOneFiniteAdeleIntegralBruhatTest.1 :
            FieldOneFiniteAdele → ℂ) ∘
          (Homeomorph.subRight x : FieldOneFiniteAdele → FieldOneFiniteAdele))
      exact
        fieldOneFiniteAdeleIntegralBruhatTest.2.comp_homeomorph
          (Homeomorph.subRight x)⟩

@[simp]
theorem fieldOneFiniteAdeleIntegralBruhatTestAt_self
    (x : FieldOneFiniteAdele) :
    (fieldOneFiniteAdeleIntegralBruhatTestAt x).1 x = 1 := by
  unfold fieldOneFiniteAdeleIntegralBruhatTestAt
  change fieldOneFiniteAdeleIntegralBruhatTest.1 (x - x) = 1
  rw [sub_self, fieldOneFiniteAdeleIntegralBruhatTest_zero]

/-- The standard Weyl action on finite Bruhat functions is faithful. -/
theorem fieldOneFiniteAdeleStandardWeylMultiplier_injective :
    Function.Injective fieldOneFiniteAdeleStandardWeylMultiplier := by
  intro r s heq
  apply fieldOneFiniteAdeleStandardAddChar_mulShift_injective
  apply AddChar.ext
  intro x
  have hop :=
    congrArg
      (fun T :
          FieldOneFiniteBruhatSchwartz →ₗ[ℂ]
            FieldOneFiniteBruhatSchwartz =>
        T (fieldOneFiniteAdeleIntegralBruhatTestAt x))
      heq
  have hvalue :=
    congrArg
      (fun f : FieldOneFiniteBruhatSchwartz => f.1 x)
      hop
  simpa only [fieldOneFiniteAdeleStandardWeylMultiplier,
    locallyConstantWeylMultiplier_apply,
    fieldOneFiniteAdeleStandardLocallyConstantAddChar,
    fieldOneFiniteAdeleIntegralBruhatTestAt_self,
    mul_one, AddChar.mulShift_apply] using hvalue

end

end GaloisForLFunctions.RHTower
