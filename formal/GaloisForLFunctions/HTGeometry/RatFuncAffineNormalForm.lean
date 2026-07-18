import GaloisForLFunctions.HTGeometry.RatFuncScaleFixedField
import GaloisForLFunctions.HTGeometry.RatFuncTranslationFixedField

/-!
# Affine normal forms on a rational coordinate

This module closes the affine part of the projective cyclic-normal-form argument.  An affine
automorphism `X ↦ uX + b` is either the identity, conjugate to its scalar linear part when
`u ≠ 1`, or conjugate to unit translation when `u = 1` and `b ≠ 0`.

The statements are literal equalities of coefficient-fixing automorphisms of `K(X)`.  They do
not assume a normal-form or fixed-field conclusion as input.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

/-- Two coefficient-fixing endomorphisms of `K(X)` agree when they agree on `X`. -/
private theorem ratFuncAlgHom_ext_X
    {f g : RatFunc K →ₐ[K] RatFunc K}
    (hX : f RatFunc.X = g RatFunc.X) :
    f = g := by
  apply AlgHom.ext
  intro z
  have hring : f.toRingHom = g.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := K[X])
    intro p
    have hpoly :
        f.toRingHom.comp (algebraMap K[X] (RatFunc K)) =
          g.toRingHom.comp (algebraMap K[X] (RatFunc K)) := by
      apply Polynomial.ringHom_ext
      · intro c
        change f (algebraMap K (RatFunc K) c) =
          g (algebraMap K (RatFunc K) c)
        rw [f.commutes, g.commutes]
      · simpa [RatFunc.algebraMap_X] using hX
    exact DFunLike.congr_fun hpoly p
  exact DFunLike.congr_fun hring z

/-- The affine automorphism `X ↦ uX + b` of `K(X)`. -/
def ratFuncAffineEquiv (u : Kˣ) (b : K) : RatFunc K ≃ₐ[K] RatFunc K :=
  ratFuncTranslationEquiv b * ratFuncUnitScaleEquiv u

@[simp]
theorem ratFuncAffineEquiv_X (u : Kˣ) (b : K) :
    ratFuncAffineEquiv u b RatFunc.X =
      algebraMap K (RatFunc K) (u : K) * RatFunc.X +
        algebraMap K (RatFunc K) b := by
  simp [ratFuncAffineEquiv]

@[simp]
theorem ratFuncAffineEquiv_one_zero :
    ratFuncAffineEquiv (1 : Kˣ) 0 = AlgEquiv.refl := by
  simp [ratFuncAffineEquiv]

/-- If the linear coefficient is not one, translation by the unique affine fixed point conjugates
the map to pure scaling. -/
theorem ratFuncAffineEquiv_translation_conj_eq_scale
    (u : Kˣ) (b : K) (hu : (u : K) ≠ 1) :
    let r : K := b / (1 - (u : K))
    ratFuncTranslationEquiv (-r) * ratFuncAffineEquiv u b *
        ratFuncTranslationEquiv r =
      ratFuncUnitScaleEquiv u := by
  dsimp only
  apply AlgEquiv.ext
  intro z
  have hhom :
      (ratFuncTranslationEquiv (-b / (1 - (u : K))) *
          ratFuncAffineEquiv u b *
            ratFuncTranslationEquiv (b / (1 - (u : K)))).toAlgHom =
        (ratFuncUnitScaleEquiv u).toAlgHom := by
    apply ratFuncAlgHom_ext_X
    simp only [AlgEquiv.mul_apply, ratFuncTranslationEquiv_X,
      ratFuncAffineEquiv_X, ratFuncUnitScaleEquiv_X, map_add, map_mul,
      AlgEquiv.commutes]
    push_cast
    field_simp [sub_ne_zero.mpr hu.symm]
    ring
  exact DFunLike.congr_fun hhom z

/-- A nonzero translation is conjugate to unit translation by rescaling its step. -/
theorem ratFuncTranslationEquiv_scale_conj_eq_one
    (b : K) (hb : b ≠ 0) :
    let v : Kˣ := Units.mk0 b hb
    ratFuncUnitScaleEquiv v⁻¹ * ratFuncTranslationEquiv b *
        ratFuncUnitScaleEquiv v =
      ratFuncTranslationEquiv 1 := by
  dsimp only
  apply AlgEquiv.ext
  intro z
  have hhom :
      (ratFuncUnitScaleEquiv (Units.mk0 b hb)⁻¹ *
          ratFuncTranslationEquiv b *
            ratFuncUnitScaleEquiv (Units.mk0 b hb)).toAlgHom =
        (ratFuncTranslationEquiv (1 : K)).toAlgHom := by
    apply ratFuncAlgHom_ext_X
    simp only [AlgEquiv.mul_apply, ratFuncUnitScaleEquiv_X,
      ratFuncTranslationEquiv_X, map_add, map_mul, AlgEquiv.commutes]
    push_cast
    field_simp [hb]
  exact DFunLike.congr_fun hhom z

/-- A nonidentity affine automorphism has exactly one of the two cyclic normal forms: scaling or
unit translation.  The conjugating coordinate change is given explicitly in each branch. -/
theorem ratFuncAffineEquiv_normalForm
    (u : Kˣ) (b : K)
    (hne : ratFuncAffineEquiv u b ≠ AlgEquiv.refl) :
    (∃ r : K,
        ratFuncTranslationEquiv (-r) * ratFuncAffineEquiv u b *
            ratFuncTranslationEquiv r =
          ratFuncUnitScaleEquiv u) ∨
      (∃ v : Kˣ,
        ratFuncUnitScaleEquiv v⁻¹ * ratFuncAffineEquiv u b *
            ratFuncUnitScaleEquiv v =
          ratFuncTranslationEquiv 1) := by
  by_cases hu : (u : K) = 1
  · have hu' : u = 1 := Units.ext hu
    subst u
    have hb : b ≠ 0 := by
      intro hb
      subst b
      exact hne ratFuncAffineEquiv_one_zero
    right
    let v : Kˣ := Units.mk0 b hb
    refine ⟨v, ?_⟩
    simpa [ratFuncAffineEquiv, v] using
      ratFuncTranslationEquiv_scale_conj_eq_one b hb
  · left
    let r : K := b / (1 - (u : K))
    refine ⟨r, ?_⟩
    simpa [r] using ratFuncAffineEquiv_translation_conj_eq_scale u b hu

end

end GaloisForLFunctions.HTGeometry
