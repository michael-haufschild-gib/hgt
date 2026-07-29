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

/-- Two coefficient-fixing automorphisms of `K(X)` agree when they agree on `X`. -/
private theorem ratFuncAlgEquiv_ext_X
    {f g : RatFunc K ≃ₐ[K] RatFunc K}
    (hX : f RatFunc.X = g RatFunc.X) :
    f = g := by
  have hhom : f.toAlgHom = g.toAlgHom :=
    ratFuncAlgHom_ext_X hX
  apply AlgEquiv.ext
  intro z
  exact DFunLike.congr_fun hhom z

/-- The affine automorphism `X ↦ uX + b` of `K(X)`. -/
def ratFuncAffineEquiv (u : Kˣ) (b : K) : RatFunc K ≃ₐ[K] RatFunc K :=
  ratFuncUnitScaleEquiv u * ratFuncTranslationEquiv b

@[simp]
theorem ratFuncAffineEquiv_X (u : Kˣ) (b : K) :
    ratFuncAffineEquiv u b RatFunc.X =
      algebraMap K (RatFunc K) (u : K) * RatFunc.X +
        algebraMap K (RatFunc K) b := by
  change ratFuncUnitScaleEquiv u
      (ratFuncTranslationEquiv b RatFunc.X) = _
  rw [ratFuncTranslationEquiv_X, map_add,
    ratFuncUnitScaleEquiv_X, AlgEquiv.commutes]

@[simp]
theorem ratFuncAffineEquiv_one_zero :
    ratFuncAffineEquiv (1 : Kˣ) 0 = AlgEquiv.refl := by
  rw [ratFuncAffineEquiv, ratFuncUnitScaleEquiv_one,
    ratFuncTranslationEquiv_zero]
  rfl

/-- If the linear coefficient is not one, translation by the unique affine fixed point conjugates
the map to pure scaling. -/
theorem ratFuncAffineEquiv_translation_conj_eq_scale
    (u : Kˣ) (b : K) (hu : (u : K) ≠ 1) :
    let r : K := b / ((u : K) - 1)
    ratFuncTranslationEquiv (-r) * ratFuncAffineEquiv u b *
        ratFuncTranslationEquiv r =
      ratFuncUnitScaleEquiv u := by
  dsimp only
  apply ratFuncAlgEquiv_ext_X
  change ratFuncTranslationEquiv (-(b / ((u : K) - 1)))
      (ratFuncAffineEquiv u b
        (ratFuncTranslationEquiv (b / ((u : K) - 1)) RatFunc.X)) =
    ratFuncUnitScaleEquiv u RatFunc.X
  rw [ratFuncTranslationEquiv_X, map_add, ratFuncAffineEquiv_X,
    AlgEquiv.commutes, map_add, map_add, map_mul, AlgEquiv.commutes,
    ratFuncTranslationEquiv_X, AlgEquiv.commutes, AlgEquiv.commutes,
    ratFuncUnitScaleEquiv_X]
  have hr :
      (u : K) * (b / ((u : K) - 1)) =
        b / ((u : K) - 1) + b := by
    field_simp [sub_ne_zero.mpr hu]
    ring
  have hrmap := congrArg (algebraMap K (RatFunc K)) hr
  simp only [map_mul, map_add] at hrmap
  rw [map_neg, mul_add, mul_neg, hrmap]
  ring

/-- A nonzero translation is conjugate to unit translation by rescaling its step. -/
theorem ratFuncTranslationEquiv_scale_conj_eq_one
    (b : K) (hb : b ≠ 0) :
    let v : Kˣ := Units.mk0 b hb
    ratFuncUnitScaleEquiv v * ratFuncTranslationEquiv b *
        ratFuncUnitScaleEquiv v⁻¹ =
      ratFuncTranslationEquiv 1 := by
  dsimp only
  apply ratFuncAlgEquiv_ext_X
  change ratFuncUnitScaleEquiv (Units.mk0 b hb)
      (ratFuncTranslationEquiv b
        (ratFuncUnitScaleEquiv (Units.mk0 b hb)⁻¹ RatFunc.X)) =
    ratFuncTranslationEquiv (1 : K) RatFunc.X
  rw [ratFuncUnitScaleEquiv_X, map_mul, AlgEquiv.commutes,
    ratFuncTranslationEquiv_X, map_mul, AlgEquiv.commutes,
    map_add, ratFuncUnitScaleEquiv_X, AlgEquiv.commutes,
    ratFuncTranslationEquiv_X]
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
  rw [mul_add, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hb,
    map_one, one_mul]

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
        ratFuncUnitScaleEquiv v * ratFuncAffineEquiv u b *
            ratFuncUnitScaleEquiv v⁻¹ =
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
    have haff :
        ratFuncAffineEquiv (1 : Kˣ) b = ratFuncTranslationEquiv b := by
      rw [ratFuncAffineEquiv, ratFuncUnitScaleEquiv_one]
      exact one_mul _
    rw [haff]
    exact ratFuncTranslationEquiv_scale_conj_eq_one b hb
  · left
    let r : K := b / ((u : K) - 1)
    refine ⟨r, ?_⟩
    simpa [r] using ratFuncAffineEquiv_translation_conj_eq_scale u b hu

end

end GaloisForLFunctions.HTGeometry
