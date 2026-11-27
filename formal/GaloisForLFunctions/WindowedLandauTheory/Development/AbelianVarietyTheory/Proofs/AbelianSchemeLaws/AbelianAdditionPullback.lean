import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGroupPullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! Addition and the second projection exhibit the same relative product. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw

attribute [local instance] Over.cartesianMonoidalCategory

private theorem isIso_shear {C : Type*} [Category C] [CartesianMonoidalCategory C] (A : C) [GrpObj A] :
    IsIso (lift μ[A] (snd A A)) := by
  have hμ : μ[A] = fst A A * snd A A := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  refine ⟨lift (fst A A * (snd A A)⁻¹) (snd A A), ?_, ?_⟩
  · ext
    · rw [Category.assoc, lift_fst, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, hμ]
      simp only [mul_inv_cancel_right, Category.id_comp]
    · simp
  · ext
    · rw [Category.assoc, lift_fst, hμ, MonObj.comp_mul, lift_fst, lift_snd]
      simp only [inv_mul_cancel_right, Category.id_comp]
    · simp

/-- The shear `(x, y) ↦ (xy, y)` identifies addition and the second projection
with the two product projections over the base. -/
theorem isPullback_mul_snd {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    IsPullback μ[A].left (snd A A).left A.hom A.hom := by
  have h₀ : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    IsPullback.of_hasPullback A.hom A.hom
  letI := isIso_shear A
  letI : IsIso (lift μ[A] (snd A A)).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (lift μ[A] (snd A A))))
  have h₁ : IsPullback (lift μ[A] (snd A A)).left (snd A A).left (snd A A).left (𝟙 A.left) :=
    IsPullback.of_horiz_isIso ⟨by rw [← Over.comp_left, lift_snd, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz h₀
  rwa [← Over.comp_left, lift_fst, Category.id_comp] at h₂

end GlobalTheory.AbLaw
