/- Local compatibility change: reassociate biproduct projections explicitly on Mathlib 4.32.2. -/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DifferentialGeometry.ShortComplex
variable {C : Type*} [Category* C] [Abelian C]
  {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {r : X ⟶ Z} {s : Y ⟶ Z}
  (sq : IsPushout f g r s)


abbrev pushoutShortComplex : ShortComplex C :=
  ShortComplex.mk (biprod.lift f (-g)) (biprod.desc r s) (by
    rw [biprod.lift_desc, Preadditive.neg_comp, sq.w, add_neg_cancel])


def pushoutSumIsCokernel :
    IsColimit (CokernelCofork.ofπ (pushoutShortComplex sq).g (pushoutShortComplex sq).zero) :=
  Cofork.IsColimit.mk _
    (fun c => sq.desc (biprod.inl ≫ Cofork.π c) (biprod.inr ≫ Cofork.π c) <|
      sub_eq_zero.1 <| by
        rw [← Category.assoc, ← Category.assoc, ← Preadditive.sub_comp,
          sub_eq_add_neg, ← Preadditive.neg_comp, ← biprod.lift_eq, Cofork.condition c,
          zero_comp])
    (fun c => by
      apply biprod.hom_ext'
      · change biprod.inl ≫ biprod.desc r s ≫ _ = _
        rw [← Category.assoc, biprod.inl_desc, sq.inl_desc]
      · change biprod.inr ≫ biprod.desc r s ≫ _ = _
        rw [← Category.assoc, biprod.inr_desc, sq.inr_desc])
    (fun c m hm => by
      apply sq.hom_ext
      · have h := congrArg (fun φ => biprod.inl ≫ φ) hm
        change biprod.inl ≫ biprod.desc r s ≫ m = _ at h
        rw [← Category.assoc, biprod.inl_desc] at h
        simpa only [sq.inl_desc] using h
      · have h := congrArg (fun φ => biprod.inr ≫ φ) hm
        change biprod.inr ≫ biprod.desc r s ≫ m = _ at h
        rw [← Category.assoc, biprod.inr_desc] at h
        simpa only [sq.inr_desc] using h)

theorem pushoutShortExact [Mono f] : (pushoutShortComplex sq).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (pushoutSumIsCokernel sq)
  mono_f := by
    exact mono_of_mono_fac (show (pushoutShortComplex sq).f ≫ biprod.fst = f from biprod.lift_fst _ _)
  epi_g := epi_of_isColimit_cofork (pushoutSumIsCokernel sq)

end DifferentialGeometry.ShortComplex
