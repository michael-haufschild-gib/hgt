import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGroupPullbacks

/-! Pulling back sections of a group scheme preserves the group law and order action. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LiePull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {f : S' ⟶ S} {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ)
include h

private theorem exists_section_equiv :
    ∃ e : (𝟙_ (Over S') ⟶ A') ≃* (Over.mk f ⟶ A), ∀ a, (e a).left = a.left ≫ φ :=
  exists_pushEquiv h (𝟙_ (Over S')) f (Category.id_comp _).symm

private def sectionEquiv : (𝟙_ (Over S') ⟶ A') ≃* (Over.mk f ⟶ A) :=
  (exists_section_equiv h).choose

private theorem sectionEquiv_left (x : 𝟙_ (Over S') ⟶ A') :
    (sectionEquiv h x).left = x.left ≫ φ :=
  (exists_section_equiv h).choose_spec x

/-- A section pulls back uniquely, and the pullback respects pointwise multiplication. -/
def pullSections : (𝟙_ (Over S) ⟶ A) →* (𝟙_ (Over S') ⟶ A') where
  toFun x := (sectionEquiv h).symm (toUnit (Over.mk f) ≫ x)
  map_one' := by rw [comp_one, map_one]
  map_mul' _ _ := by rw [comp_mul, map_mul]

@[reassoc]
theorem pullSections_left (x : 𝟙_ (Over S) ⟶ A) :
    (pullSections h x).left ≫ φ = f ≫ x.left := by
  rw [← sectionEquiv_left h]
  exact congrArg Over.Hom.left ((sectionEquiv h).apply_symm_apply (toUnit (Over.mk f) ≫ x))

/-- A pair of compatible endomorphisms commutes with pullback on sections. -/
theorem pullSections_comp (x : 𝟙_ (Over S) ⟶ A) {a : A ⟶ A} {a' : A' ⟶ A'}
    (e : a'.left ≫ φ = φ ≫ a.left) :
    pullSections h (x ≫ a) = pullSections h x ≫ a' := by
  apply Over.OverMorphism.ext
  refine h.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
  simp only [pullSections_left, Over.comp_left, Category.assoc]
  rw [e, ← Category.assoc _ φ, pullSections_left]
  exact (Category.assoc f (show S ⟶ A.left from x.left) a.left).symm

/-- Evaluating a pulled-back section gives the corresponding point over the original base. -/
theorem pullSections_eval (T : Over S') (x : 𝟙_ (Over S) ⟶ A) :
    (toUnit T ≫ pullSections h x).left ≫ φ =
      (toUnit (Over.mk (T.hom ≫ f)) ≫ x).left := by
  simp only [Over.comp_left, Category.assoc, pullSections_left]
  rfl

end GlobalTheory.LiePull
