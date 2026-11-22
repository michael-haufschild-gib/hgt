import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeForms

/-! Pullback on relative differential forms for morphisms over the base ring. -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)} {f : Y ⟶ X}

/-- A scheme morphism over the base induces a base-algebra map on sections. -/
def sectionPullback (hf : f ≫ s = t) (U : X.Opens) :
    SectionRing s U →ₐ[k] SectionRing t (f ⁻¹ᵁ U) where
  toRingHom := (f.app U).hom
  commutes' r := by
    subst t
    change (f.app U).hom (((Scheme.ΓSpecIso _).inv ≫ s.appLE ⊤ U _).hom r) =
      (((Scheme.ΓSpecIso _).inv ≫ (f ≫ s).appLE ⊤ (f ⁻¹ᵁ U) _).hom r)
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]

theorem sectionRes_comp_pullback (hf : f ≫ s = t) {U V : X.Opens} (i : V ⟶ U) :
    (sectionRes t ((Opens.map f.base).map i)).comp (sectionPullback hf U) =
      (sectionPullback hf V).comp (sectionRes s i) := by
  ext x
  exact (ConcreteCategory.congr_hom (f.naturality i.op) x).symm

/-- Pullback of forms before sheafification is compatible with restriction. -/
theorem formsOn_pullback_natural (hf : f ≫ s = t) {U V : X.Opens} (i : V ⟶ U)
    (n : ℕ) (ω : FormsOn s U n) :
    ExteriorDifferentials.map (sectionRes t ((Opens.map f.base).map i)) n
      (ExteriorDifferentials.map (sectionPullback hf U) n ω) =
    ExteriorDifferentials.map (sectionPullback hf V) n
      (ExteriorDifferentials.map (sectionRes s i) n ω) := by
  rw [← ExteriorDifferentials.map_comp, ← ExteriorDifferentials.map_comp,
    sectionRes_comp_pullback]

private abbrev underlyingModules (X : Scheme.{u}) : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
  SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)

/-- The canonical map from forms on section rings into the sheaf of forms. -/
def toRelativeForms (s : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    formsPresheaf s n ⟶ (underlyingModules X).obj (relativeForms s n) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (formsPresheaf s n)

private def formsPullbackPresheaf (hf : f ≫ s = t) (n : ℕ) :
    formsPresheaf s n ⟶ (underlyingModules X).obj
      ((Scheme.Modules.pushforward f).obj (relativeForms t n)) where
  app U := ModuleCat.ofHom
    { toFun := fun ω => (toRelativeForms t n).app (op (f ⁻¹ᵁ U.unop))
        (ExteriorDifferentials.map (sectionPullback hf U.unop) n ω)
      map_add' x y :=
        (((toRelativeForms t n).app (op (f ⁻¹ᵁ U.unop))).hom.toAddMonoidHom.comp
          (ExteriorDifferentials.map (sectionPullback hf U.unop) n).toAddMonoidHom).map_add x y
      map_smul' r ω := by
        let L := ((toRelativeForms t n).app (op (f ⁻¹ᵁ U.unop))).hom
        let E := ExteriorDifferentials.map (sectionPullback hf U.unop) n
        exact (congrArg L (E.map_smulₛₗ r ω)).trans (L.map_smul _ _) }
  naturality {U V} i := by
    ext ω
    exact (congrArg (fun x => (toRelativeForms t n).app (op (f ⁻¹ᵁ V.unop)) x)
        (formsOn_pullback_natural hf i.unop n ω)).symm.trans
      (PresheafOfModules.naturality_apply (toRelativeForms t n)
        ((Opens.map f.base).map i.unop).op
        (ExteriorDifferentials.map (sectionPullback hf U.unop) n ω))

/-- Pullback of relative forms is a morphism to the pushforward of the sheaf of forms. -/
def relativeFormsPullback (hf : f ≫ s = t) (n : ℕ) :
    relativeForms s n ⟶ (Scheme.Modules.pushforward f).obj (relativeForms t n) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
    (formsPullbackPresheaf hf n)

end GlobalTheory.SchemeCohomology
