import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExteriorDifferentials
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! The sheaf of relative differential forms on a scheme over a ring. -/

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}

section Sections

/-- Sections tagged by their structure morphism, which determines the base action. -/
def SectionRing (_s : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : Type u :=
  Γ(X, U)

instance (s : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : CommRing (SectionRing s U) :=
  inferInstanceAs (CommRing Γ(X, U))

/-- The algebra of sections over the base ring of the scheme. -/
abbrev sectionAlgebra (s : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    Algebra k Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ U (by simp)).hom.toAlgebra

variable (s : X ⟶ Spec (CommRingCat.of k))

instance (U : X.Opens) : Algebra k (SectionRing s U) := sectionAlgebra s U

/-- Restriction of sections preserves the base algebra structure. -/
def sectionRes {U V : X.Opens} (i : V ⟶ U) :
    SectionRing s U →ₐ[k] SectionRing s V where
  toRingHom := (X.presheaf.map i.op).hom
  commutes' r := by
    change (X.presheaf.map i.op).hom
      (((Scheme.ΓSpecIso _).inv ≫ s.appLE ⊤ U _).hom r) =
        ((Scheme.ΓSpecIso _).inv ≫ s.appLE ⊤ V _).hom r
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]

theorem sectionRes_id (U : X.Opens) : sectionRes s (𝟙 U) = AlgHom.id k (SectionRing s U) := by
  ext a
  change (X.presheaf.map (𝟙 U).op).hom a = a
  simp only [op_id, Functor.map_id]
  rfl

theorem sectionRes_comp {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) :
    sectionRes s (j ≫ i) = (sectionRes s j).comp (sectionRes s i) := by
  ext a
  change (X.presheaf.map (j ≫ i).op).hom a =
    (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom a)
  rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]

end Sections

section Forms

variable (s : X ⟶ Spec (CommRingCat.of k))

/-- Differential forms on the section ring of an open set. -/
abbrev FormsOn (U : X.Opens) (n : ℕ) := ExteriorDifferentials k (SectionRing s U) n

private def formsAdd (n : ℕ) : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (FormsOn s U.unop n)
  map i := AddCommGrpCat.ofHom (ExteriorDifferentials.map (sectionRes s i.unop) n).toAddMonoidHom
  map_id U := by
    ext x
    change ExteriorDifferentials.map (sectionRes s (𝟙 U.unop)) n x = x
    rw [sectionRes_id, ExteriorDifferentials.map_id]
  map_comp i j := by
    ext x
    change ExteriorDifferentials.map (sectionRes s (j.unop ≫ i.unop)) n x =
      ExteriorDifferentials.map (sectionRes s j.unop) n
        (ExteriorDifferentials.map (sectionRes s i.unop) n x)
    rw [sectionRes_comp, ExteriorDifferentials.map_comp]

private instance formsAdd_module (n : ℕ) (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((formsAdd s n).obj U) :=
  inferInstanceAs (Module (SectionRing s U.unop) (FormsOn s U.unop n))

/-- The presheaf obtained by taking exterior differentials of each section ring. -/
def formsPresheaf (n : ℕ) : PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (formsAdd s n) fun i r x =>
    (ExteriorDifferentials.map (sectionRes s i.unop) n).map_smulₛₗ r x

/-- The sheaf of relative `n`-forms, obtained by sheafifying the presheaf of forms. -/
def relativeForms (n : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (formsPresheaf s n)

end Forms

end GlobalTheory.SchemeCohomology
