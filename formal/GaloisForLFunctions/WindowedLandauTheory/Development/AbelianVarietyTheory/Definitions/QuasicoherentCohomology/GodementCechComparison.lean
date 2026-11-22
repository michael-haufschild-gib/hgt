import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCechComplex
import GaloisForLFunctions.HTGeometry.SheafCechLeray
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! Godement dimension shifting for Čech cohomology on a cover with acyclic intersections. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HTGeometry RHTower

namespace GlobalTheory.SchemeCohomology

universe u w

variable {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}

private def godementMap (φ : F ⟶ G) : deningerGodementSheaf F ⟶ deningerGodementSheaf G :=
  ⟨{ app := fun W => AddCommGrpCat.ofHom
      { toFun := fun s x => (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map φ.1 (s x)
        map_zero' := funext fun x => map_zero _
        map_add' := fun s t => funext fun x => map_add _ (s x) (t x) }
     naturality := fun _ _ _ => rfl }⟩

private theorem godementMap_natural (φ : F ⟶ G) :
    deningerGodementι F ≫ godementMap φ = φ ≫ deningerGodementι G := by
  ext W s
  funext x
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ x.1 x.2 φ.1 s

/-- The map of short exact Godement sequences induced by a map of sheaves. -/
def godementSequenceMap (φ : F ⟶ G) : deningerGodementComplex F ⟶ deningerGodementComplex G where
  τ₁ := φ
  τ₂ := godementMap φ
  τ₃ := cokernel.map _ _ φ (godementMap φ) (godementMap_natural φ)
  comm₁₂ := (godementMap_natural φ).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

variable {ι : Type*} [DecidableEq ι] [LinearOrder ι] (V : Opens X) (U : ι → Opens X)

/-- The alternating Čech complex of a sheaf on the given cover. -/
abbrev sheafCechComplex (F : TopCat.Sheaf AddCommGrpCat.{u} X) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (sheafCech F V U).cochainComplex

variable {V U}

/-- A sheaf and its Godement quotient form a termwise short exact sequence of Čech
complexes if the original sheaf is acyclic on the intersections. -/
theorem godementCech_shortExact [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (hF : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} F (coverInter V U a)) :
    (ShortComplex.mk
      (sheafCechMap (deningerGodementComplex F).f V U).cochainMap
      (sheafCechMap (deningerGodementComplex F).g V U).cochainMap (by
        ext n c
        exact Subtype.ext (funext fun a => sheafCech_comp_zero V U a (c.1 a)))).ShortExact := by
  have hS := deningerGodementShortExact F
  exact FinsetCechDatum.shortExact_cochainMap _ _
    (sheafCech_comp_zero V U)
    (fun a _ => sheafCech_injective hS a)
    (fun a _ => ⟨fun h => sheafCech_exact hS a _ h, by
      rintro ⟨x, rfl⟩
      exact sheafCech_comp_zero V U a x⟩)
    (fun a ha => deningerSections_surjective_of_acyclic hS _ (hF a ha))

theorem isZero_godementCech_homology (hcov : V ≤ ⨆ i, U i) (n : ℕ) :
    IsZero ((sheafCechComplex V U (deningerGodementSheaf F)).homology (n + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    (FinsetCechDatum.cochainComplex_exactAt _ (godementCech_exactAt hcov (n + 1)))

end GlobalTheory.SchemeCohomology
