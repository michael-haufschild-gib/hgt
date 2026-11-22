import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsAcyclic
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PushforwardComparison
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! Comparing cohomology of quasi-coherent sheaves along an affine morphism. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

local instance affinePushforwardHasExt (X : TopCat.{0}) :
    HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  hasExt_of_enoughInjectives _

private def freeComparison {X : TopCat.{0}} (U : Opens X) :
    RHTower.deningerOpenFree U ⟶ openFree U :=
  (RHTower.deningerOpenFreeHomEquiv U (openFree U)).symm (openFreeHomEquiv U _ (𝟙 _))

private theorem freeComparison_comp {X : TopCat.{0}} (U : Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{0} X} (a : openFree U ⟶ F) :
    RHTower.deningerOpenFreeHomEquiv U F (freeComparison U ≫ a) = openFreeHomEquiv U F a := by
  rw [RHTower.deningerOpenFreeHomEquiv_naturality_right, freeComparison, Equiv.apply_symm_apply,
    ← openFreeHomEquiv_natural, Category.id_comp]

private instance {X : TopCat.{0}} (U : Opens X) : IsIso (freeComparison U) := by
  apply isIso_of_coyoneda_map_bijective
  intro F
  convert ((openFreeHomEquiv U F).trans (RHTower.deningerOpenFreeHomEquiv U F).symm).bijective using 1
  funext a
  exact (RHTower.deningerOpenFreeHomEquiv U F).injective ((freeComparison_comp U a).trans
    (Equiv.apply_symm_apply _ _).symm)

variable {X Y : Scheme.{0}} (f : Y ⟶ X) [IsAffineHom f]

/-- An affine morphism computes cohomology of quasi-coherent sheaves by its direct image. -/
theorem quasicoherent_pushforwardComparison_bijective (M : Y.Modules) [M.IsQuasicoherent]
    (q : ℕ) (V : X.Opens) :
    Function.Bijective (CohomologyOn.pushforwardComparison f M V q) := by
  let G := (SheafOfModules.toSheaf Y.ringCatSheaf).obj M
  change Function.Bijective (abelianPushforwardComparison f.base G V q)
  refine abelianPushforwardComparison_bijective f.base X.isBasis_affineOpens G ?_ V q
  intro U hU n x
  let e := asIso (freeComparison (f ⁻¹ᵁ U))
  have h0 := quasicoherent_acyclicOn M (IsAffineOpen.preimage hU f) n
    ((Ext.mk₀ e.hom).comp x (zero_add (n + 1)))
  have h := congrArg ((Ext.mk₀ e.inv).precomp G (zero_add (n + 1))) h0
  change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add (n + 1))) (zero_add (n + 1)) =
    (Ext.mk₀ e.inv).comp 0 (zero_add (n + 1)) at h
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.mk₀_id_comp,
    Ext.comp_zero] at h
  exact h

/-- Cohomology of relative forms is computed by direct image along an affine morphism. -/
theorem relativeForms_pushforwardComparison_bijective {k : Type} [CommRing k]
    (t : Y ⟶ Spec (CommRingCat.of k)) (p q : ℕ) (V : X.Opens) :
    Function.Bijective (CohomologyOn.pushforwardComparison f (relativeForms t p) V q) := by
  letI := relativeForms_isQuasicoherent t p
  exact quasicoherent_pushforwardComparison_bijective f (relativeForms t p) q V

end GlobalTheory.SchemeCohomology
