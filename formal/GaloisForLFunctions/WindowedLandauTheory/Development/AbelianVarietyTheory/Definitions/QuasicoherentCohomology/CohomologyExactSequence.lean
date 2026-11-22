import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CohomologyOn
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.RingTheory.Noetherian.Basic

/-! The cohomology sequence of a short exact sequence of scheme modules is linear over the
global section ring. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
  Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {X : Scheme.{u}}

private abbrev toAbelianSheaf (X : Scheme.{u}) := SheafOfModules.toSheaf X.ringCatSheaf

private theorem toAbelianSheaf_map_epi {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Epi ((toAbelianSheaf X).map f) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (J := Opens.grothendieckTopology X) (𝟙 X.ringCatSheaf.obj)
  let a := PresheafOfModules.sheafification (J := Opens.grothendieckTopology X)
    (𝟙 X.ringCatSheaf.obj)
  let G := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let f₀ := G.map f
  have hnat : a.map f₀ ≫ adj.counit.app N = adj.counit.app M ≫ f := adj.counit.naturality f
  haveI : Epi (a.map f₀) := by
    have e : a.map f₀ = adj.counit.app M ≫ f ≫ inv (adj.counit.app N) := by
      rw [← reassoc_of% hnat, IsIso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  have hfac : a.map f₀ = a.map (factorThruImage f₀) ≫ a.map (image.ι f₀) := by
    rw [← a.map_comp, image.fac]
  -- The inclusion of the presheaf image becomes an isomorphism after sheafification.
  haveI : Epi (a.map (factorThruImage f₀) ≫ a.map (image.ι f₀)) := by
    rw [← hfac]
    infer_instance
  haveI : Epi (a.map (image.ι f₀)) :=
    epi_of_epi (a.map (factorThruImage f₀)) _
  haveI : IsIso (a.map (image.ι f₀)) := isIso_of_mono_of_epi _
  haveI : Epi ((toAbelianSheaf X).map (a.map (factorThruImage f₀))) := by
    haveI : Epi ((PresheafOfModules.toPresheaf _).map (factorThruImage f₀)) := by
      apply NatTrans.epi_of_epi_app
    change Epi ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf _).map (factorThruImage f₀)))
    exact (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_epi _
  haveI : Epi ((toAbelianSheaf X).map (a.map f₀)) := by
    rw [hfac, Functor.map_comp]
    infer_instance
  have e : (toAbelianSheaf X).map f =
      inv ((toAbelianSheaf X).map (adj.counit.app M)) ≫ (toAbelianSheaf X).map (a.map f₀) ≫
        (toAbelianSheaf X).map (adj.counit.app N) := by
    rw [← Functor.map_comp, hnat, Functor.map_comp, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- A short exact sequence of scheme modules remains short exact as abelian sheaves. -/
theorem shortExact_toAbelianSheaf {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toAbelianSheaf X)).ShortExact := by
  obtain ⟨hexact, hmono⟩ := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (toAbelianSheaf X)).mp inferInstance S hS
  haveI := hS.epi_g
  haveI : Epi ((toAbelianSheaf X).map S.g) := toAbelianSheaf_map_epi S.g
  exact ShortComplex.ShortExact.mk' hexact hmono inferInstance

local instance cohomologyExactHasExt (T : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} T) :=
  hasExt_of_enoughInjectives _

private abbrev freeSheafOn (U : X.Opens) :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

private def scalarShortComplexMap (S : ShortComplex X.Modules) (r : Γ(X, ⊤)) :
    S ⟶ S where
  τ₁ := globalSectionEnd S.X₁ r
  τ₂ := globalSectionEnd S.X₂ r
  τ₃ := globalSectionEnd S.X₃ r
  comm₁₂ := globalSectionEnd_natural S.f r
  comm₂₃ := globalSectionEnd_natural S.g r

/-- The connecting map is linear since multiplication by a global section
is an endomorphism of the short exact sequence. -/
def CohomologyOn.boundary {S : ShortComplex X.Modules} (hS : S.ShortExact) (U : X.Opens) (q : ℕ) :
    CohomologyOn S.X₃ U q →ₗ[Γ(X, ⊤)] CohomologyOn S.X₁ U (q + 1) :=
  let h := shortExact_toAbelianSheaf hS
  { h.extClass.postcomp (freeSheafOn U) (rfl : q + 1 = q + 1) with
    map_smul' r x := by
      let a := (toAbelianSheaf X).mapShortComplex.map (scalarShortComplexMap S r)
      let y : Ext (freeSheafOn U) ((toAbelianSheaf X).obj S.X₃) q := x
      change (y.comp (Ext.mk₀ a.τ₃) (add_zero q)).comp h.extClass rfl =
        (y.comp h.extClass rfl).comp (Ext.mk₀ a.τ₁) (add_zero (q + 1))
      rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
        h.extClass_naturality h a] }

theorem CohomologyOn.exact_map_boundary {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (U : X.Opens) (q : ℕ) : Function.Exact (CohomologyOn.map S.g U q) (CohomologyOn.boundary hS U q) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₃' (freeSheafOn U) (shortExact_toAbelianSheaf hS) q (q + 1) rfl)

theorem CohomologyOn.exact_boundary_map {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (U : X.Opens) (q : ℕ) :
    Function.Exact (CohomologyOn.boundary hS U q) (CohomologyOn.map S.f U (q + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₁' (freeSheafOn U) (shortExact_toAbelianSheaf hS) q (q + 1) rfl)

/-- Finiteness of the outer modules in an exact pair over a Noetherian ring implies
finiteness of the middle module. -/
theorem finite_of_exact_noetherian {R M N P : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] [Module.Finite R M] [Module.Finite R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g) : Module.Finite R N := by
  have hk : LinearMap.ker g = LinearMap.range f := by
    ext y
    exact h y
  letI : IsNoetherian R P := isNoetherian_of_isNoetherianRing_of_finite R P
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · rw [Submodule.map_top]
    exact IsNoetherian.noetherian _
  · rw [top_inf_eq, hk, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map f

end GlobalTheory.SchemeCohomology
