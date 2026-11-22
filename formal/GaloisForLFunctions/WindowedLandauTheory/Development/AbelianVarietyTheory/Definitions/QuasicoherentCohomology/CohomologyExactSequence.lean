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

private abbrev toAbelianSheaf (X : Scheme.{u}) : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf X.ringCatSheaf

local instance (X : Scheme.{u}) : (toAbelianSheaf X).PreservesZeroMorphisms :=
  inferInstanceAs ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesZeroMorphisms)

local instance (X : Scheme.{u}) : PreservesFiniteLimits (toAbelianSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

private theorem epi_iff_of_iso_square {C : Type*} [Category* C] {A B D E : C}
    (e : A ≅ B) (e' : D ≅ E) {f : A ⟶ D} {g : B ⟶ E}
    (h : f ≫ e'.hom = e.hom ≫ g) : Epi f ↔ Epi g := by
  constructor
  · intro hf
    letI := hf
    haveI : Epi (e.hom ≫ g) := h ▸ epi_comp f e'.hom
    exact epi_of_epi e.hom g
  · intro hg
    letI := hg
    have he := congrArg (· ≫ e'.inv) h
    have hf : f = e.hom ≫ g ≫ e'.inv := by
      simpa only [Category.assoc, e'.hom_inv_id, Category.comp_id] using he
    rw [hf]
    infer_instance

private theorem toAbelianSheaf_map_epi {M N : X.Modules} (f : M ⟶ N) [hf : Epi f] :
    Epi ((toAbelianSheaf X).map f) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (J := Opens.grothendieckTopology X) (𝟙 X.ringCatSheaf.obj)
  let a := PresheafOfModules.sheafification (J := Opens.grothendieckTopology X)
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit := inferInstanceAs (IsIso
    (PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj)).counit)
  letI : a.IsLeftAdjoint := adj.isLeftAdjoint
  let ε := asIso adj.counit
  let G := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let f₀ := G.map f
  have hnat : a.map f₀ ≫ (ε.app N).hom = (ε.app M).hom ≫ f := adj.counit.naturality f
  haveI : Epi (a.map f₀) := (epi_iff_of_iso_square (ε.app M) (ε.app N) hnat).mpr hf
  have hfac : a.map f₀ = a.map (Limits.factorThruImage f₀) ≫ a.map (Limits.image.ι f₀) := by
    rw [← a.map_comp, Limits.image.fac]
  -- The inclusion of the presheaf image becomes an isomorphism after sheafification.
  haveI : Epi (a.map (Limits.factorThruImage f₀) ≫ a.map (Limits.image.ι f₀)) := by
    rw [← hfac]
    infer_instance
  haveI : Epi (a.map (Limits.image.ι f₀)) :=
    epi_of_epi (a.map (Limits.factorThruImage f₀)) _
  have hi : IsIso (a.map (Limits.image.ι f₀)) := isIso_of_mono_of_epi _
  haveI : Epi ((toAbelianSheaf X).map (a.map (Limits.factorThruImage f₀))) := by
    haveI : Epi ((PresheafOfModules.toPresheaf _).map (Limits.factorThruImage f₀)) :=
      Functor.map_epi (PresheafOfModules.toPresheaf _) _
    change Epi ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf _).map (Limits.factorThruImage f₀)))
    exact (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_epi _
  let A := toAbelianSheaf X
  letI : Epi (A.map (a.map (Limits.factorThruImage f₀))) :=
    inferInstanceAs (Epi ((toAbelianSheaf X).map (a.map (Limits.factorThruImage f₀))))
  let i := A.mapIso (@asIso _ _ _ _ (a.map (Limits.image.ι f₀)) hi)
  letI : Epi (A.map (a.map (Limits.image.ι f₀))) := @IsIso.epi_of_iso _ _ _ _ i.hom i.isIso_hom
  have hc : A.map (a.map f₀) =
      A.map (a.map (Limits.factorThruImage f₀)) ≫ A.map (a.map (Limits.image.ι f₀)) :=
    (congrArg A.map hfac).trans (A.map_comp _ _)
  have hmapEpi : Epi (A.map (a.map f₀)) :=
    hc.symm ▸ epi_comp (A.map (a.map (Limits.factorThruImage f₀))) (A.map (a.map (Limits.image.ι f₀)))
  have hn : A.map (a.map f₀) ≫ (A.mapIso (ε.app N)).hom = (A.mapIso (ε.app M)).hom ≫ A.map f :=
    (A.map_comp _ _).symm.trans ((congrArg A.map hnat).trans (A.map_comp _ _))
  exact (epi_iff_of_iso_square (A.mapIso (ε.app M)) (A.mapIso (ε.app N)) hn).mp hmapEpi

/-- A short exact sequence of scheme modules remains short exact as abelian sheaves. -/
theorem shortExact_toAbelianSheaf {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toAbelianSheaf X)).ShortExact := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  exact .mk' (hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance)
    (Functor.map_mono (toAbelianSheaf X) S.f) (toAbelianSheaf_map_epi S.g)

local instance cohomologyExactHasExt (T : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} T) :=
  hasExt_of_enoughInjectives _

private abbrev freeSheafOn (U : X.Opens) : TopCat.Sheaf AddCommGrpCat.{u} X :=
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
    CohomologyOn S.X₃ U q →ₗ[Γ(X, ⊤)] CohomologyOn S.X₁ U (q + 1) := by
  letI : HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) := cohomologyExactHasExt X
  let h := shortExact_toAbelianSheaf hS
  let δ : CohomologyOn S.X₃ U q →+ CohomologyOn S.X₁ U (q + 1) :=
    h.extClass.postcomp (freeSheafOn U) (rfl : q + 1 = q + 1)
  refine { δ with map_smul' := ?_ }
  intro r x
  let a := (toAbelianSheaf X).mapShortComplex.map (scalarShortComplexMap S r)
  let y : Ext (freeSheafOn U) ((toAbelianSheaf X).obj S.X₃) q := x
  change (y.comp (Ext.mk₀ a.τ₃) (add_zero q)).comp h.extClass rfl =
    (y.comp h.extClass rfl).comp (Ext.mk₀ a.τ₁) (add_zero (q + 1))
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]
  exact congrArg (fun η : Ext ((toAbelianSheaf X).obj S.X₃)
    ((toAbelianSheaf X).obj S.X₁) 1 => y.comp η rfl) (h.extClass_naturality h a).symm

theorem CohomologyOn.exact_map_boundary {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (U : X.Opens) (q : ℕ) : Function.Exact (CohomologyOn.map S.g U q) (CohomologyOn.boundary hS U q) := by
  letI : HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) := cohomologyExactHasExt X
  have e := (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₃' (freeSheafOn U) (shortExact_toAbelianSheaf hS) q (q + 1) rfl)
  intro y
  exact e y

theorem CohomologyOn.exact_boundary_map {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (U : X.Opens) (q : ℕ) :
    Function.Exact (CohomologyOn.boundary hS U q) (CohomologyOn.map S.f U (q + 1)) := by
  letI : HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) := cohomologyExactHasExt X
  have e := (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₁' (freeSheafOn U) (shortExact_toAbelianSheaf hS) q (q + 1) rfl)
  intro y
  exact e y

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
