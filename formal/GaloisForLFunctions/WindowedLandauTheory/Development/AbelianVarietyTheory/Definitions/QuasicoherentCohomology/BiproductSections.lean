import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.QuasicoherenceOnAffines
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! Finite direct sums of modules preserve finite sections and the basic-open
localization property. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology

universe u

variable {X : Scheme.{u}} {I : Type u} [Fintype I] (F : I → X.Modules)

private abbrev sectionEvaluation (U : X.Opens) : X.Modules ⥤ ModuleCat Γ(X, U) :=
  SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)

private def sectionsBiproductIso (U : X.Opens) :
    (sectionEvaluation U).obj (⨁ F) ≅ ModuleCat.of Γ(X, U) (∀ i, Γ(F i, U)) :=
  let A := sectionEvaluation U
  letI : PreservesBiproduct F A := preservesBiproduct_of_preservesProduct A
  mapBiproduct A F ≪≫ ModuleCat.biproductIsoPi (A.obj ∘ F)

/-- Sections of a finite biproduct identify with the product by the projections. -/
def sectionsBiproductEquiv (U : X.Opens) :
    Γ(⨁ F, U) ≃ₗ[Γ(X, U)] ∀ i, Γ(F i, U) :=
  (sectionsBiproductIso F U).toLinearEquiv

theorem sectionsBiproductEquiv_apply (U : X.Opens) (x : Γ(⨁ F, U)) (i : I) :
    sectionsBiproductEquiv F U x i = (biproduct.π F i).app U x := by
  let A := sectionEvaluation U
  letI : PreservesBiproduct F A := preservesBiproduct_of_preservesProduct A
  have h : (sectionsBiproductIso F U).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) = A.map (biproduct.π F i) := by
    change (mapBiproduct A F).hom ≫ (ModuleCat.biproductIsoPi _).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) = _
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc,
      mapBiproduct_hom, biproduct.lift_π]
  exact ConcreteCategory.congr_hom h x

theorem biproduct_sections_finite (U : X.Opens)
    (hF : ∀ i, Module.Finite Γ(X, U) Γ(F i, U)) :
    Module.Finite Γ(X, U) Γ(⨁ F, U) := by
  letI := hF
  exact Module.Finite.equiv (sectionsBiproductEquiv F U).symm

theorem biproduct_isQuasicoherent (hF : ∀ i, (F i).IsQuasicoherent) :
    (⨁ F).IsQuasicoherent := by
  classical
  let G := (⨁ F : X.Modules)
  refine isQuasicoherent_of_affineCover_localization G (fun U : X.affineOpens => U.1)
    (IsOpenCover.mk (iSup_affineOpens_eq_top X)) (fun U => U.2) ?_
  intro V f
  let U : X.Opens := V.1
  let W := X.basicOpen f
  let j : W ⟶ U := homOfLE (X.basicOpen_le f)
  let q := X.presheaf.map j.op f
  let π (i : I) : G ⟶ F i := biproduct.π F i
  have hnat (i : I) (x : Γ(G, U)) :
      (π i).app W (G.presheaf.map j.op x) = (F i).presheaf.map j.op ((π i).app U x) :=
    NatTrans.naturality_apply (π i).mapPresheaf j.op x
  have hloc (i : I) : HasBasicOpenLocalization (F i) U f := by
    letI := hF i
    exact hasBasicOpenLocalization_of_isQuasicoherent (F i) V.2 f
  constructor
  · intro z
    have h (i : I) : ∃ n : ℕ, ∃ y : Γ(F i, U),
        q ^ n • (π i).app W z = (F i).presheaf.map j.op y :=
      (hloc i).1 ((π i).app W z)
    choose n y hy using h
    let N := Finset.univ.sup n
    let t (i : I) := f ^ (N - n i) • y i
    let x : Γ(G, U) := (sectionsBiproductEquiv F U).symm t
    refine ⟨N, x, ?_⟩
    apply (sectionsBiproductEquiv F W).injective
    funext i
    simp only [sectionsBiproductEquiv_apply, Scheme.Modules.Hom.app_smul, hnat]
    have hx : (π i).app U x = t i := by
      rw [← sectionsBiproductEquiv_apply, LinearEquiv.apply_symm_apply]
    rw [hx]
    change q ^ N • (π i).app W z = (F i).presheaf.map j.op (f ^ (N - n i) • y i)
    rw [(F i).map_smul j, map_pow, ← hy, smul_smul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ i))]
  · intro z hz
    have h (i : I) : ∃ n : ℕ, f ^ n • (π i).app U z = 0 := by
      apply (hloc i).2
      rw [← hnat, hz, map_zero]
    choose n hn using h
    let N := Finset.univ.sup n
    refine ⟨N, ?_⟩
    apply (sectionsBiproductEquiv F U).injective
    funext i
    simp only [sectionsBiproductEquiv_apply, Scheme.Modules.Hom.app_smul, map_zero]
    have hi : n i ≤ N := Finset.le_sup (f := n) (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hi, pow_add, mul_smul, hn, smul_zero]

end GlobalTheory.SchemeCohomology
