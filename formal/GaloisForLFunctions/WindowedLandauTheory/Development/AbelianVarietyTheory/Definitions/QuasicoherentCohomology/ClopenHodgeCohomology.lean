import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ClopenRelativeForms
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BiproductCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HodgeTrace

/-! Restriction identifies Hodge cohomology with the product over a finite clopen partition. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.SchemeCohomology

local instance clopenCohomologyHasExt (T : TopCat.{0}) :
    HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} T) := hasExt_of_enoughInjectives _

variable {K : Type} [CommRing K] {X : Scheme.{0}} {J : Type} [Fintype J]
  (s : X ⟶ Spec (CommRingCat.of K)) (U : J → X.Opens)

private theorem cohomology_map_bijective_of_iso {F G : X.Modules} (e : F ≅ G) (q : ℕ) :
    Function.Bijective (CohomologyOn.map e.hom ⊤ q) := by
  let P : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat :=
    SheafOfModules.toSheaf X.ringCatSheaf
  let e' := P.mapIso e
  let a := CohomologyOn.map e.hom ⊤ q
  let b := CohomologyOn.map e.inv ⊤ q
  have h₁ : Function.LeftInverse b a := by
    intro x
    change ((x : Ext _ _ q).comp (Ext.mk₀ e'.hom) (add_zero q)).comp
      (Ext.mk₀ e'.inv) (add_zero q) = x
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    exact (congrArg (fun m => (x : Ext _ _ q).comp (Ext.mk₀ m) (add_zero q))
      e'.hom_inv_id).trans ((x : Ext _ _ q).comp_mk₀_id)
  have h₂ : Function.RightInverse b a := by
    intro x
    change ((x : Ext _ _ q).comp (Ext.mk₀ e'.inv) (add_zero q)).comp
      (Ext.mk₀ e'.hom) (add_zero q) = x
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    exact (congrArg (fun m => (x : Ext _ _ q).comp (Ext.mk₀ m) (add_zero q))
      e'.inv_hom_id).trans ((x : Ext _ _ q).comp_mk₀_id)
  exact ⟨h₁.injective, h₂.surjective⟩

/-- The restriction maps are jointly a linear equivalence to the Hodge
cohomology of a finite clopen partition. -/
def hodgeClopenEquiv (p q : ℕ) (hclosed : ∀ i, IsClosed (U i : Set X))
    (hdis : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : iSup U = ⊤) :
    HodgeCohomology s p q ≃ₗ[K] ∀ i, HodgeCohomology ((U i).ι ≫ s) p q := by
  letI (i : J) : IsClosedImmersion (U i).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hclosed i)
  let e := clopenFormsIso s U p hclosed hdis hcov
  let a := CohomologyOn.map e.hom ⊤ q
  let b := CohomologyOn.biproductEquiv (clopenForms s U p) ⊤ q
  let c (i : J) := formsPushforwardEquiv (s := s) (f := (U i).ι) rfl p q
  let E := Equiv.piCongrRight fun i => (c i).toEquiv
  let L := LinearMap.pi fun i => hodgePullback (s := s) (f := (U i).ι) rfl p q
  have h : (L : HodgeCohomology s p q → _) = E ∘ b ∘ a := by
    funext x i
    change c i (CohomologyOn.map (relativeFormsPullback (s := s) (f := (U i).ι) rfl p) ⊤ q x) =
      c i (b (a x) i)
    apply congrArg (c i)
    let P : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat :=
      SheafOfModules.toSheaf X.ringCatSheaf
    change (x : Ext _ _ q).comp
      (Ext.mk₀ (P.map (relativeFormsPullback (s := s) (f := (U i).ι) rfl p))) (add_zero q) =
      ((x : Ext _ _ q).comp (Ext.mk₀ (P.map e.hom)) (add_zero q)).comp
        (Ext.mk₀ (P.map (biproduct.π (clopenForms s U p) i))) (add_zero q)
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp]
    exact congrArg (fun m => (x : Ext _ _ q).comp (Ext.mk₀ (P.map m)) (add_zero q))
      (clopenFormsIso_hom_π s U p hclosed hdis hcov i).symm
  exact LinearEquiv.ofBijective L
    (h.symm ▸ E.bijective.comp (b.bijective.comp (cohomology_map_bijective_of_iso e q)))

@[simp] theorem hodgeClopenEquiv_apply (p q : ℕ) (hclosed : ∀ i, IsClosed (U i : Set X))
    (hdis : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : iSup U = ⊤)
    (x : HodgeCohomology s p q) (i : J) :
    hodgeClopenEquiv s U p q hclosed hdis hcov x i =
      hodgePullback (s := s) (f := (U i).ι) rfl p q x :=
  rfl

end GlobalTheory.SchemeCohomology
