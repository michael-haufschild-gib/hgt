import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineTraceTower
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HodgeTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CohomologyPullbackComposition

/-! The tower law for affine traces gives transitivity of the
finite étale trace on Hodge cohomology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite

namespace GlobalTheory.SchemeCohomology

local instance traceTowerHasExt (X : TopCat.{0}) :
    HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X) := hasExt_of_enoughInjectives _

/-- Successive coefficient maps on global cohomology compose. -/
theorem CohomologyOn.map_comp_top {X : Scheme.{0}} {A B C : X.Modules}
    (f : A ⟶ B) (g : B ⟶ C) (q : ℕ) (x : CohomologyOn A ⊤ q) :
    CohomologyOn.map g ⊤ q (CohomologyOn.map f ⊤ q x) =
      CohomologyOn.map (f ≫ g) ⊤ q x := by
  let P := SheafOfModules.toSheaf X.ringCatSheaf
  change ((x : Ext _ _ q).comp (Ext.mk₀ (P.map f)) (add_zero q)).comp
      (Ext.mk₀ (P.map g)) (add_zero q) =
    (x : Ext _ _ q).comp (Ext.mk₀ (P.map (f ≫ g))) (add_zero q)
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp]

private theorem cohomologyMap_id_top {X : Scheme.{0}} {A : X.Modules}
    (q : ℕ) (x : CohomologyOn A ⊤ q) :
    CohomologyOn.map (𝟙 A) ⊤ q x = x := by
  let P := SheafOfModules.toSheaf X.ringCatSheaf
  change (x : Ext _ _ q).comp (Ext.mk₀ (P.map (𝟙 A))) (add_zero q) = x
  rw [Functor.map_id, Ext.comp_mk₀_id]

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}}
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {u : Z ⟶ Spec (CommRingCat.of k)} {f : Y ⟶ X} {g : Z ⟶ Y}
  [IsFinite f] [Etale f] [IsFinite g] [Etale g]

/-- Equal finite étale morphisms give the same Hodge trace. -/
theorem hodgeTrace_congr {f' : Y ⟶ X} [IsFinite f'] [Etale f']
    (e : f = f') (hf : f ≫ s = t) (hf' : f' ≫ s = t) (p q : ℕ) :
    hodgeTrace hf p q = hodgeTrace hf' p q := by
  subst f'
  rfl

/-- The trace morphism on relative forms composes under the
direct-image comparison. -/
theorem relativeFormsTrace_trans (hf : f ≫ s = t) (hg : g ≫ t = u)
    (hgf : (g ≫ f) ≫ s = u) (p : ℕ) :
    (Scheme.Modules.pushforwardComp g f).hom.app (relativeForms u p) ≫ relativeFormsTrace hgf p =
      (Scheme.Modules.pushforward f).map (relativeFormsTrace hg p) ≫ relativeFormsTrace hf p := by
  apply moduleHom_ext_affine
  intro U hU x
  obtain ⟨ω, rfl⟩ := (affineFormsSections u p (hU.preimage (g ≫ f))).surjective x
  change (relativeFormsTrace hgf p).app U (formsOnToSections u p ((g ≫ f) ⁻¹ᵁ U) ω) =
    (relativeFormsTrace hf p).app U
      ((relativeFormsTrace hg p).app (f ⁻¹ᵁ U) (formsOnToSections u p (g ⁻¹ᵁ (f ⁻¹ᵁ U)) ω))
  rw [relativeFormsTrace_app hgf p hU, relativeFormsTrace_app hg p (hU.preimage f),
    relativeFormsTrace_app hf p hU, affineFormTrace_trans hf hg hgf hU p ω]

/-- The finite étale trace on Hodge cohomology is transitive. -/
theorem hodgeTrace_trans (hf : f ≫ s = t) (hg : g ≫ t = u)
    (hgf : (g ≫ f) ≫ s = u) (p q : ℕ) (x : HodgeCohomology u p q) :
    hodgeTrace hgf p q x = hodgeTrace hf p q (hodgeTrace hg p q x) := by
  let F := relativeForms u p
  let G := (Scheme.Modules.pushforward g).obj F
  let B := (Scheme.Modules.pushforward f).obj G
  let α := (Scheme.Modules.pushforwardComp g f).app F
  let E := formsPushforwardEquiv hgf p q
  have he : Function.Surjective (fun z : CohomologyOn B ⊤ q =>
      E (CohomologyOn.map α.hom ⊤ q z)) := by
    intro y
    obtain ⟨v, rfl⟩ := E.surjective y
    refine ⟨CohomologyOn.map α.inv ⊤ q v, congrArg E ?_⟩
    rw [CohomologyOn.map_comp_top, α.inv_hom_id, cohomologyMap_id_top]
  obtain ⟨z, rfl⟩ := he x
  let A := SheafOfModules.toSheaf X.ringCatSheaf
  let Ay := SheafOfModules.toSheaf Y.ringCatSheaf
  let Az := SheafOfModules.toSheaf Z.ringCatSheaf
  let T := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f.base
  let z' := CohomologyOn.pushforwardComparison f G ⊤ q z
  have hα : A.map α.hom = 𝟙 (A.obj B) := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro y
    rfl
  have hcomp : formsPushforwardEquiv hg p q z' = E (CohomologyOn.map α.hom ⊤ q z) := by
    have h := abelianCohomologyPullback_comp f.base g.base
      (F := A.obj B) (G := Ay.obj G) (L := Az.obj F) (𝟙 _) (𝟙 _) (⊤ : X.Opens) q z
    rw [Functor.map_id, Category.id_comp] at h
    have h' := CohomologyOn.pullback_apply (g ≫ f) α.hom ⊤ q z
    rw [hα] at h'
    exact h.trans h'.symm
  let μ := relativeFormsTrace hg p
  let μ' := (Scheme.Modules.pushforward f).map μ
  have hμ : T.map (Ay.map μ) = A.map μ' := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro y
    rfl
  have hz : CohomologyOn.pushforwardComparison f (relativeForms t p) ⊤ q
      (CohomologyOn.map μ' ⊤ q z) = CohomologyOn.map μ ⊤ q z' := by
    have h := abelianPushforwardComparison_map f.base (Ay.map μ) (⊤ : X.Opens) q z
    rw [show (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f.base).map (Ay.map μ) =
      A.map μ' from hμ] at h
    exact h
  calc
    _ = CohomologyOn.map (relativeFormsTrace hgf p) ⊤ q (CohomologyOn.map α.hom ⊤ q z) := by
      change CohomologyOn.map (relativeFormsTrace hgf p) ⊤ q
        (E.symm (E (CohomologyOn.map α.hom ⊤ q z))) = _
      rw [E.symm_apply_apply]
    _ = CohomologyOn.map (relativeFormsTrace hf p) ⊤ q (CohomologyOn.map μ' ⊤ q z) := by
      rw [CohomologyOn.map_comp_top, CohomologyOn.map_comp_top, relativeFormsTrace_trans hf hg hgf p]
    _ = hodgeTrace hf p q (CohomologyOn.map μ ⊤ q z') := by
      rw [← hz]
      let E₀ := formsPushforwardEquiv hf p q
      change CohomologyOn.map (relativeFormsTrace hf p) ⊤ q (CohomologyOn.map μ' ⊤ q z) =
        CohomologyOn.map (relativeFormsTrace hf p) ⊤ q
          (E₀.symm (E₀ (CohomologyOn.map μ' ⊤ q z)))
      rw [E₀.symm_apply_apply]
    _ = _ := by
      rw [← hcomp]
      let E₁ := formsPushforwardEquiv hg p q
      change hodgeTrace hf p q (CohomologyOn.map μ ⊤ q z') =
        hodgeTrace hf p q (CohomologyOn.map μ ⊤ q (E₁.symm (E₁ z')))
      rw [E₁.symm_apply_apply]

end GlobalTheory.SchemeCohomology
