import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! The basic-open localization criterion for quasi-coherence on an affine cover. -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {X : Scheme.{u}} (F : X.Modules)

/-- On a basic open, every section comes from the ambient open after clearing
denominators, and a section in the kernel is killed by a power of the denominator. -/
def HasBasicOpenLocalization (U : X.Opens) (f : Γ(X, U)) : Prop :=
  let i := homOfLE (X.basicOpen_le f)
  (∀ s : Γ(F, X.basicOpen f), ∃ (n : ℕ) (t : Γ(F, U)),
    (X.presheaf.map i.op f) ^ n • s = F.presheaf.map i.op t) ∧
  (∀ t : Γ(F, U), F.presheaf.map i.op t = 0 → ∃ n : ℕ, f ^ n • t = 0)

private theorem fromSpec_image_le {U : X.Opens} (hU : IsAffineOpen U)
    (W : (Spec Γ(X, U)).Opens) : hU.fromSpec ''ᵁ W ≤ U :=
  (hU.fromSpec.image_le_opensRange W).trans hU.opensRange_fromSpec.le

private theorem fromSpec_smul {U : X.Opens} (hU : IsAffineOpen U)
    (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U))
    (z : Γ(F.restrict hU.fromSpec, W)) :
    (F.restrictAppIso hU.fromSpec W).hom (r • z) =
      X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r •
        (F.restrictAppIso hU.fromSpec W).hom z := by
  have h :
      X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op ≫ (hU.fromSpec.appIso W).hom =
        (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map W.leTop.op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE, hU.fromSpec_app_self,
      Category.assoc, ← Functor.map_comp]
    rfl
  have hr :
      (hU.fromSpec.appIso W).inv
        ((Spec Γ(X, U)).presheaf.map W.leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r)) =
        X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Category.assoc, ← h]
    simp
  rw [← hr]
  rfl

/-- On an affine open, quasi-coherence is equivalent to localization on basic opens. -/
theorem isQuasicoherent_fromSpec_iff_localization {U : X.Opens} (hU : IsAffineOpen U) :
    (F.restrict hU.fromSpec).IsQuasicoherent ↔
      ∀ f : Γ(X, U), HasBasicOpenLocalization F U f := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ,
    isIso_fromTildeΓ_iff_isLocalizing]
  refine forall_congr' fun f => ?_
  let W := PrimeSpectrum.basicOpen f
  let φ := ((modulesSpecToSheaf.obj (F.restrict hU.fromSpec)).obj.map W.leTop.op).hom
  change IsLocalizedModule.Away f φ ↔ _
  have ht : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have hb : hU.fromSpec ''ᵁ W = X.basicOpen f := hU.fromSpec_image_basicOpen f
  have key (U' V' : X.Opens) (r : U' ≤ U) (i : V' ≤ U') (e : U' = U)
      (e' : V' = X.basicOpen f) : HasBasicOpenLocalization F U f ↔
      ((∀ s : Γ(F, V'), ∃ (n : ℕ) (t : Γ(F, U')),
        X.presheaf.map (homOfLE (i.trans r)).op (f ^ n) • s =
          F.presheaf.map (homOfLE i).op t) ∧
      (∀ t : Γ(F, U'), F.presheaf.map (homOfLE i).op t = 0 →
        ∃ n : ℕ, X.presheaf.map (homOfLE r).op (f ^ n) • t = 0)) := by
    subst U' V'
    have hr : (homOfLE r).op = 𝟙 (op U) := rfl
    simp only [HasBasicOpenLocalization, hr, X.presheaf.map_id, map_pow]
    rfl
  rw [key _ _ (fromSpec_image_le hU _) (hU.fromSpec.image_mono le_top) ht hb]
  constructor
  · intro h
    refine ⟨fun z => ?_, fun z hz => ?_⟩
    · obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj φ f z
      exact ⟨n, t, (fromSpec_smul F hU _ (f ^ n) z).symm.trans ht⟩
    · have hz' : φ z = φ 0 := hz.trans (map_zero φ).symm
      obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (f := φ) f (x := z) (y := 0) hz'
      rw [smul_zero] at hn
      exact ⟨n, (fromSpec_smul F hU _ (f ^ n) z).symm.trans hn⟩
  · rintro ⟨hs, hk⟩
    refine IsLocalizedModule.Away.mk_of_addCommGroup (f := φ)
      (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl) ?_ ?_
    · intro z
      obtain ⟨n, t, ht⟩ := hs z
      exact ⟨n, t, (fromSpec_smul F hU _ (f ^ n) z).trans ht⟩
    · intro z hz
      obtain ⟨n, hn⟩ := hk z hz
      exact ⟨n, (fromSpec_smul F hU _ (f ^ n) z).trans hn⟩

/-- Localizing a quasi-coherent sheaf on any basic open computes its sections there. -/
theorem hasBasicOpenLocalization_of_isQuasicoherent [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) : HasBasicOpenLocalization F U f :=
  (isQuasicoherent_fromSpec_iff_localization F hU).mp inferInstance f

set_option backward.isDefEq.respectTransparency false in
/-- The basic-open localization criterion applied on an affine cover. -/
theorem isQuasicoherent_of_affineCover_localization {ι : Type u}
    (U : ι → X.Opens) (hcov : IsOpenCover U) (haff : ∀ i, IsAffineOpen (U i))
    (hloc : ∀ i (f : Γ(X, U i)), HasBasicOpenLocalization F (U i) f) :
    F.IsQuasicoherent := by
  let presentation (i : ι) : (F.over (U i)).Presentation := by
    let hU := haff i
    let M := F.restrict hU.fromSpec
    haveI : M.IsQuasicoherent := (isQuasicoherent_fromSpec_iff_localization F hU).mpr (hloc i)
    haveI := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
    let P : M.Presentation := SheafOfModules.Presentation.ofIsIso M.fromTildeΓ
      (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _))
    let iso : Scheme.Modules.restrictFunctor hU.fromSpec ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom ≅ Scheme.Modules.restrictFunctor (U i).ι :=
      (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
        Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec
    let Q : (F.restrict (U i).ι).Presentation := SheafOfModules.Presentation.ofIsIso (iso.app F).hom
      (Scheme.Modules.presentationRestrict hU.isoSpec.hom P)
    let e := Scheme.Modules.overEquiv (U i)
    haveI : Limits.PreservesColimitsOfSize.{u, u} e.inverse := inferInstance
    let overIso : e.inverse.obj (F.restrict (U i).ι) ≅ F.over (U i) :=
      e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv (U i)).app F).symm ≪≫
        (e.unitIso.app (F.over (U i))).symm
    exact SheafOfModules.Presentation.ofIsIso overIso.hom
      (Q.map e.inverse ((U i).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm)
  refine SheafOfModules.QuasicoherentData.isQuasicoherent (M := F)
    { I := ι, X := U, coversTop := ?_, presentation := presentation }
  rwa [Opens.coversTop_iff]

end GlobalTheory.SchemeCohomology
