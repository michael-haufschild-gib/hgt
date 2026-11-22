import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineModuleMorphisms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineFiniteEtaleTrace

/-! The affine traces of forms glue to a sheaf trace for a finite étale morphism. -/

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {f : Y ⟶ X} [IsFinite f] [Etale f]

private def affineTraceOnSections (hf : f ≫ s = t) (n : ℕ) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Γ((Scheme.Modules.pushforward f).obj (relativeForms t n), U) →ₗ[Γ(X, U)]
      Γ(relativeForms s n, U) where
  toFun y := formsOnToSections s n U
    (affineFormTrace hf hU n ((affineFormsSections t n (hU.preimage f)).symm y))
  map_add' y z := ((formsOnToSections s n U).toAddMonoidHom.comp
    ((affineFormTrace hf hU n).comp (affineFormsSections t n (hU.preimage f)).symm.toAddMonoidHom)
      ).map_add y z
  map_smul' r y := by
    let E := affineFormsSections t n (hU.preimage f)
    change formsOnToSections s n U
      (affineFormTrace hf hU n (E.symm (sectionPullback hf U r •
        (show Γ(relativeForms t n, f ⁻¹ᵁ U) from y)))) =
      (show SectionRing s U from r) • formsOnToSections s n U (affineFormTrace hf hU n (E.symm y))
    rw [E.symm.map_smul, affineFormTrace_smul, LinearMap.map_smul]

private theorem affineTraceOnSections_apply (hf : f ≫ s = t) (n : ℕ) {U : X.Opens}
    (hU : IsAffineOpen U) (ω : FormsOn t (f ⁻¹ᵁ U) n) :
    affineTraceOnSections hf n hU (formsOnToSections t n (f ⁻¹ᵁ U) ω) =
      formsOnToSections s n U (affineFormTrace hf hU n ω) :=
  congrArg (fun x => formsOnToSections s n U (affineFormTrace hf hU n x))
    ((affineFormsSections t n (hU.preimage f)).symm_apply_apply ω)

private theorem affineTraceOnSections_res (hf : f ≫ s = t) (n : ℕ) {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ⟶ U)
    (y : Γ((Scheme.Modules.pushforward f).obj (relativeForms t n), U)) :
    (relativeForms s n).presheaf.map i.op (affineTraceOnSections hf n hU y) =
      affineTraceOnSections hf n hV
        (((Scheme.Modules.pushforward f).obj (relativeForms t n)).presheaf.map i.op y) := by
  obtain ⟨ω, hω⟩ := (affineFormsSections t n (hU.preimage f)).surjective y
  change formsOnToSections t n (f ⁻¹ᵁ U) ω = y at hω
  rw [← hω, affineTraceOnSections_apply, formsOnToSections_res]
  have h := formsOnToSections_res t n ((TopologicalSpace.Opens.map f.base).map i) ω
  change ((Scheme.Modules.pushforward f).obj (relativeForms t n)).presheaf.map i.op
    (formsOnToSections t n (f ⁻¹ᵁ U) ω) =
      formsOnToSections t n (f ⁻¹ᵁ V)
        (ExteriorDifferentials.map (sectionRes t ((TopologicalSpace.Opens.map f.base).map i)) n ω) at h
  rw [h, affineTraceOnSections_apply, affineFormTrace_res hf hU hV]

/-- Trace on relative forms along a finite étale map of schemes over the base. -/
def relativeFormsTrace (hf : f ≫ s = t) (n : ℕ) :
    (Scheme.Modules.pushforward f).obj (relativeForms t n) ⟶ relativeForms s n :=
  homOfAffineSections (fun U => affineTraceOnSections hf n U.prop)
    (fun U V i => affineTraceOnSections_res hf n U.prop V.prop i)

theorem relativeFormsTrace_app (hf : f ≫ s = t) (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (ω : FormsOn t (f ⁻¹ᵁ U) n) :
    (relativeFormsTrace hf n).app U (formsOnToSections t n (f ⁻¹ᵁ U) ω) =
      formsOnToSections s n U (affineFormTrace hf hU n ω) :=
  (homOfAffineSections_app _ _ ⟨U, hU⟩ _).trans (affineTraceOnSections_apply hf n hU ω)

omit [IsFinite f] [Etale f] in
theorem relativeFormsPullback_app (hf : f ≫ s = t) (n : ℕ) (U : X.Opens) (ω : FormsOn s U n) :
    (relativeFormsPullback hf n).app U (formsOnToSections s n U ω) =
      formsOnToSections t n (f ⁻¹ᵁ U) (ExteriorDifferentials.map (sectionPullback hf U) n ω) := by
  let L := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let M := (Scheme.Modules.pushforward f).obj (relativeForms t n)
  have h := L.homEquiv_unit (X := formsPresheaf s n) (Y := M) (relativeFormsPullback hf n)
  have e := congrArg (fun α => (α.app (op U)).hom ω) h
  rw [relativeFormsPullback, Equiv.apply_symm_apply] at e
  exact e.symm

private theorem nsmul_moduleHom_app {F G : X.Modules} (a : F ⟶ G) (d : ℕ)
    (U : X.Opens) (x : Γ(F, U)) : (d • a).app U x = d • a.app U x := by
  induction d with
  | zero => rw [zero_smul, zero_smul]; rfl
  | succ m ih =>
    rw [succ_nsmul, succ_nsmul, Scheme.Modules.Hom.add_app]
    exact congrArg (fun y => y + a.app U x) ih

/-- Trace after pullback multiplies by the trace of the unit, when this trace is constant. -/
theorem relativeFormsTrace_comp_pullback (hf : f ≫ s = t) (n d : ℕ)
    (hd : ∀ (U : X.Opens) (hU : IsAffineOpen U), affineSectionTrace (f := f) s t hU 1 = d) :
    relativeFormsPullback hf n ≫ relativeFormsTrace hf n = d • 𝟙 (relativeForms s n) := by
  apply moduleHom_ext_affine
  intro U hU y
  obtain ⟨ω, rfl⟩ := (affineFormsSections s n hU).surjective y
  change (relativeFormsPullback hf n ≫ relativeFormsTrace hf n).app U
      (formsOnToSections s n U ω) = _
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, relativeFormsPullback_app,
    relativeFormsTrace_app hf n hU]
  have h := affineFormTrace_smul_pullback hf hU n (1 : SectionRing t (f ⁻¹ᵁ U)) ω
  rw [one_smul, hd U hU] at h
  rw [h, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_moduleHom_app]
  rfl

end GlobalTheory.SchemeCohomology
