import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BiproductSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RelativeFormsTrace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Relative forms decompose over a finite partition into clopen subschemes. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [CommRing K] {X : Scheme.{0}} {J : Type} [Fintype J]
  (s : X ⟶ Spec (CommRingCat.of K)) (U : J → X.Opens)

/-- The pushforward of the relative forms on a clopen component. -/
abbrev clopenForms (p : ℕ) (i : J) : X.Modules :=
  (Scheme.Modules.pushforward (U i).ι).obj (relativeForms ((U i).ι ≫ s) p)

private def clopenFormsMap (p : ℕ) : relativeForms s p ⟶ ⨁ clopenForms s U p :=
  biproduct.lift fun i => relativeFormsPullback (f := (U i).ι) rfl p

private theorem forms_pullback_bijective_on_affine {Y : Scheme.{0}}
    {f : Y ⟶ X} [IsOpenImmersion f] {t : Y ⟶ Spec (CommRingCat.of K)} (hf : f ≫ s = t)
    {V : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen (f ⁻¹ᵁ V))
    (hle : V ≤ f.opensRange) (p : ℕ) :
    Function.Bijective ((relativeFormsPullback hf p).app V) := by
  letI := f.isIso_app V hle
  let e := AlgEquiv.ofBijective (sectionPullback hf V)
    (ConcreteCategory.bijective_of_isIso (f.app V))
  let a := affineFormsSections s p hV
  let b := affineFormsSections t p hW
  have he : Function.Bijective (ExteriorDifferentials.map e.toAlgHom p) := by
    let E := ExteriorDifferentials.map e.toAlgHom p
    let G := ExteriorDifferentials.map e.symm.toAlgHom p
    have hleft : Function.LeftInverse G E := by
      intro x
      change ExteriorDifferentials.map e.symm.toAlgHom p (ExteriorDifferentials.map e.toAlgHom p x) = x
      rw [← ExteriorDifferentials.map_comp, AlgEquiv.symm_comp, ExteriorDifferentials.map_id]
    have hright : Function.RightInverse G E := by
      intro x
      change ExteriorDifferentials.map e.toAlgHom p (ExteriorDifferentials.map e.symm.toAlgHom p x) = x
      rw [← ExteriorDifferentials.map_comp, AlgEquiv.comp_symm, ExteriorDifferentials.map_id]
    exact ⟨hleft.injective, hright.surjective⟩
  have h : ((relativeFormsPullback hf p).app V : Γ(relativeForms s p, V) → _) =
      b ∘ ExteriorDifferentials.map e.toAlgHom p ∘ a.symm := by
    funext x
    obtain ⟨y, rfl⟩ := a.surjective x
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
    exact relativeFormsPullback_app hf p V y
  rw [h]
  exact b.bijective.comp (he.comp a.symm.bijective)

private theorem clopenFormsMap_isIso (p : ℕ)
    (hclosed : ∀ i, IsClosed (U i : Set X))
    (hdis : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : iSup U = ⊤) :
    IsIso (clopenFormsMap s U p) := by
  classical
  let A : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat X := SheafOfModules.toSheaf X.ringCatSheaf
  letI : A.ReflectsIsomorphisms :=
    inferInstanceAs ((SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms)
  apply (isIso_iff_of_reflects_iso (clopenFormsMap s U p) A).mp
  let V : {W : X.Opens // IsAffineOpen W ∧ ∃ i, W ≤ U i} → X.Opens := Subtype.val
  have hV : Opens.IsBasis (Set.range V) := by
    refine Opens.isBasis_iff_nbhd.2 fun {W x} hx => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ x))
    obtain ⟨T, hT, hxT, hTW⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ W ⊓ U i from ⟨hx, hi⟩)
    exact ⟨T, ⟨⟨T, hT, i, hTW.trans inf_le_right⟩, rfl⟩, hxT, hTW.trans inf_le_left⟩
  apply TopCat.Sheaf.isIso_iff_isIso_basis hV
  rintro ⟨W, hW, i, hWi⟩
  haveI : IsClosedImmersion (U i).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hclosed i)
  let g (j : J) := relativeFormsPullback (f := (U j).ι) (s := s) rfl p
  have hb : Function.Bijective ((g i).app W) :=
    forms_pullback_bijective_on_affine s rfl hW (hW.preimage (U i).ι)
      (by simpa only [Scheme.Opens.opensRange_ι] using hWi) p
  have hsub (j : J) (hji : j ≠ i) : Subsingleton Γ(clopenForms s U p j, W) := by
    have hEmpty : (U j).ι ⁻¹ᵁ W = ⊥ := by
      refine le_antisymm (fun x hx => ?_) bot_le
      have hh : (U j).ι x ∈ U j ⊓ U i := ⟨x.2, hWi hx⟩
      rw [hdis j i hji] at hh
      exact hh.elim
    let t := (U j).ι ≫ s
    let F := (SheafOfModules.toSheaf (U j).toScheme.ringCatSheaf).obj (relativeForms t p)
    exact AddCommGrpCat.isZero_iff_subsingleton.mp
      (TopCat.Sheaf.isTerminalOfEqEmpty F hEmpty).isZero
  let E := sectionsBiproductEquiv (clopenForms s U p) W
  have hcoord (x : Γ(relativeForms s p, W)) (j : J) :
      E ((clopenFormsMap s U p).app W x) j = (g j).app W x :=
    (sectionsBiproductEquiv_apply _ _ _ _).trans
      (congrArg (fun a => a.app W x) (biproduct.lift_π g j))
  apply (ConcreteCategory.isIso_iff_bijective (f := _)).2
  change Function.Bijective ((clopenFormsMap s U p).app W)
  constructor
  · intro a b h
    apply hb.injective
    exact (hcoord a i).symm.trans ((congrArg (fun y => E y i) h).trans (hcoord b i))
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective (E y i)
    refine ⟨x, E.injective ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      exact (hcoord x i).trans hx
    · exact (hsub j hji).elim _ _

/-- Restrictions into the clopen components identify the sheaf with the
direct sum of their direct images. -/
def clopenFormsIso (p : ℕ) (hclosed : ∀ i, IsClosed (U i : Set X))
    (hdis : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : iSup U = ⊤) :
    relativeForms s p ≅ ⨁ clopenForms s U p :=
  letI := clopenFormsMap_isIso s U p hclosed hdis hcov
  asIso (clopenFormsMap s U p)

theorem clopenFormsIso_hom_π (p : ℕ) (hclosed : ∀ i, IsClosed (U i : Set X))
    (hdis : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : iSup U = ⊤) (i : J) :
    (clopenFormsIso s U p hclosed hdis hcov).hom ≫ biproduct.π (clopenForms s U p) i =
      relativeFormsPullback (f := (U i).ι) rfl p :=
  biproduct.lift_π _ _

end GlobalTheory.SchemeCohomology
