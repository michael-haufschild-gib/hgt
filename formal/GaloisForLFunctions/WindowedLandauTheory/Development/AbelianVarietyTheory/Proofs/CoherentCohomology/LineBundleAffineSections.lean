import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleQuasicoherent
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-! Sections of an invertible sheaf over an affine open form a finite projective module. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

/-- Local rank-one freeness on principal opens descends to finite projectivity on the affine open. -/
theorem finite_projective_sections {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(toMod L, U) ∧ Module.Projective Γ(X, U) Γ(toMod L, U) := by
  let F := toMod L
  letI : F.IsQuasicoherent := isQuasicoherent_toMod hL
  let s : Set Γ(X, U) := {g | ∃ j, X.basicOpen g ≤ L.U j}
  have hs : Ideal.span s = ⊤ := hU.self_le_iSup_basicOpen_iff.mp (by
    intro x hx
    have hx' : x ∈ ⨆ j, L.U j := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx'
    obtain ⟨g, hg, hxg⟩ := hU.exists_basicOpen_le ⟨x, hj⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨g, j, hg⟩, hxg⟩)
  let B (g : s) := Γ(X, X.basicOpen g.1)
  let V (g : s) := Γ(F, X.basicOpen g.1)
  letI (g : s) : Algebra Γ(X, U) (B g) := Scheme.algebra_section_section_basicOpen g.1
  letI (g : s) : Module Γ(X, U) (V g) := Module.compHom _ (algebraMap Γ(X, U) (B g))
  letI (g : s) : IsScalarTower Γ(X, U) (B g) (V g) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI (g : s) : IsLocalization.Away g.1 (B g) := hU.isLocalization_basicOpen g.1
  let localize (g : s) : Γ(F, U) →ₗ[Γ(X, U)] V g :=
    let i := homOfLE (X.basicOpen_le g.1)
    { (F.presheaf.map i.op).hom with
      map_smul' := fun a v => F.map_smul i a v }
  haveI (g : s) : IsLocalizedModule.Away g.1 (localize g) := by
    have h := hasBasicOpenLocalization_of_isQuasicoherent F hU g.1
    refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun v => ?_) h.2
    · rw [Module.End.isUnit_iff]
      change Function.Bijective
        (algebraMap (B g) (Module.End (B g) (V g)) (algebraMap Γ(X, U) (B g) g.1))
      rw [← Module.End.isUnit_iff]
      exact (IsLocalization.Away.algebraMap_isUnit (S := B g) g.1).map _
    · obtain ⟨n, a, ha⟩ := h.1 v
      refine ⟨n, a, ?_⟩
      change (algebraMap Γ(X, U) (B g) (g.1 ^ n)) • v = _
      rw [map_pow]
      exact ha
  have hfree (g : s) : Module.Free (B g) (V g) := by
    obtain ⟨j, hj⟩ := g.2
    exact Module.Free.of_equiv (chartEquiv hL j hj).symm
  haveI (g : s) : Module.Finite (B g) (V g) := by
    obtain ⟨j, hj⟩ := g.2
    let e := (chartEquiv hL j hj).symm
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  haveI : Module.FinitePresentation Γ(X, U) Γ(F, U) :=
    Module.FinitePresentation.of_localizationSpan' (Rₚ := fun g => B g) s hs localize fun g => by
      letI := hfree g
      exact Module.finitePresentation_of_projective (B g) (V g)
  haveI : Module.Flat Γ(X, U) Γ(F, U) :=
    Module.flat_of_isLocalized_span (R := Γ(X, U)) Γ(X, U) Γ(F, U) s hs
      (fun g => V g) localize fun g => by
        letI := hfree g
        letI : Module.Flat Γ(X, U) (B g) := IsLocalization.flat (B g) (Submonoid.powers g.1)
        exact Module.Flat.trans Γ(X, U) (B g) (V g)
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.LineBundleSections
