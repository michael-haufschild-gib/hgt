import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.DualNumberTangentCriteria
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Unramified.LocalStructure

/-! Geometric dual-number lifts give scheme-theoretic smoothness
and unramifiedness criteria. -/

noncomputable section

namespace GlobalTheory.TangentCrit

open AlgebraicGeometry CategoryTheory Limits

universe u

abbrev dualPt (k : Type u) [CommRing k] : Spec (.of k) ⟶ Spec (.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

abbrev dualBase (k : Type u) [CommRing k] : Spec (.of (DualNumber k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

@[reassoc]
lemma dualPt_dualBase (k : Type u) [CommRing k] : dualPt k ≫ dualBase k = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

/-- A morphism is formally unramified if every geometric tangent
vector which it sends to a constant vector is constant. -/
theorem formallyUnramified_of_tangent {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (w : Spec (.of (DualNumber k)) ⟶ X),
      w ≫ f = dualBase k ≫ dualPt k ≫ w ≫ f → w = dualBase k ≫ dualPt k ≫ w) :
    FormallyUnramified f := by
  refine ⟨fun {U} hU {V} hV e => formallyUnramified_of_dual_const _
    (f.finiteType_appLE hU hV e).essFiniteType fun k _ _ φ hφ b => ?_⟩
  have := H k (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) (by
    simp only [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV e, ← Spec.map_comp_assoc]
    congr 2
    ext a
    · rfl
    · exact hφ a)
  simp only [← Spec.map_comp_assoc] at this
  rw [cancel_mono, Spec.map_inj] at this
  exact congrArg TrivSqZeroExt.snd congr($this b)

/-- Local finite presentation cancels against a locally finite type
base morphism. -/
theorem locallyOfFinitePresentation_of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S)
    [LocallyOfFinitePresentation (f ≫ π)] [LocallyOfFiniteType π] :
    LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).1]
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π (f x))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW : U ≤ π ⁻¹ᵁ W⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxW (π ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, RingHom.FinitePresentation.of_comp_finiteType
    (π.appLE W U hUW).hom ?_ (π.finiteType_appLE hW hU hUW)⟩
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  exact (f ≫ π).finitePresentation_appLE hW hV _

theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  refine ⟨fun {U} hU {V} hV e => ?_⟩
  have h₁ := f.formallyUnramified_appLE hU hV e
  have h₂ := f.finiteType_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

private lemma SpecMap_fromSpecStalk_closedPoint {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}}
    [IsLocalRing R] (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint R) = x := by
  exact (Scheme.Hom.comp_apply _ _ _).trans
    ((congrArg (X.fromSpecStalk x) Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)

/-- Relative tangent lifts over a base imply smoothness when
the source is smooth over that base. -/
theorem smooth_of_tangent {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) [Smooth (f ≫ π)]
    [LocallyOfFiniteType π]
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
      (v : Spec (.of (DualNumber k)) ⟶ Y), dualPt k ≫ v = x ≫ f → v ≫ π = dualBase k ≫ x ≫ f ≫ π →
      ∃ w : Spec (.of (DualNumber k)) ⟶ X, dualPt k ≫ w = x ∧ w ≫ f = v) :
    Smooth f := by
  have := locallyOfFinitePresentation_of_comp f π
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro x -
  let k := AlgebraicClosure (IsLocalRing.ResidueField (X.presheaf.stalk x))
  let ξ : X.presheaf.stalk x →+* k := (algebraMap _ k).comp (IsLocalRing.residue _)
  have hξ : IsLocalHom ξ := inferInstance
  have e : (f.stalkMap x).hom.comp (π.stalkMap (f x)).hom = ((f ≫ π).stalkMap x).hom := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  refine formallySmooth_of_dual_lift (π.stalkMap (f x)).hom (f.stalkMap x).hom
    (LocallyOfFiniteType.stalkMap π _) (e ▸ LocallyOfFiniteType.stalkMap (f ≫ π) x)
    (e ▸ (f ≫ π).smoothLocus_eq_top.ge (Set.mem_univ x)) ξ fun ψ h₁ h₂ => ?_
  obtain ⟨w, hw₁, hw₂⟩ := H k (Spec.map (CommRingCat.ofHom ξ) ≫ X.fromSpecStalk x)
    (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk (f x)) (by
      simp only [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
      congr 2
      ext a
      exact h₁ a) (by
      rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc,
        ← Scheme.SpecMap_stalkMap_fromSpecStalk]
      simp only [← Spec.map_comp_assoc]
      congr 2
      ext a
      · exact h₁ _
      · exact h₂ a)
  obtain ⟨⟨y, φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (.of (DualNumber k))).symm.surjective w
  change _ ≫ Spec.map φ ≫ X.fromSpecStalk y = _ at hw₁
  change (Spec.map φ ≫ X.fromSpecStalk y) ≫ f = _ at hw₂
  rw [← Spec.map_comp_assoc] at hw₁
  obtain rfl : y = x := by
    have h₃ : IsLocalHom (CommRingCat.ofHom ξ).hom := hξ
    have h₄ : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom).hom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
    have h₅ : IsLocalHom (φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom).hom :=
      RingHom.isLocalHom_comp _ _
    exact (SpecMap_fromSpecStalk_closedPoint _).symm.trans
      ((congrArg (fun g : Spec (.of k) ⟶ X => g (IsLocalRing.closedPoint k)) hw₁).trans
        (SpecMap_fromSpecStalk_closedPoint _))
  rw [cancel_mono, Spec.map_inj] at hw₁
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc, cancel_mono,
    Spec.map_inj] at hw₂
  exact ⟨φ.hom, fun b => congr($hw₁ b), fun a => congr($hw₂ a)⟩

end GlobalTheory.TangentCrit
