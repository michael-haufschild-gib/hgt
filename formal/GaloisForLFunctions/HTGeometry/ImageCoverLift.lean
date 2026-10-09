import GaloisForLFunctions.HTGeometry.SubgroupCover
import GaloisForLFunctions.HTGeometry.UniversalCoverDeckGroup

/-!
# Lifting a map onto the fundamental group of its exact image cover

Equality of the source and covering fundamental-group images upgrades the
covering-space lifting criterion: the resulting lift induces a surjection.
Combined with the subgroup-cover construction, this factors each continuous map
through an actual cover representing its exact image.
-/

open Topology Set Function

namespace GaloisForLFunctions.HTGeometry

/-- A covering induces an injective map on fundamental groups, with a chosen target basepoint. -/
theorem fundamentalGroup_mapOfEq_injective_of_covering
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) {e : E} {b : B} (he : p e = b) :
    Injective (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he) := by
  subst b
  intro γ δ h
  apply hp.injective_path_homotopic_map e e
  simpa only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl] using! h

/-- Lifting to a cover with exactly the source image makes the lifted fundamental-group map onto. -/
theorem exists_surjective_fundamentalGroup_lift
    {A E B : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {p : E → B} (hp : IsCoveringMap p) (f : C(A, B)) (a : A) (e : E)
    (he : p e = f a)
    (hrange : (FundamentalGroup.map f a).range =
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range) :
    ∃ F : C(A, E), ∃ hF : F a = e, p ∘ F = f ∧
      Surjective (FundamentalGroup.mapOfEq F hF) := by
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := hp.existsUnique_continuousMap_lifts_of_range_le he hrange.le
  refine ⟨F, hF0, hF, ?_⟩
  have hcomp : (⟨p, hp.continuous⟩ : C(E, B)).comp F = f :=
    ContinuousMap.ext (congrFun hF)
  subst e
  subst f
  intro δ
  obtain ⟨γ, hγ⟩ := hrange.ge ⟨δ, rfl⟩
  refine ⟨γ, ?_⟩
  apply fundamentalGroup_mapOfEq_injective_of_covering hp rfl
  rw [FundamentalGroup.map_apply, FundamentalGroup.mapOfEq_apply] at hγ
  simp only [FundamentalGroup.mapOfEq_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Path.Homotopic.Quotient.cast_rfl_rfl, ← Path.Homotopic.Quotient.map_comp] at hγ ⊢
  exact hγ

/-- Every source map factors through its exact image cover, with a lift onto fundamental groups. -/
theorem exists_subgroup_cover_lift_surjective_fundamentalGroup
    {A E B G : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] [LocallyConnectedSpace B]
    [SimplyConnectedSpace E] [Group G] [MulAction G E]
    {p : E → B} (hp : IsQuotientCoveringMap p G)
    (f : C(A, B)) (a : A) (e : p ⁻¹' {f a}) :
    ∃ H : Subgroup G, ∃ F : C(A, SubgroupCover (E := E) H),
      ∃ hF : F a = Quotient.mk (MulAction.orbitRel H E) e.val,
      subgroupCoverProjection hp H ∘ F = f ∧
      Surjective (FundamentalGroup.mapOfEq F hF) := by
  let H := ((FundamentalGroup.map f a).range.map
    (hp.fundamentalGroupToMulOpposite e)).unop
  have he : subgroupCoverProjection hp H (Quotient.mk _ e.val) = f a := e.property
  have hrange : (FundamentalGroup.map f a).range =
      (FundamentalGroup.mapOfEq (x := Quotient.mk (MulAction.orbitRel H E) e.val)
        ⟨subgroupCoverProjection hp H, (isCoveringMap_subgroupCoverProjection hp H).continuous⟩
        he).range :=
    (fundamentalGroup_range_prescribed_subgroup hp e (FundamentalGroup.map f a).range).symm
  obtain ⟨F, hF, hcomp, hsurj⟩ := exists_surjective_fundamentalGroup_lift
    (isCoveringMap_subgroupCoverProjection hp H) f a (Quotient.mk _ e.val) he hrange
  exact ⟨H, F, hF, hcomp, hsurj⟩

/-- The intrinsic deck group gives the same exact-image factorization from any universal cover. -/
theorem exists_universal_cover_image_factorization
    {A E B : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] [LocallyConnectedSpace B]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → B} (hp : IsCoveringMap p) (hsurj : Surjective p)
    (f : C(A, B)) (a : A) (e : p ⁻¹' {f a}) :
    let hd := isQuotientCoveringMap_coveringDeckGroup hp hsurj
    ∃ H : Subgroup (coveringDeckGroup p), ∃ F : C(A, SubgroupCover (E := E) H),
      ∃ hF : F a = Quotient.mk (MulAction.orbitRel H E) e.val,
      subgroupCoverProjection hd H ∘ F = f ∧
      Surjective (FundamentalGroup.mapOfEq F hF) :=
  exists_subgroup_cover_lift_surjective_fundamentalGroup
    (isQuotientCoveringMap_coveringDeckGroup hp hsurj) f a e

end GaloisForLFunctions.HTGeometry
