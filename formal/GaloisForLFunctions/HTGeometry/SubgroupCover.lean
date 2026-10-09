import GaloisForLFunctions.HTGeometry.CoveringRightCancellation
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Algebra.Group.Subgroup.MulOpposite

/-!
# Intermediate coverings with prescribed fundamental-group image

A subgroup of the acting group of a quotient covering defines an intermediate
orbit covering. Its induced fundamental-group image is the inverse image of the
opposite subgroup under deck monodromy. When the original source is simply
connected, this realizes every subgroup of the base fundamental group.
-/

open Topology Set Function

namespace GaloisForLFunctions.HTGeometry

variable {E B G : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [Group G] [MulAction G E] {p : E → B}

/-- The orbit space for a subgroup of the deck action, with quotient topology. -/
abbrev SubgroupCover (H : Subgroup G) := Quotient (MulAction.orbitRel H E)

/-- The natural projection from a subgroup orbit quotient to the original base. -/
def subgroupCoverProjection (hp : IsQuotientCoveringMap p G) (H : Subgroup G) :
    SubgroupCover (E := E) H → B :=
  Quotient.lift p fun _ _ h => by
    obtain ⟨g, rfl⟩ := h
    exact hp.map_smul (g : G)

@[simp] theorem subgroupCoverProjection_mk (hp : IsQuotientCoveringMap p G)
    (H : Subgroup G) (e : E) : subgroupCoverProjection hp H (Quotient.mk (MulAction.orbitRel H E) e) = p e := rfl

/-- Restricting the acting group retains the quotient-covering property. -/
theorem isQuotientCoveringMap_subgroupQuotient (hp : IsQuotientCoveringMap p G)
    (H : Subgroup G) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel H E) : E → SubgroupCover (E := E) H) H where
  __ := isQuotientMap_quotient_mk'
  continuous_const_smul h := hp.continuous_const_smul (h : G)
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint e := by
    obtain ⟨U, hU, hd⟩ := hp.disjoint e
    refine ⟨U, hU, fun h hh => Subtype.ext ?_⟩
    exact hd (h : G) hh

/-- Distinct subgroup orbits in the same original fiber have disjoint neighborhoods. -/
theorem isSeparatedMap_subgroupCoverProjection (hp : IsQuotientCoveringMap p G)
    (H : Subgroup G) : IsSeparatedMap (subgroupCoverProjection hp H) := by
  letI := hp.toContinuousConstSMul
  let r : E → SubgroupCover (E := E) H := Quotient.mk (MulAction.orbitRel H E)
  have hr := isQuotientCoveringMap_subgroupQuotient hp H
  intro x y hxy hne
  induction x using Quotient.inductionOn with | _ e =>
  induction y using Quotient.inductionOn with | _ e' =>
  obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.mp hxy
  change g • e' = e at hg
  obtain ⟨U, hU, hd⟩ := hp.disjoint e'
  obtain ⟨V, hVU, hVo, he'V⟩ := mem_nhds_iff.mp hU
  refine ⟨r '' ((g • ·) '' V), r '' V,
    hr.isCoveringMap.isOpenMap _ (isOpenMap_smul g V hVo),
    hr.isCoveringMap.isOpenMap _ hVo, ?_, ?_, ?_⟩
  · exact ⟨e, ⟨e', he'V, hg⟩, rfl⟩
  · exact ⟨e', he'V, rfl⟩
  · rw [disjoint_left]
    rintro z ⟨_, ⟨u, hu, rfl⟩, hzu⟩ ⟨v, hv, hzv⟩
    have huv : r (g • u) = r v := hzu.trans hzv.symm
    obtain ⟨h, hh⟩ := Quotient.eq''.mp huv
    change (h : G) • v = g • u at hh
    have heq : g⁻¹ * (h : G) = 1 := hd _
      ⟨u, ⟨v, hVU hv, by simp only [mul_smul, hh, inv_smul_smul]⟩, hVU hu⟩
    have hhg : (h : G) = g := by simpa only [inv_mul_eq_one, eq_comm] using heq
    apply hne
    apply Quotient.sound
    refine ⟨h, ?_⟩
    change (h : G) • e' = e
    rw [hhg, hg]

/-- The subgroup quotient is an intermediate covering over a locally connected base. -/
theorem isCoveringMap_subgroupCoverProjection [LocallyConnectedSpace B]
    (hp : IsQuotientCoveringMap p G) (H : Subgroup G) :
    IsCoveringMap (subgroupCoverProjection hp H) := by
  have hr := isQuotientCoveringMap_subgroupQuotient hp H
  exact isCoveringMap_of_comp_right_of_isSeparatedMap
    (r := Quotient.mk (MulAction.orbitRel H E)) hp.isCoveringMap
    hr.isCoveringMap.isLocalHomeomorph hr.surjective
    (isSeparatedMap_subgroupCoverProjection hp H)

/-- A loop lies in the induced fundamental-group image exactly when its lift closes. -/
theorem mem_fundamentalGroup_range_iff_monodromy_eq
    (hp : IsCoveringMap p) {b : B} (e : p ⁻¹' {b})
    (γ : FundamentalGroup B b) :
    γ ∈ (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.property).range ↔
      hp.monodromy γ e = e := by
  constructor
  · rintro ⟨δ, rfl⟩
    apply hp.monodromy_eq_of_map_eq δ
    simp [FundamentalGroup.mapOfEq_apply]
  · intro h
    refine ⟨(hp.liftPathQuotient γ e).cast rfl (congrArg Subtype.val h.symm), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply,
      Path.Homotopic.Quotient.map_cast, IsCoveringMap.map_liftPathQuotient]
    simp

/-- Monodromy commutes with a continuous map between covering spaces over the same base. -/
theorem monodromy_comp_val {Y : Type*} [TopologicalSpace Y]
    {r : E → Y} {q : Y → B} (hp : IsCoveringMap (q ∘ r))
    (hq : IsCoveringMap q) (hr : Continuous r)
    {b b' : B} (γ : Path.Homotopic.Quotient b b') (e : (q ∘ r) ⁻¹' {b}) :
    (hq.monodromy γ ⟨r e, e.property⟩ : Y) = r (hp.monodromy γ e) := by
  have h : hq.monodromy γ ⟨r e, e.property⟩ =
      (⟨r (hp.monodromy γ e), (hp.monodromy γ e).property⟩ : q ⁻¹' {b'}) := by
    apply hq.monodromy_eq_of_map_eq ((hp.liftPathQuotient γ e).map ⟨r, hr⟩)
    rw [← Path.Homotopic.Quotient.map_comp]
    exact hp.map_liftPathQuotient γ e
  exact congrArg Subtype.val h

/-- The induced subgroup is precisely the inverse image of the chosen opposite subgroup. -/
theorem fundamentalGroup_range_subgroupCoverProjection [LocallyConnectedSpace B]
    (hp : IsQuotientCoveringMap p G) (H : Subgroup G)
    {b : B} (e : p ⁻¹' {b}) :
    (FundamentalGroup.mapOfEq (x := Quotient.mk (MulAction.orbitRel H E) e.val)
      ⟨subgroupCoverProjection hp H, (isCoveringMap_subgroupCoverProjection hp H).continuous⟩
      (show subgroupCoverProjection hp H (Quotient.mk _ e.val) = b from e.property)).range =
    H.op.comap (hp.fundamentalGroupToMulOpposite e) := by
  let r : E → SubgroupCover (E := E) H := Quotient.mk (MulAction.orbitRel H E)
  have hq := isCoveringMap_subgroupCoverProjection hp H
  have hr := isQuotientCoveringMap_subgroupQuotient hp H
  ext γ
  have he : subgroupCoverProjection hp H (r e) = b := e.property
  refine (mem_fundamentalGroup_range_iff_monodromy_eq hq ⟨r e, he⟩ γ).trans ?_
  rw [Subtype.ext_iff]
  change (hq.monodromy γ ⟨r e, e.property⟩ : SubgroupCover (E := E) H) = r e ↔
    (hp.fundamentalGroupToMulOpposite e γ).unop ∈ H
  rw [monodromy_comp_val (r := r) (q := subgroupCoverProjection hp H)
    hp.isCoveringMap hq hr.continuous γ e]
  change r (hp.isCoveringMap.monodromy γ e) = r e ↔
    (hp.fundamentalGroupToMulOpposite e γ).unop ∈ H
  rw [← hp.unop_fundamentalGroupToMulOpposite_smul]
  constructor
  · intro heq
    obtain ⟨h, hh⟩ := Quotient.eq''.mp heq
    have hhg := hp.isCancelSMul.right_cancel (h : G)
      (hp.fundamentalGroupToMulOpposite e γ).unop e.val hh
    exact hhg ▸ h.property
  · intro hγ
    exact Quotient.sound ⟨⟨_, hγ⟩, rfl⟩

/-- A simply connected quotient covering realizes every subgroup of the base fundamental group. -/
theorem fundamentalGroup_range_prescribed_subgroup [LocallyConnectedSpace B]
    [SimplyConnectedSpace E] (hp : IsQuotientCoveringMap p G)
    {b : B} (e : p ⁻¹' {b}) (K : Subgroup (FundamentalGroup B b)) :
    let H := (K.map (hp.fundamentalGroupToMulOpposite e)).unop
    (FundamentalGroup.mapOfEq (x := Quotient.mk (MulAction.orbitRel H E) e.val)
      ⟨subgroupCoverProjection hp H, (isCoveringMap_subgroupCoverProjection hp H).continuous⟩
      (show subgroupCoverProjection hp H (Quotient.mk _ e.val) = b from e.property)).range = K := by
  dsimp only
  rw [fundamentalGroup_range_subgroupCoverProjection]
  ext γ
  change hp.fundamentalGroupToMulOpposite e γ ∈ K.map (hp.fundamentalGroupToMulOpposite e) ↔ γ ∈ K
  constructor
  · rintro ⟨δ, hδ, heq⟩
    exact hp.fundamentalGroupToMulOpposite_injective e heq ▸ hδ
  · intro hγ
    exact ⟨γ, hγ, rfl⟩

end GaloisForLFunctions.HTGeometry
