import GaloisForLFunctions.HTGeometry.DisjointPointCapsFundamentalGroup
import GaloisForLFunctions.HTGeometry.PuncturedWindingBaseChange

open Topology Set Function
open DifferentialGeometry.Topology.VanKampen

namespace GaloisForLFunctions.HTGeometry

/-- Changing the displayed target basepoint does not change surjectivity. -/
theorem fundamentalGroup_map_surjective_of_mapOfEq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (hs : Surjective (FundamentalGroup.mapOfEq f h)) :
    Surjective (FundamentalGroup.map f x) := by
  subst y
  intro δ
  obtain ⟨γ, hγ⟩ := hs δ
  refine ⟨γ, ?_⟩
  simpa only [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl] using hγ

/-- The old parametrizing space itself maps onto the completion's fundamental group. -/
theorem PointCapData.fundamentalGroup_old_surjective
    {Y D I : Type*} [TopologicalSpace Y] [TopologicalSpace D]
    (c : PointCapData Y D I) [T1Space D] [PathConnectedSpace Y]
    [SimplyConnectedSpace D] [PathConnectedSpace {z : D // z ≠ c.center}]
    (a : Y) : Surjective (FundamentalGroup.map ⟨c.old, c.continuous_old⟩ a) := by
  let e := c.isOpenEmbedding_old.isEmbedding.toHomeomorph
  have he : Surjective (FundamentalGroup.map ⟨e, e.continuous⟩ a) :=
    fundamentalGroup_map_surjective_of_mapOfEq ⟨e, e.continuous⟩ rfl
      (fundamentalGroup_mapOfEq_bijective e a rfl).2
  intro δ
  obtain ⟨γ, hγ⟩ := c.fundamentalGroup_body_surjective (e a) δ
  obtain ⟨β, hβ⟩ := he γ
  refine ⟨β, ?_⟩
  rw [← hβ] at hγ
  simp only [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.map_comp] at hγ
  exact hγ

/-- A commuting factorization through a simply connected space kills every loop
when the two original maps are onto on fundamental groups. -/
theorem simplyConnectedSpace_of_commuting_surjective_fundamentalGroups
    {A Y Z M : Type*} [TopologicalSpace A] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace M] [SimplyConnectedSpace Z] [PathConnectedSpace M]
    (f : C(A, Y)) (i : C(Y, M)) (j : C(A, Z)) (g : C(Z, M)) (a : A)
    (hf : Surjective (FundamentalGroup.map f a))
    (hi : Surjective (FundamentalGroup.map i (f a)))
    (hcomm : g.comp j = i.comp f) : SimplyConnectedSpace M := by
  have hs : Surjective (FundamentalGroup.map (g.comp j) a) := by
    rw [hcomm]
    intro δ
    obtain ⟨β, hβ⟩ := hi δ
    obtain ⟨α, hα⟩ := hf β
    refine ⟨α, ?_⟩
    change Path.Homotopic.Quotient.map α (i.comp f) = δ
    rw [Path.Homotopic.Quotient.map_comp]
    change (FundamentalGroup.map i (f a)) ((FundamentalGroup.map f a) α) = δ
    rw [hα, hβ]
  letI : Subsingleton (FundamentalGroup M (g (j a))) := ⟨fun δ ε => by
    obtain ⟨α, rfl⟩ := hs δ
    obtain ⟨β, rfl⟩ := hs ε
    have h : (FundamentalGroup.map j a) α = (FundamentalGroup.map j a) β :=
      Subsingleton.elim _ _
    have hh := congrArg (FundamentalGroup.map g (j a)) h
    simpa only [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.map_comp] using hh⟩
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, fun x γ => ?_⟩
  have hq : (⟦γ⟧ : FundamentalGroup M x) = ⟦Path.refl x⟧ := by
    apply (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (g (j a)) x).symm.injective
    exact Subsingleton.elim _ _
  exact Quotient.exact hq

end GaloisForLFunctions.HTGeometry
