import Mathlib.Topology.Homotopy.Lifting

/-!
# Comparing pointed connected coverings

Equality of the based fundamental-group images gives lifts of each projection
through the other cover. Uniqueness of lifts makes these maps inverse, yielding
a unique pointed homeomorphism over the base. Neither covering source needs to
be simply connected.
-/

open Topology Function

namespace GaloisForLFunctions.HTGeometry

/-- Matching based fundamental-group images determine a unique pointed covering isomorphism. -/
theorem existsUnique_covering_homeomorph_of_range_eq
    {E Y B : Type*} [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace B]
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace Y] [LocallyPathConnectedSpace Y]
    {p : E → B} {q : Y → B} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (e₀ : E) (y₀ : Y) (hbase : q y₀ = p e₀)
    (hrange : (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀).range =
      (FundamentalGroup.mapOfEq ⟨q, hq.continuous⟩ hbase).range) :
    ∃! d : E ≃ₜ Y, d e₀ = y₀ ∧ ∀ e, q (d e) = p e := by
  let p' : C(E, B) := ⟨p, hp.continuous⟩
  let q' : C(Y, B) := ⟨q, hq.continuous⟩
  have hreverse : (FundamentalGroup.map q' y₀).range ≤
      (FundamentalGroup.mapOfEq p' hbase.symm).range := by
    rintro γ ⟨δ, rfl⟩
    obtain ⟨η, hη⟩ := hrange.ge ⟨δ, rfl⟩
    refine ⟨η, ?_⟩
    rw [FundamentalGroup.map_apply, FundamentalGroup.mapOfEq_apply] at hη
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply]
    change (Path.Homotopic.Quotient.map η p').cast hbase hbase =
      Path.Homotopic.Quotient.map δ q'
    rw [hη]
    simp [q']
  obtain ⟨d, ⟨hd0, hdp⟩, hdunique⟩ := hq.existsUnique_continuousMap_lifts_of_range_le
    (f := p') hbase hrange.le
  obtain ⟨d', ⟨hd1, hdp'⟩, -⟩ := hp.existsUnique_continuousMap_lifts_of_range_le
    (f := q') hbase.symm hreverse
  have hleft : (d' : Y → E) ∘ d = id := by
    refine hp.eq_of_comp_eq (d'.continuous.comp d.continuous) continuous_id ?_ e₀ ?_
    · funext e
      change p (d' (d e)) = p e
      exact (congrFun hdp' (d e)).trans (congrFun hdp e)
    · change d' (d e₀) = e₀
      rw [hd0, hd1]
  have hright : (d : E → Y) ∘ d' = id := by
    refine hq.eq_of_comp_eq (d.continuous.comp d'.continuous) continuous_id ?_ y₀ ?_
    · funext y
      change q (d (d' y)) = q y
      exact (congrFun hdp (d' y)).trans (congrFun hdp' y)
    · change d (d' y₀) = y₀
      rw [hd1, hd0]
  let D : E ≃ₜ Y :=
    { toFun := d
      invFun := d'
      left_inv := fun e => congrFun hleft e
      right_inv := fun y => congrFun hright y
      continuous_toFun := d.continuous
      continuous_invFun := d'.continuous }
  refine ⟨D, ⟨hd0, fun e => congrFun hdp e⟩, ?_⟩
  intro D' hD'
  have hd' : (⟨D', D'.continuous⟩ : C(E, Y)) = d :=
    hdunique (⟨D', D'.continuous⟩ : C(E, Y)) ⟨hD'.1, funext hD'.2⟩
  ext e
  exact DFunLike.congr_fun hd' e

end GaloisForLFunctions.HTGeometry
