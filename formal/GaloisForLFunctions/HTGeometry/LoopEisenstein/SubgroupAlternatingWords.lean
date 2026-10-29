import GaloisForLFunctions.RHTower.Deninger.DeningerPushoutDecomp

/-!
# Alternating representatives in a join of two subgroups

The pushout over a common subgroup maps onto the join. Its actual normal
form supplies either a common-subgroup element or a nonempty alternating
word outside that subgroup. No injectivity of the pushout map is needed.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

open Monoid

/-- A join of two subgroups has alternating representatives relative to any common subgroup. -/
theorem subgroup_join_base_or_alternating {G : Type*} [Group G]
    (H : Bool → Subgroup G) (M : Subgroup G) (hM : ∀ i, M ≤ H i)
    {g : G} (hg : g ∈ H false ⊔ H true) :
    g ∈ M ∨ ∃ L : List (Σ i, H i), L ≠ [] ∧
      (∀ p ∈ L, (p.2 : G) ∉ M) ∧
      List.IsChain (fun p q : Σ i, H i => p.1 ≠ q.1) L ∧
      (L.map (fun p => (p.2 : G))).prod = g := by
  classical
  let φ : ∀ i, M →* H i := fun i =>
    { toFun := fun m => ⟨m, hM i m.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : ∀ i, Function.Injective (φ i) := by
    intro i x y he
    exact Subtype.ext (congrArg (fun h : H i => (h : G)) he)
  let f : ∀ i, H i →* G := fun i => (H i).subtype
  have hf : ∀ i, (f i).comp (φ i) = M.subtype := fun _ => rfl
  let ψ : PushoutI φ →* G := PushoutI.lift f M.subtype hf
  have hH : ∀ i, H i ≤ ψ.range := by
    intro i x hx
    refine ⟨PushoutI.of i (⟨x, hx⟩ : H i), ?_⟩
    exact PushoutI.lift_of f M.subtype hf _
  obtain ⟨x, hx⟩ := (sup_le (hH false) (hH true) : H false ⊔ H true ≤ ψ.range) hg
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty φ hφ
  rcases _root_.RHTower.deningerExists_letterProd (d := d) x with hbase | hword
  · obtain ⟨m, hm, _⟩ := hbase
    left
    have he : ψ x = (m : G) := by
      rw [hm]
      exact PushoutI.lift_base f M.subtype hf m
    rw [← hx, he]
    exact m.property
  · obtain ⟨L, hL, hred, halt, _, he⟩ := hword
    right
    refine ⟨L, hL, ?_, halt, ?_⟩
    · intro p hp hm
      apply hred p hp
      exact ⟨⟨p.2, hm⟩, Subtype.ext rfl⟩
    · rw [← hx, he]
      change _ = ψ (L.map (fun p => PushoutI.of p.1 p.2)).prod
      rw [map_list_prod, List.map_map]
      congr 1

end GaloisForLFunctions.HTGeometry.LoopEisenstein
