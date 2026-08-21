import GaloisForLFunctions.HTGeometry.HaferkampBackwardLightCone

/-!
# Coalescing temporal merge plans for a backwards light cone

Appendix B uses a complete collection of source-to-root paths that coalesce
after every crossing.  A `TemporalRootMergePlan` records the equivalent
single-parent form: every non-root qubit has one later parent, and the chosen
parent edges occur in the physical block order.  This is stronger data than a
collection of unrelated paths and is what makes a single gate word collapse
an entire Pauli string, rather than merely mark its root coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A time-compatible rooted merge forest embedded in an ordered block.
The order lists every non-root qubit once and sends each one to a parent that
occurs later unless it is the root. -/
structure TemporalRootMergePlan
    (Q : Type*) [DecidableEq Q] (root : Q) (blockEdges : List (Q × Q)) where
  order : List Q
  order_nodup : order.Nodup
  mem_order_iff : ∀ q, q ∈ order ↔ q ≠ root
  parent : Q → Q
  parent_later : ∀ q, q ≠ root → parent q ≠ root →
    order.indexOf q < order.indexOf (parent q)
  selected_sublist : (order.map fun q => (q, parent q)).Sublist blockEdges

namespace TemporalRootMergePlan

/-- The ordered gate locations used by a temporal merge plan. -/
def selectedEdges
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges) : List (Q × Q) :=
  plan.order.map fun q => (q, plan.parent q)

/-- Each selected location is genuinely two-qubit. -/
theorem parent_ne_self
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    {q : Q} (hq : q ≠ root) : q ≠ plan.parent q := by
  by_cases hparent : plan.parent q = root
  · simpa [hparent] using hq
  · intro hEq
    have hlt := plan.parent_later q hq hparent
    rw [hEq] at hlt
    exact Nat.lt_irrefl _ hlt

/-- Every selected edge has distinct endpoints. -/
theorem selectedEdges_edge_distinct
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges) :
    ∀ edge ∈ plan.selectedEdges, edge.1 ≠ edge.2 := by
  intro edge hedge
  rw [selectedEdges] at hedge
  obtain ⟨q, hq, hEdge⟩ := List.mem_map.1 hedge
  subst edge
  exact plan.parent_ne_self ((plan.mem_order_iff q).mp hq)

/-- The merge locations occur in the original physical block word. -/
theorem selectedEdges_sublist
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges) :
    plan.selectedEdges.Sublist blockEdges := by
  exact plan.selected_sublist

end TemporalRootMergePlan

end

end GaloisForLFunctions.HTGeometry
