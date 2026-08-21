import GaloisForLFunctions.HTGeometry.HaferkampQubitPathTransport

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
  height : Q → ℕ
  height_zero_iff : ∀ q, height q = 0 ↔ q = root
  parent_ne_self : ∀ q, q ≠ root → q ≠ parent q
  parent_height_lt : ∀ q, q ≠ root → height (parent q) < height q
  parent_later : ∀ q, q ≠ root → parent q ≠ root →
    ∃ before between after,
      order = before ++ q :: between ++ parent q :: after
  no_later_targets : ∀ before q after r,
    order = before ++ q :: after → r ∈ after → parent r ≠ q
  selected_sublist : (order.map fun q => (q, parent q)).Sublist blockEdges

namespace TemporalRootMergePlan

/-- Perform one planned support merge.  A locally trivial pair receives the
identity action; every other pair is replaced by a rootward `Z`. -/
def mergeLabel
    {Q : Type*} [DecidableEq Q] (P : Q → Option (Fin 3)) (a b : Q) :
    Q → Option (Fin 3) :=
  if P a = none ∧ P b = none then P
  else updateTwoQubitPauliLabel P a b none (some 2)

/-- A genuine planned merge clears its source coordinate. -/
theorem mergeLabel_source_eq_none
    {Q : Type*} [DecidableEq Q] (P : Q → Option (Fin 3))
    {a b : Q} (hab : a ≠ b) :
    mergeLabel P a b a = none := by
  by_cases hlocal : P a = none ∧ P b = none
  · simp [mergeLabel, hlocal]
  · simp [mergeLabel, hlocal, updateTwoQubitPauliLabel, hab]

/-- A planned merge leaves every unaddressed coordinate unchanged. -/
theorem mergeLabel_apply_of_ne
    {Q : Type*} [DecidableEq Q] (P : Q → Option (Fin 3))
    {a b q : Q} (hqa : q ≠ a) (hqb : q ≠ b) :
    mergeLabel P a b q = P q := by
  by_cases hlocal : P a = none ∧ P b = none
  · simp [mergeLabel, hlocal]
  · simp [mergeLabel, hlocal, updateTwoQubitPauliLabel, hqa, hqb]

/-- One planned merge cannot erase the last nonidentity Pauli support. -/
theorem exists_nonidentity_mergeLabel
    {Q : Type*} [DecidableEq Q] (P : Q → Option (Fin 3))
    {a b : Q} (hP : ∃ q, P q ≠ none) :
    ∃ q, mergeLabel P a b q ≠ none := by
  by_cases hlocal : P a = none ∧ P b = none
  · obtain ⟨q, hq⟩ := hP
    exact ⟨q, by simpa [mergeLabel, hlocal] using hq⟩
  · exact ⟨b, by simp [mergeLabel, hlocal, updateTwoQubitPauliLabel]⟩

/-- The ordered gate locations used by a temporal merge plan. -/
def selectedEdges
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges) : List (Q × Q) :=
  plan.order.map fun q => (q, plan.parent q)

/-- Each selected location is genuinely two-qubit. -/
theorem source_ne_parent
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    {q : Q} (hq : q ≠ root) : q ≠ plan.parent q := by
  exact plan.parent_ne_self q hq

/-- Every selected edge has distinct endpoints. -/
theorem selectedEdges_edge_distinct
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges) :
    ∀ edge ∈ plan.selectedEdges, edge.1 ≠ edge.2 := by
  intro edge hedge
  rw [selectedEdges] at hedge
  obtain ⟨q, hq, hEdge⟩ := List.mem_map.1 hedge
  subst edge
  exact plan.source_ne_parent ((plan.mem_order_iff q).mp hq)

/-- The merge locations occur in the original physical block word. -/
theorem selectedEdges_sublist
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges) :
    plan.selectedEdges.Sublist blockEdges := by
  exact plan.selected_sublist

end TemporalRootMergePlan

end

end GaloisForLFunctions.HTGeometry
