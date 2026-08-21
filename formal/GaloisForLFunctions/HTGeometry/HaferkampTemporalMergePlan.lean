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

/-- If the root is never a merge source, one merge either preserves its label
or replaces it by `Z`. -/
theorem mergeLabel_root_eq_self_or_Z
    {Q : Type*} [DecidableEq Q] (P : Q → Option (Fin 3))
    {a b root : Q} (hroota : root ≠ a) :
    mergeLabel P a b root = P root ∨ mergeLabel P a b root = some 2 := by
  by_cases hlocal : P a = none ∧ P b = none
  · left
    simp [mergeLabel, hlocal]
  · by_cases hbroot : b = root
    · right
      subst b
      simp [mergeLabel, hlocal, updateTwoQubitPauliLabel]
    · left
      simp only [mergeLabel, if_neg hlocal, updateTwoQubitPauliLabel]
      rw [Function.update_of_ne (Ne.symm hbroot), Function.update_of_ne hroota]

/-- Once the root label is `Z`, a merge that does not source the root keeps
it `Z`. -/
theorem mergeLabel_root_eq_Z_of_root_eq_Z
    {Q : Type*} [DecidableEq Q] (P : Q → Option (Fin 3))
    {a b root : Q} (hroota : root ≠ a) (hroot : P root = some 2) :
    mergeLabel P a b root = some 2 := by
  rcases mergeLabel_root_eq_self_or_Z P hroota with hpreserve | hZ
  · rw [hpreserve, hroot]
  · exact hZ

/-- Nonzero root support cannot disappear when the root is not a source. -/
theorem mergeLabel_root_ne_none_of_root_ne_none
    {Q : Type*} [DecidableEq Q] (P : Q → Option (Fin 3))
    {a b root : Q} (hroota : root ≠ a) (hroot : P root ≠ none) :
    mergeLabel P a b root ≠ none := by
  rcases mergeLabel_root_eq_self_or_Z P hroota with hpreserve | hZ
  · rwa [hpreserve]
  · simp [hZ]

/-- Execute the selected source-to-parent merges in physical order. -/
def execute
    {Q : Type*} [DecidableEq Q] (parent : Q → Q) :
    List Q → (Q → Option (Fin 3)) → Q → Option (Fin 3)
  | [], P => P
  | q :: tail, P => execute parent tail (mergeLabel P q (parent q))

/-- A sequence of merges leaves a coordinate untouched when it never appears
as a source or target. -/
theorem execute_apply_eq_of_not_mem
    {Q : Type*} [DecidableEq Q] (parent : Q → Q)
    (order : List Q) (P : Q → Option (Fin 3)) (x : Q)
    (hsource : x ∉ order)
    (htarget : ∀ q ∈ order, parent q ≠ x) :
    execute parent order P x = P x := by
  induction order generalizing P with
  | nil => rfl
  | cons q tail ih =>
      simp only [List.mem_cons, not_or] at hsource
      have htargetTail : ∀ r ∈ tail, parent r ≠ x := by
        intro r hr
        exact htarget r (by simp [hr])
      rw [execute, ih (mergeLabel P q (parent q)) hsource.2 htargetTail]
      exact mergeLabel_apply_of_ne P hsource.1 (htarget q (by simp)).symm

/-- Executing any finite merge sequence preserves existence of nonidentity
support. -/
theorem exists_nonidentity_execute
    {Q : Type*} [DecidableEq Q] (parent : Q → Q)
    (order : List Q) (P : Q → Option (Fin 3))
    (hP : ∃ q, P q ≠ none) :
    ∃ q, execute parent order P q ≠ none := by
  induction order generalizing P with
  | nil => exact hP
  | cons q tail ih =>
      rw [execute]
      apply ih
      exact exists_nonidentity_mergeLabel P hP

/-- When the root is never a source, a merge sequence can only preserve its
initial label or turn it into `Z`. -/
theorem execute_root_eq_initial_or_Z
    {Q : Type*} [DecidableEq Q] (parent : Q → Q)
    (order : List Q) (P : Q → Option (Fin 3)) (root : Q)
    (hroot_source : root ∉ order) :
    execute parent order P root = P root ∨
      execute parent order P root = some 2 := by
  induction order generalizing P with
  | nil => exact Or.inl rfl
  | cons q tail ih =>
      simp only [List.mem_cons, not_or] at hroot_source
      rw [execute]
      rcases ih (mergeLabel P q (parent q)) hroot_source.2 with htail | htail
      · rcases mergeLabel_root_eq_self_or_Z P hroot_source.1 with hpreserve | hZ
        · exact Or.inl (htail.trans hpreserve)
        · exact Or.inr (htail.trans hZ)
      · exact Or.inr htail

/-- Once root support is `Z`, a sequence that never sources the root keeps it
exactly `Z`. -/
theorem execute_root_eq_Z_of_initial_Z
    {Q : Type*} [DecidableEq Q] (parent : Q → Q)
    (order : List Q) (P : Q → Option (Fin 3)) (root : Q)
    (hroot_source : root ∉ order) (hroot : P root = some 2) :
    execute parent order P root = some 2 := by
  induction order generalizing P with
  | nil => exact hroot
  | cons q tail ih =>
      simp only [List.mem_cons, not_or] at hroot_source
      rw [execute]
      apply ih
      · exact hroot_source.2
      · exact mergeLabel_root_eq_Z_of_root_eq_Z P hroot_source.1 hroot

/-- In an ordered merge forest, every listed source is absent after the
complete execution. -/
theorem execute_apply_eq_none_of_mem
    {Q : Type*} [DecidableEq Q] (parent : Q → Q)
    (order : List Q) (hnodup : order.Nodup)
    (hsource_ne_parent : ∀ q ∈ order, q ≠ parent q)
    (hno_later_targets : ∀ before q after r,
      order = before ++ q :: after → r ∈ after → parent r ≠ q)
    (P : Q → Option (Fin 3)) {x : Q} (hx : x ∈ order) :
    execute parent order P x = none := by
  induction order generalizing P with
  | nil => simp at hx
  | cons q tail ih =>
      have hnodupTail : tail.Nodup := (List.nodup_cons.mp hnodup).2
      have hsourceTail : ∀ r ∈ tail, r ≠ parent r := by
        intro r hr
        exact hsource_ne_parent r (by simp [hr])
      have hnoTail : ∀ before q' after r,
          tail = before ++ q' :: after → r ∈ after → parent r ≠ q' := by
        intro before q' after r hsplit hr
        apply hno_later_targets (q :: before) q' after r
        simp [hsplit]
        exact hr
      simp only [List.mem_cons] at hx
      rcases hx with hhead | hx
      · subst x
        rw [execute]
        rw [execute_apply_eq_of_not_mem parent tail
          (mergeLabel P q (parent q)) q (List.nodup_cons.mp hnodup).1]
        · exact mergeLabel_source_eq_none P (hsource_ne_parent q (by simp))
        · intro r hr
          exact hno_later_targets [] q tail r (by simp) hr
      · rw [execute]
        exact ih hnodupTail hsourceTail hnoTail (mergeLabel P q (parent q)) hx

/-- The completed plan clears every non-root qubit. -/
theorem execute_order_apply_eq_none
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    (P : Q → Option (Fin 3)) {q : Q} (hq : q ≠ root) :
    execute plan.parent plan.order P q = none := by
  apply execute_apply_eq_none_of_mem plan.parent plan.order plan.order_nodup
  · intro r hr
    exact plan.parent_ne_self r ((plan.mem_order_iff r).mp hr)
  · exact plan.no_later_targets
  · exact (plan.mem_order_iff q).mpr hq

/-- A nonidentity input remains nonidentity after the completed plan. -/
theorem exists_nonidentity_execute_order
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    (P : Q → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ q, execute plan.parent plan.order P q ≠ none := by
  exact exists_nonidentity_execute plan.parent plan.order P hP

/-- Since every non-root coordinate is cleared, nonidentity support finishes
at the distinguished root. -/
theorem execute_order_root_ne_none
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    (P : Q → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    execute plan.parent plan.order P root ≠ none := by
  obtain ⟨q, hq⟩ := plan.exists_nonidentity_execute_order P hP
  by_cases hqroot : q = root
  · simpa [hqroot] using hq
  · have hclear := plan.execute_order_apply_eq_none P hqroot
    rw [hclear] at hq
    exact (hq rfl).elim

/-- Every non-root vertex has a parent chain ending in one selected edge into
the root. -/
theorem exists_parent_eq_root
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    {q : Q} (hq : q ≠ root) :
    ∃ r, plan.parent r = root := by
  have recurse : ∀ k : ℕ, ∀ q : Q, plan.height q = k → q ≠ root →
      ∃ r, plan.parent r = root := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro q hheight hqroot
        by_cases hparent : plan.parent q = root
        · exact ⟨q, hparent⟩
        · have hlt : plan.height (plan.parent q) < k := by
            simpa [hheight] using plan.parent_height_lt q hqroot
          exact ih (plan.height (plan.parent q)) hlt (plan.parent q) rfl hparent
  exact recurse (plan.height q) q rfl hq

/-- If a root-targeting merge occurs, nonzero initial root support is
normalized to `Z` and remains so through the rest of the sequence. -/
theorem execute_root_eq_Z_of_root_ne_none_of_exists_target
    {Q : Type*} [DecidableEq Q] (parent : Q → Q)
    (order : List Q) (P : Q → Option (Fin 3)) (root : Q)
    (hroot_source : root ∉ order) (hroot : P root ≠ none)
    (htarget : ∃ q ∈ order, parent q = root) :
    execute parent order P root = some 2 := by
  induction order generalizing P with
  | nil => simp at htarget
  | cons q tail ih =>
      simp only [List.mem_cons, not_or] at hroot_source
      have hrootNext : mergeLabel P q (parent q) root ≠ none :=
        mergeLabel_root_ne_none_of_root_ne_none P hroot_source.1 hroot
      rw [execute]
      by_cases hqtarget : parent q = root
      · have hlocal : ¬ (P q = none ∧ P (parent q) = none) := by
          intro hlocal
          apply hroot
          simpa [hqtarget] using hlocal.2
        have hZnext : mergeLabel P q (parent q) root = some 2 := by
          rw [hqtarget]
          simp [mergeLabel, hlocal, updateTwoQubitPauliLabel]
        exact execute_root_eq_Z_of_initial_Z parent tail
          (mergeLabel P q (parent q)) root hroot_source.2 hZnext
      · apply ih (mergeLabel P q (parent q)) root hroot_source.2 hrootNext
        rcases htarget with ⟨r, hr, hrroot⟩
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact (hqtarget hrroot).elim
        · exact ⟨r, hr, hrroot⟩

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
