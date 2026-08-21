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
  terminal : Q
  terminal_prefix : ∃ before, order = before ++ [terminal]
  parent_terminal : parent terminal = root

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

/-- Executing consecutive portions of a merge plan is associative in physical
time order. -/
theorem execute_append
    {Q : Type*} [DecidableEq Q] (parent : Q → Q)
    (left right : List Q) (P : Q → Option (Fin 3)) :
    execute parent (left ++ right) P =
      execute parent right (execute parent left P) := by
  induction left generalizing P with
  | nil => rfl
  | cons q tail ih =>
      simp only [List.cons_append, execute]
      exact ih (mergeLabel P q (parent q))

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
    ∃ r, r ≠ root ∧ plan.parent r = root := by
  have recurse : ∀ k : ℕ, ∀ q : Q, plan.height q = k → q ≠ root →
      ∃ r, r ≠ root ∧ plan.parent r = root := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro q hheight hqroot
        by_cases hparent : plan.parent q = root
        · exact ⟨q, hqroot, hparent⟩
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
          rw [hqtarget] at hlocal ⊢
          simp [mergeLabel, hlocal, updateTwoQubitPauliLabel]
        exact execute_root_eq_Z_of_initial_Z parent tail
          (mergeLabel P q (parent q)) root hroot_source.2 hZnext
      · apply ih (mergeLabel P q (parent q)) hroot_source.2 hrootNext
        rcases htarget with ⟨r, hr, hrroot⟩
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact (hqtarget hrroot).elim
        · exact ⟨r, hr, hrroot⟩

/-- A coalescing merge plan sends every nonidentity finite Pauli label to the
literal root-only `Z`, provided the register has a second qubit. -/
theorem execute_order_eq_root_Z
    {Q : Type*} [DecidableEq Q] [Nontrivial Q]
    {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    (P : Q → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    execute plan.parent plan.order P = Function.update (fun _ => none) root (some 2) := by
  funext q
  by_cases hqroot : q = root
  · subst q
    have hroot_source : root ∉ plan.order := by
      simpa using (plan.mem_order_iff root)
    have hfinish := plan.execute_order_root_ne_none P hP
    by_cases hProot : P root = none
    · rcases execute_root_eq_initial_or_Z plan.parent plan.order P root hroot_source with
        hpreserve | hZ
      · exact (hfinish (hpreserve.trans hProot)).elim
      · simpa using hZ
    · obtain ⟨source, hsource⟩ := exists_ne root
      obtain ⟨r, hr, hrparent⟩ := plan.exists_parent_eq_root hsource
      have htarget : ∃ s ∈ plan.order, plan.parent s = root :=
        ⟨r, (plan.mem_order_iff r).mpr hr, hrparent⟩
      simpa using execute_root_eq_Z_of_root_ne_none_of_exists_target
        plan.parent plan.order P root hroot_source hProot htarget
  · rw [plan.execute_order_apply_eq_none P hqroot]
    simp [Function.update_of_ne hqroot]

/-- At the terminal root-targeting merge, at least one addressed Pauli label
is nontrivial.  Thus that terminal location is an actual, not identity,
local Clifford gate in the Appendix-B construction. -/
theorem exists_terminal_prefix_local_nontrivial
    {Q : Type*} [DecidableEq Q] [Nontrivial Q]
    {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    (P : Q → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ before, plan.order = before ++ [plan.terminal] ∧
      ¬ (execute plan.parent before P plan.terminal = none ∧
        execute plan.parent before P root = none) := by
  obtain ⟨before, horder⟩ := plan.terminal_prefix
  refine ⟨before, horder, ?_⟩
  intro hlocal
  have hfinal : execute plan.parent plan.order P root = some 2 := by
    have h := congrFun (plan.execute_order_eq_root_Z P hP) root
    simpa using h
  rw [horder, execute_append] at hfinal
  simp only [execute] at hfinal
  rw [plan.parent_terminal] at hfinal
  simp [mergeLabel, hlocal] at hfinal

/-- The symbolic execution of a temporal merge plan is realized by a genuine
Pauli merge schedule; locally trivial planned locations are omitted. -/
def castPauliMergeSchedule
    {Q : Type*} [DecidableEq Q] {P R S : Q → Option (Fin 3)}
    (h : R = S) (schedule : PauliMergeSchedule Q P R) :
    PauliMergeSchedule Q P S := h ▸ schedule

/-- Reindexing only a dependent schedule terminal label does not change its
literal edge word. -/
theorem edgeList_castPauliMergeSchedule
    {Q : Type*} [DecidableEq Q] {P R S : Q → Option (Fin 3)}
    (h : R = S) (schedule : PauliMergeSchedule Q P R) :
    (castPauliMergeSchedule h schedule).edgeList = schedule.edgeList := by
  cases h
  rfl

/-- The symbolic execution of a temporal merge plan is realized by a genuine
Pauli merge schedule; locally trivial planned locations are omitted. -/
theorem exists_schedule_execute
    {Q : Type*} [DecidableEq Q] (parent : Q → Q)
    (order : List Q) (P : Q → Option (Fin 3))
    (hsource_ne_parent : ∀ q ∈ order, q ≠ parent q) :
    ∃ R, ∃ schedule : PauliMergeSchedule Q P R,
      schedule.edgeList.Sublist (order.map fun q => (q, parent q)) ∧
        R = execute parent order P := by
  induction order generalizing P with
  | nil => exact ⟨P, .done P, .slnil, rfl⟩
  | cons q tail ih =>
      have hsourceTail : ∀ r ∈ tail, r ≠ parent r := by
        intro r hr
        exact hsource_ne_parent r (by simp [hr])
      by_cases hlocal : P q = none ∧ P (parent q) = none
      · obtain ⟨R, schedule, hsub, hR⟩ := ih P hsourceTail
        refine ⟨R, schedule, List.Sublist.cons _ hsub, ?_⟩
        simpa [execute, mergeLabel, hlocal] using hR
      · have hsupport : P q ≠ none ∨ P (parent q) ≠ none := by
          by_cases hq : P q = none
          · right
            intro hparent
            exact hlocal ⟨hq, hparent⟩
          · exact Or.inl hq
        let Pnext := updateTwoQubitPauliLabel P q (parent q) none (some 2)
        obtain ⟨R, schedule, hsub, hR⟩ := ih Pnext hsourceTail
        refine ⟨R, .step P q (parent q) (hsource_ne_parent q (by simp)) hsupport schedule,
          ?_, ?_⟩
        · change ((q, parent q) :: schedule.edgeList).Sublist
            ((q, parent q) :: tail.map fun r => (r, parent r))
          exact List.Sublist.cons_cons _ hsub
        · simpa [execute, mergeLabel, hlocal, Pnext] using hR

/-- The whole temporal plan is an ordered subword schedule whose terminal
label is exactly root-only `Z`. -/
theorem exists_schedule_to_root_Z
    {Q : Type*} [DecidableEq Q] [Nontrivial Q]
    {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    (P : Q → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ schedule : PauliMergeSchedule Q P (Function.update (fun _ => none) root (some 2)),
      schedule.edgeList.Sublist (plan.order.map fun q => (q, plan.parent q)) := by
  have hsource_ne_parent : ∀ q ∈ plan.order, q ≠ plan.parent q := by
    intro q hq
    exact plan.parent_ne_self q ((plan.mem_order_iff q).mp hq)
  obtain ⟨R, schedule, hsub, hR⟩ :=
    exists_schedule_execute plan.parent plan.order P hsource_ne_parent
  have hterminal := plan.execute_order_eq_root_Z P hP
  let hcast : R = Function.update (fun _ => none) root (some 2) := hR.trans hterminal
  refine ⟨castPauliMergeSchedule hcast schedule, ?_⟩
  rw [edgeList_castPauliMergeSchedule]
  exact hsub

/-- The ordered gate locations used by a temporal merge plan. -/
def selectedEdges
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges) : List (Q × Q) :=
  plan.order.map fun q => (q, plan.parent q)

/-- The terminal source is non-root and its selected edge is root-targeting. -/
theorem terminal_ne_root
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges) :
    plan.terminal ≠ root := by
  obtain ⟨before, horder⟩ := plan.terminal_prefix
  apply (plan.mem_order_iff plan.terminal).mp
  rw [horder]
  simp

/-- The portion of the plan strictly before its terminal root merge has a
certified schedule, and the terminal pair is nontrivial in the label state
left by that schedule. -/
theorem exists_schedule_before_terminal
    {Q : Type*} [DecidableEq Q] [Nontrivial Q]
    {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    (P : Q → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ before, ∃ Pbefore : Q → Option (Fin 3),
      ∃ earlierSchedule : PauliMergeSchedule Q P Pbefore,
        plan.order = before ++ [plan.terminal] ∧
        earlierSchedule.edgeList.Sublist (before.map fun q => (q, plan.parent q)) ∧
        Pbefore = execute plan.parent before P ∧
        (Pbefore plan.terminal ≠ none ∨ Pbefore root ≠ none) := by
  obtain ⟨before, horder, hlocal⟩ :=
    plan.exists_terminal_prefix_local_nontrivial P hP
  have hsource_ne_parent : ∀ q ∈ before, q ≠ plan.parent q := by
    intro q hq
    exact plan.parent_ne_self q ((plan.mem_order_iff q).mp (by
      rw [horder]
      simp [hq]))
  obtain ⟨Pbefore, earlierSchedule, hsub, hbefore⟩ :=
    exists_schedule_execute plan.parent before P hsource_ne_parent
  refine ⟨before, Pbefore, earlierSchedule, horder, hsub, hbefore, ?_⟩
  rw [hbefore]
  simpa only [not_and_or] using hlocal

/-- A complete schedule can retain the designated terminal root edge as its
literal final gate location.  This is stronger than merely producing some
subword schedule with the same terminal Pauli label. -/
theorem exists_schedule_execute_ending_terminal
    {Q : Type*} [DecidableEq Q] [Nontrivial Q]
    {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    (P : Q → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ R, ∃ schedule : PauliMergeSchedule Q P R, ∃ beforeEdges,
      schedule.edgeList = beforeEdges ++ [(plan.terminal, root)] ∧
      schedule.edgeList.Sublist plan.selectedEdges ∧
      R = execute plan.parent plan.order P := by
  obtain ⟨before, Pbefore, earlierSchedule, horder, hsub, hbefore, hlocal⟩ :=
    plan.exists_schedule_before_terminal P hP
  let terminalSchedule : PauliMergeSchedule Q Pbefore
      (updateTwoQubitPauliLabel Pbefore plan.terminal root none (some 2)) :=
    .step Pbefore plan.terminal root plan.terminal_ne_root hlocal (.done _)
  let fullSchedule := earlierSchedule.append terminalSchedule
  refine ⟨_, fullSchedule, earlierSchedule.edgeList, ?_, ?_, ?_⟩
  · dsimp [fullSchedule]
    rw [PauliMergeSchedule.edgeList_append]
    rfl
  · dsimp [fullSchedule]
    rw [PauliMergeSchedule.edgeList_append]
    change (earlierSchedule.edgeList ++ [(plan.terminal, root)]).Sublist
      plan.selectedEdges
    rw [selectedEdges, horder, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [plan.parent_terminal]
    exact List.Sublist.append hsub (by simp)
  · have hnot : ¬ (Pbefore plan.terminal = none ∧ Pbefore root = none) := by
      simpa only [not_and_or] using hlocal
    rw [horder, execute_append]
    simp only [execute]
    rw [plan.parent_terminal]
    rw [← hbefore]
    rw [mergeLabel, if_neg hnot]

/-- The terminal-edge-retaining schedule has the literal root-only `Z`
output after reindexing its endpoint along the completed merge-plan identity. -/
theorem exists_schedule_to_root_Z_ending_terminal
    {Q : Type*} [DecidableEq Q] [Nontrivial Q]
    {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges)
    (P : Q → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ schedule : PauliMergeSchedule Q P (Function.update (fun _ => none) root (some 2)),
      ∃ beforeEdges,
        schedule.edgeList = beforeEdges ++ [(plan.terminal, root)] ∧
        schedule.edgeList.Sublist plan.selectedEdges := by
  obtain ⟨R, schedule, beforeEdges, hlast, hsub, hR⟩ :=
    plan.exists_schedule_execute_ending_terminal P hP
  let hcast : R = Function.update (fun _ => none) root (some 2) :=
    hR.trans (plan.execute_order_eq_root_Z P hP)
  refine ⟨castPauliMergeSchedule hcast schedule, beforeEdges, ?_, ?_⟩
  · rw [edgeList_castPauliMergeSchedule]
    exact hlast
  · rw [edgeList_castPauliMergeSchedule]
    exact hsub

/-- The selected merge word ends with the terminal edge into the root. -/
theorem selectedEdges_eq_append_terminal
    {Q : Type*} [DecidableEq Q] {root : Q} {blockEdges : List (Q × Q)}
    (plan : TemporalRootMergePlan Q root blockEdges) :
    ∃ before,
      plan.selectedEdges = before ++ [(plan.terminal, root)] := by
  obtain ⟨before, horder⟩ := plan.terminal_prefix
  refine ⟨before.map fun q => (q, plan.parent q), ?_⟩
  simp [selectedEdges, horder, plan.parent_terminal]

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
