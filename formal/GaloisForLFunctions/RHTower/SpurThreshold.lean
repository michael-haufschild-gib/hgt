/-
Doc 24 AMP threshold bridge for the SPUR-R stack.

`SpurTransitions` proves the finite Boolean copy/flip block arithmetic.  This
module supplies the reusable adapter from ordered real-valued margin sequences
to those Boolean states: once a threshold split is known, the copy/flip sequence
has at most one transition and the corrected counting capstone applies.
-/
import GaloisForLFunctions.RHTower.SpurTransitions

noncomputable section

namespace RHTower

/-- Boolean states obtained by thresholding an ordered real-valued sequence. -/
def thresholdStates (t : ℝ) (xs : List ℝ) : List Bool :=
  xs.map fun x => decide (t < x)

/-- AMP margin states relative to the copy/flip threshold `1`. -/
def ampMarginStates (xs : List ℝ) : List Bool :=
  thresholdStates 1 xs

/-- If every entry thresholds to the same Boolean state, the threshold states are constant. -/
theorem thresholdStates_eq_replicate_of_forall_eq (t : ℝ) :
    ∀ (xs : List ℝ) (b : Bool),
      (∀ x ∈ xs, decide (t < x) = b) →
        thresholdStates t xs = List.replicate xs.length b := by
  intro xs b h
  rw [thresholdStates]
  exact (List.map_eq_replicate_iff).mpr h

/-- A threshold split gives one constant block on each side of the threshold. -/
theorem thresholdStates_append_eq_replicate_append_replicate {t : ℝ}
    {left right : List ℝ} {b : Bool}
    (hleft : ∀ x ∈ left, decide (t < x) = b)
    (hright : ∀ x ∈ right, decide (t < x) = !b) :
    thresholdStates t (left ++ right) =
      List.replicate left.length b ++ List.replicate right.length (!b) := by
  rw [thresholdStates]
  rw [List.map_append]
  have hl := thresholdStates_eq_replicate_of_forall_eq t left b hleft
  have hr := thresholdStates_eq_replicate_of_forall_eq t right (!b) hright
  simpa [thresholdStates] using congrArg₂ List.append hl hr

/-- A threshold split has at most one copy/flip transition. -/
theorem copyFlipTransitions_thresholdStates_append_le_one {t : ℝ}
    {left right : List ℝ} {b : Bool}
    (hleft : ∀ x ∈ left, decide (t < x) = b)
    (hright : ∀ x ∈ right, decide (t < x) = !b) :
    copyFlipTransitions (thresholdStates t (left ++ right)) ≤ 1 := by
  rw [thresholdStates_append_eq_replicate_append_replicate hleft hright]
  exact copyFlipTransitions_block_le_one left.length right.length b

/-- Corrected counting after a real threshold split. -/
theorem corrected_counting_exact_pair_of_thresholdStates_append {Z : ℕ} {t : ℝ}
    {left right : List ℝ} {b : Bool}
    (hleft : ∀ x ∈ left, decide (t < x) = b)
    (hright : ∀ x ∈ right, decide (t < x) = !b)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (thresholdStates t (left ++ right))) :
    Z = 2 :=
  even_count_eq_two_of_visible_and_le_two hvisible heven
    (corrected_counting_bound_at_most_one_crossing hbound
      (copyFlipTransitions_thresholdStates_append_le_one hleft hright) heven)

/-- An AMP margin split has at most one copy/flip transition. -/
theorem copyFlipTransitions_ampMarginStates_append_le_one
    {left right : List ℝ} {b : Bool}
    (hleft : ∀ x ∈ left, decide (1 < x) = b)
    (hright : ∀ x ∈ right, decide (1 < x) = !b) :
    copyFlipTransitions (ampMarginStates (left ++ right)) ≤ 1 := by
  unfold ampMarginStates
  exact copyFlipTransitions_thresholdStates_append_le_one hleft hright

/-- Corrected counting from an AMP margin split. -/
theorem corrected_counting_exact_pair_of_ampMargin_append {Z : ℕ}
    {left right : List ℝ} {b : Bool}
    (hleft : ∀ x ∈ left, decide (1 < x) = b)
    (hright : ∀ x ∈ right, decide (1 < x) = !b)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (left ++ right))) :
    Z = 2 := by
  unfold ampMarginStates at hbound
  exact corrected_counting_exact_pair_of_thresholdStates_append hleft hright hvisible heven hbound

/-- Prop-level AMP wrapper for a below/equal block followed by an above block. -/
theorem copyFlipTransitions_ampMarginStates_notlt_lt_append_le_one
    {left right : List ℝ}
    (hleft : ∀ x ∈ left, ¬ 1 < x)
    (hright : ∀ x ∈ right, 1 < x) :
    copyFlipTransitions (ampMarginStates (left ++ right)) ≤ 1 := by
  exact copyFlipTransitions_ampMarginStates_append_le_one (b := false)
    (by intro x hx; simp [hleft x hx])
    (by intro x hx; simp [hright x hx])

/-- Prop-level AMP wrapper for an above block followed by a below/equal block. -/
theorem copyFlipTransitions_ampMarginStates_lt_notlt_append_le_one
    {left right : List ℝ}
    (hleft : ∀ x ∈ left, 1 < x)
    (hright : ∀ x ∈ right, ¬ 1 < x) :
    copyFlipTransitions (ampMarginStates (left ++ right)) ≤ 1 := by
  exact copyFlipTransitions_ampMarginStates_append_le_one (b := true)
    (by intro x hx; simp [hleft x hx])
    (by intro x hx; simp [hright x hx])

/-- Corrected counting for AMP below/equal then above threshold blocks. -/
theorem corrected_counting_exact_pair_of_ampMargin_notlt_lt_append {Z : ℕ}
    {left right : List ℝ}
    (hleft : ∀ x ∈ left, ¬ 1 < x)
    (hright : ∀ x ∈ right, 1 < x)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (left ++ right))) :
    Z = 2 :=
  even_count_eq_two_of_visible_and_le_two hvisible heven
    (corrected_counting_bound_at_most_one_crossing hbound
      (copyFlipTransitions_ampMarginStates_notlt_lt_append_le_one hleft hright) heven)

/-- Corrected counting for AMP above then below/equal threshold blocks. -/
theorem corrected_counting_exact_pair_of_ampMargin_lt_notlt_append {Z : ℕ}
    {left right : List ℝ}
    (hleft : ∀ x ∈ left, 1 < x)
    (hright : ∀ x ∈ right, ¬ 1 < x)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound : Z ≤ 2 + copyFlipTransitions (ampMarginStates (left ++ right))) :
    Z = 2 :=
  even_count_eq_two_of_visible_and_le_two hvisible heven
    (corrected_counting_bound_at_most_one_crossing hbound
      (copyFlipTransitions_ampMarginStates_lt_notlt_append_le_one hleft hright) heven)

end RHTower
