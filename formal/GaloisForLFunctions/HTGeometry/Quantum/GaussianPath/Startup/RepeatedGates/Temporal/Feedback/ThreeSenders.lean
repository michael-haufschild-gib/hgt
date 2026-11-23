import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.CrossConnections

/-! # Three distinct two-sender patterns cannot coexist in a temporal forest -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
variable {V : Type*} [DecidableEq V]

/-- An output knows two specified inputs and misses the third. -/
def seesTwo (w : List (V×V)) (a b c : V) : Prop :=
  ∃ y, a∈inputs w y ∧ b∈inputs w y ∧ c∉inputs w y

private theorem same_label {w : List (V×V)} {a b c : V} (h : seesTwo w a b c) :
    label w a=label w b := by
  obtain ⟨_,ha,hb,_⟩ := h
  exact (label_of_input w ha).trans (label_of_input w hb).symm

private theorem old_or_union (e : V×V) (w : List (V×V)) (a b c : V)
    (h : seesTwo (e::w) a b c) :
    let U := inputs w e.1 ∪ inputs w e.2
    seesTwo w a b c ∨ (a∈U ∧ b∈U ∧ c∉U) := by
  obtain ⟨y,hy⟩ := h
  by_cases hit : y=e.1 ∨ y=e.2
  · right; simpa only [inputs,if_pos hit] using hy
  · left; exact ⟨y,by simpa only [inputs,if_neg hit] using hy⟩

private theorem old_of_connected {e : V×V} {w : List (V×V)} {a b c : V}
    (hm : ¬Nonmerging e w) (hab : label w a=label w b) (h : seesTwo (e::w) a b c) :
    seesTwo w a b c := by
  rcases old_or_union e w a b c h with h|⟨ha,hb,hc⟩
  · exact h
  · rcases mem_union.mp ha with ha|ha <;> rcases mem_union.mp hb with hb|hb
    · exact ⟨e.1,ha,hb,fun hh => hc (mem_union_left _ hh)⟩
    · exact (hm ((label_of_input w ha).symm.trans (hab.trans (label_of_input w hb)))).elim
    · exact (hm ((label_of_input w hb).symm.trans (hab.symm.trans (label_of_input w ha)))).elim
    · exact ⟨e.2,ha,hb,fun hh => hc (mem_union_right _ hh)⟩

private theorem old_of_three {e : V×V} {w : List (V×V)} {a b c : V}
    (hm : ¬Nonmerging e w) (h₁ : seesTwo (e::w) a b c)
    (h₂ : seesTwo (e::w) b c a) (h₃ : seesTwo (e::w) c a b) : seesTwo w a b c := by
  rcases old_or_union e w a b c h₁ with h|⟨ha,hb,_⟩
  · exact h
  · have h₂' := (old_or_union e w b c a h₂).resolve_right (fun hh => hh.2.2 ha)
    have h₃' := (old_or_union e w c a b h₃).resolve_right (fun hh => hh.2.2 hb)
    exact old_of_connected hm ((same_label h₂').trans (same_label h₃')).symm h₁

/-- At most two of the three two-out-of-three input patterns exist
anywhere in a forest of component mergers. A new call produces only one
pattern. The other two would already put all three senders in one component. -/
theorem forest_excludes_three_patterns (w : List (V×V)) (h : redundant w=0) (a b c : V) :
    ¬(seesTwo w a b c ∧ seesTwo w b c a ∧ seesTwo w c a b) := by
  induction w with
  | nil =>
    rintro ⟨⟨i,hi,hj,_⟩,⟨j,hb,_,ha⟩,_⟩
    simp only [inputs,mem_singleton] at hi hj hb ha
    exact ha (hi.trans (hj.symm.trans hb))
  | cons e w ih =>
    have hm : ¬Nonmerging e w := by
      intro hm
      simp only [redundant,if_pos hm,Nat.add_one_ne_zero] at h
    have hw : redundant w=0 := by simpa only [redundant,if_neg hm,Nat.add_zero] using h
    rintro ⟨h₁,h₂,h₃⟩
    exact ih hw ⟨old_of_three hm h₁ h₂ h₃,old_of_three hm h₂ h₃ h₁,old_of_three hm h₃ h₁ h₂⟩

private theorem reduced_inputs_subset (w : List (V×V)) (y : V) :
    inputs (mergingWord w) y ⊆ inputs w y := by
  induction w generalizing y with
  | nil => exact Subset.rfl
  | cons e w ih =>
    by_cases hn : Nonmerging e w
    · rw [mergingWord,if_pos hn]
      exact (ih y).trans (inputs_mono e w y)
    · rw [mergingWord,if_neg hn]
      by_cases hit : y=e.1 ∨ y=e.2
      · simp only [inputs,if_pos hit]
        exact union_subset_union (ih _) (ih _)
      · simpa only [inputs,if_neg hit] using ih y

/-- For missing pairs whose outputs have the same history of nonmerging
calls, some pair of tests lacks a cross-connection in at least one direction. -/
theorem three_missing_pairs_exclude_mutual_cross (w : List (V×V)) (x y : Fin 3→V)
    (hm : ∀ i, x i∉inputs w (y i)) (hp : ∀ i, profile w (y i)=profile w (y 0)) :
    ¬(∀ i j, i≠j → x i∈inputs w (y j)) := by
  intro h
  let u := mergingWord w
  have cross (i j : Fin 3) (hne : i≠j) : x i∈inputs u (y j) :=
    cross_connection_in_forest w (hm i) ((hp j).trans (hp i).symm) (h i j hne)
  have miss (i : Fin 3) : x i∉inputs u (y i) := fun hh => hm i (reduced_inputs_subset w _ hh)
  exact forest_excludes_three_patterns u (redundant_mergingWord w) (x 0) (x 1) (x 2)
    ⟨⟨y 2,cross 0 2 (by omega),cross 1 2 (by omega),miss 2⟩,
      ⟨y 0,cross 1 0 (by omega),cross 2 0 (by omega),miss 0⟩,
      ⟨y 1,cross 2 1 (by omega),cross 0 1 (by omega),miss 1⟩⟩

#print axioms three_missing_pairs_exclude_mutual_cross
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
