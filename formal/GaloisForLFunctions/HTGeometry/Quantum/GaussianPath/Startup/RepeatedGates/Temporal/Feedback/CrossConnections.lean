import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.Profiles

/-! # Removing cyclic calls within an output history class -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
variable {V : Type*} [DecidableEq V]

/-- Delete every call internal to an already connected component. -/
def mergingWord : List (V×V) → List (V×V)
  | [] => []
  | e::w => if Nonmerging e w then mergingWord w else e::mergingWord w

/-- Retaining just the component mergers preserves every component label. -/
theorem label_mergingWord (w : List (V×V)) : label (mergingWord w)=label w := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    funext i
    by_cases h : Nonmerging e w
    · rw [mergingWord,if_pos h,ih,label]
      have he : label w e.1=label w e.2 := h
      by_cases hi : label w i=label w e.2 <;> simp only [hi,he,ite_self,if_false]
    · rw [mergingWord,if_neg h]
      simp only [label,ih]

/-- Every retained call joins different components in the reduced word. -/
theorem redundant_mergingWord (w : List (V×V)) : redundant (mergingWord w)=0 := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    by_cases h : Nonmerging e w
    · simpa only [mergingWord,if_pos h] using ih
    · have hh : ¬Nonmerging e (mergingWord w) := by simpa only [Nonmerging,label_mergingWord] using h
      simp only [mergingWord,if_neg h,redundant,if_neg hh,ih,Nat.add_zero]

/-- Inputs that can reach a call at the specified date, prior to any
subsequent propagation. -/
def eventInputs : List (V×V) → ℕ → Finset V
  | [], _ => ∅
  | e::w, k => if k=w.length then inputs w e.1 ∪ inputs w e.2 else eventInputs w k

private theorem earlier {w : List (V×V)} {i : V} {k : ℕ} (hk : k∈profile w i) : k<w.length := by
  induction w generalizing i k with
  | nil => simp [profile] at hk
  | cons e w ih =>
    simp only [List.length_cons]
    by_cases hit : i=e.1 ∨ i=e.2
    · rw [profile,if_pos hit,mergeProfiles] at hk
      have h (h : k∈profile w e.1 ∪ profile w e.2) : k<w.length+1 := by
        rcases mem_union.mp h with h|h <;> exact Nat.lt_succ_of_lt (ih h)
      by_cases hn : Nonmerging e w
      · rw [if_pos hn,mem_insert] at hk
        exact hk.elim (fun he => he ▸ Nat.lt_succ_self _) h
      · rw [if_neg hn] at hk
        exact h hk
    · rw [profile,if_neg hit] at hk
      exact Nat.lt_succ_of_lt (ih hk)

private theorem carried_inputs {w : List (V×V)} {i : V} {k : ℕ} (hk : k∈profile w i) :
    eventInputs w k ⊆ inputs w i := by
  induction w generalizing i k with
  | nil => simp [profile] at hk
  | cons e w ih =>
    by_cases hit : i=e.1 ∨ i=e.2
    · rw [profile,if_pos hit,mergeProfiles] at hk
      rw [inputs,if_pos hit]
      have h (hh : k∈profile w e.1 ∪ profile w e.2) :
          eventInputs (e::w) k ⊆ inputs w e.1 ∪ inputs w e.2 := by
        rcases mem_union.mp hh with hx|hx
        · rw [eventInputs,if_neg (earlier hx).ne]
          exact (ih hx).trans subset_union_left
        · rw [eventInputs,if_neg (earlier hx).ne]
          exact (ih hx).trans subset_union_right
      by_cases hn : Nonmerging e w
      · rw [if_pos hn,mem_insert] at hk
        rcases hk with rfl|hk
        · rw [eventInputs,if_pos rfl]; exact fun _ hx => hx
        · exact h hk
      · rw [if_neg hn] at hk
        exact h hk
    · rw [profile,if_neg hit] at hk
      rw [eventInputs,if_neg (earlier hk).ne,inputs,if_neg hit]
      exact ih hk

private theorem through_event {w : List (V×V)} {i j : V} (hh : i∈inputs w j)
    (hm : i∉inputs (mergingWord w) j) : ∃ k∈profile w j, i∈eventInputs w k := by
  induction w generalizing i j with
  | nil => exact (hm hh).elim
  | cons e w ih =>
    by_cases hit : j=e.1 ∨ j=e.2
    · rw [inputs,if_pos hit] at hh
      rw [profile,if_pos hit,mergeProfiles]
      by_cases hn : Nonmerging e w
      · exact ⟨w.length,by simp only [if_pos hn,mem_insert_self],by simpa only [eventInputs,if_pos rfl] using hh⟩
      · rw [mergingWord,if_neg hn,inputs,if_pos hit,mem_union,not_or] at hm
        rw [if_neg hn]
        rcases mem_union.mp hh with hx|hx
        · obtain ⟨k,hk,he⟩ := ih hx hm.1
          exact ⟨k,mem_union_left _ hk,by simpa only [eventInputs,if_neg (earlier hk).ne] using he⟩
        · obtain ⟨k,hk,he⟩ := ih hx hm.2
          exact ⟨k,mem_union_right _ hk,by simpa only [eventInputs,if_neg (earlier hk).ne] using he⟩
    · rw [inputs,if_neg hit] at hh
      have hm' : i∉inputs (mergingWord w) j := by
        by_cases hn : Nonmerging e w
        · simpa only [mergingWord,if_pos hn] using hm
        · simpa only [mergingWord,if_neg hn,inputs,if_neg hit] using hm
      obtain ⟨k,hk,he⟩ := ih hh hm'
      exact ⟨k,by simpa only [profile,if_neg hit] using hk,
        by simpa only [eventInputs,if_neg (earlier hk).ne] using he⟩

/-- If one output misses an input, every connection from that input
to another output with the same feedback history already exists in
the circuit containing only component mergers. -/
theorem cross_connection_in_forest (w : List (V×V)) {x y z : V}
    (hm : x∉inputs w y) (hp : profile w z=profile w y) (h : x∈inputs w z) :
    x∈inputs (mergingWord w) z := by
  by_contra hh
  obtain ⟨k,hk,hx⟩ := through_event h hh
  exact hm (carried_inputs (hp ▸ hk) hx)

#print axioms cross_connection_in_forest
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
