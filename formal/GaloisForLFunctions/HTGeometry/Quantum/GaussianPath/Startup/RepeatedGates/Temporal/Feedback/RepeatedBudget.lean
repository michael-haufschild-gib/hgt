import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.CrossConnections
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.ComponentCount

/-! # Charging repeated calls to physical gate count -/
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
variable {V : Type*} [DecidableEq V]

/-- Deleting nonmerging calls removes exactly their number from the word. -/
theorem merger_length (w : List (V×V)) :
    (mergingWord w).length+redundant w=w.length := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    by_cases h : Nonmerging e w
    · rw [mergingWord,if_pos h,redundant,if_pos h,List.length_cons]
      omega
    · rw [mergingWord,if_neg h,redundant,if_neg h,List.length_cons,List.length_cons]
      omega

/-- Distinct marked endpoints cost at most two per nonmerging call. -/
theorem marked_le_twice_redundant (w : List (V×V)) :
    (marked w).card≤2*redundant w := by
  induction w with
  | nil => simp only [marked,redundant,Finset.card_empty,Nat.mul_zero,le_refl]
  | cons e w ih =>
    by_cases h : Nonmerging e w
    · have h' : label w e.1=label w e.2 := h
      rw [marked,if_pos h',redundant,if_pos h]
      have h₁ := Finset.card_insert_le e.2 (marked w)
      have h₂ := Finset.card_insert_le e.1 (insert e.2 (marked w))
      omega
    · have h' : label w e.1≠label w e.2 := h
      simpa only [marked,if_neg h',redundant,if_neg h,Nat.add_zero] using ih

/-- A bound on nonmerging calls gives a gate floor even when the same
pair of wires participates in many of those calls. -/
theorem repeat_budget [Fintype V] (w : List (V×V)) :
    Fintype.card V+redundant w≤w.length+(parts w).card := by
  have h := mark_budget (mergingWord w)
  have he : parts (mergingWord w)=parts w := by rw [parts,parts,label_mergingWord]
  rw [he] at h
  have hl := merger_length w
  omega

#print axioms repeat_budget
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
