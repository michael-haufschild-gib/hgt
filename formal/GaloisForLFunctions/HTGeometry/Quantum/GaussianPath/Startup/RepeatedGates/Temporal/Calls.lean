import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-! # Input sets and component labels of a sequence of two-wire calls -/
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
variable {V : Type*} [DecidableEq V]

/-- The head is the latest call. Its endpoints acquire each other's inputs. -/
def inputs : List (V×V) → V → Finset V
  | [], i => {i}
  | e::w, i => if i=e.1 ∨ i=e.2 then inputs w e.1 ∪ inputs w e.2 else inputs w i

/-- Joining components preserves the first endpoint's label. -/
def label : List (V×V) → V → V
  | [], i => i
  | e::w, i => if label w i=label w e.2 then label w e.1 else label w i

/-- Every input reaching an output has its component label. -/
theorem label_of_input (w : List (V×V)) {i j : V} (h : j ∈ inputs w i) : label w j=label w i := by
  induction w generalizing i j with
  | nil => simpa only [inputs,Finset.mem_singleton,label] using h
  | cons e w ih =>
    have lift {x y : V} (he : label w x=label w y) : label (e::w) x=label (e::w) y := by
      simp only [label,he]
    have joined : label (e::w) e.1=label (e::w) e.2 := by simp [label]
    by_cases hi : i=e.1 ∨ i=e.2
    · rw [inputs,if_pos hi,Finset.mem_union] at h
      have hx : label (e::w) j=label (e::w) e.1 := h.elim (fun h => lift (ih h))
        (fun h => (lift (ih h)).trans joined.symm)
      exact hi.elim (fun hi => hi ▸ hx) (fun hi => hi ▸ hx.trans joined)
    · rw [inputs,if_neg hi] at h
      exact lift (ih h)

/-- A call inside one previous component can change mutual communication
only at its endpoints. Mark all such endpoints. -/
def marked : List (V×V) → Finset V
  | [] => ∅
  | e::w => if label w e.1=label w e.2 then insert e.1 (insert e.2 (marked w)) else marked w

/-- A fully communicating set with at least three members cannot avoid
all marked endpoints. At a merger an untouched output puts the entire set
inside one old component, where the merger transmits no new input. -/
theorem exchanging_meets_marked (w : List (V×V)) (S : Finset V) (hS : 2<S.card)
    (hall : ∀ i∈S, S ⊆ inputs w i) : ∃ i∈S, i∈marked w := by
  induction w with
  | nil =>
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0<S.card)
    have hc := Finset.card_le_card (hall i hi)
    simp only [inputs,Finset.card_singleton] at hc
    omega
  | cons e w ih =>
    by_cases he : label w e.1=label w e.2
    · rw [marked,if_pos he]
      by_cases ha : e.1∈S
      · exact ⟨_,ha,Finset.mem_insert_self ..⟩
      by_cases hb : e.2∈S
      · exact ⟨_,hb,Finset.mem_insert_of_mem (Finset.mem_insert_self ..)⟩
      have hprev (i) (hi : i∈S) : S ⊆ inputs w i := by
        have hne : ¬(i=e.1 ∨ i=e.2) := fun h => h.elim (fun he => ha (he ▸ hi)) (fun he => hb (he ▸ hi))
        simpa only [inputs,if_neg hne] using hall i hi
      obtain ⟨i,hi,hm⟩ := ih hprev
      exact ⟨i,hi,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm)⟩
    · rw [marked,if_neg he]
      have hex : ∃ v∈S, ¬(v=e.1 ∨ v=e.2) := by
        by_contra! h
        have hs : S ⊆ {e.1,e.2} := fun i hi => by simpa only [Finset.mem_insert,Finset.mem_singleton] using h i hi
        have hsize := (Finset.card_le_card hs).trans (Finset.card_insert_le ..)
        simp only [Finset.card_singleton] at hsize
        omega
      obtain ⟨v,hv,hne⟩ := hex
      have hv' : S ⊆ inputs w v := by simpa only [inputs,if_neg hne] using hall v hv
      have same (x) (hx : x∈S) : label w x=label w v := label_of_input w (hv' hx)
      apply ih
      intro i hi j hj
      have h := hall i hi hj
      have hij := (same j hj).trans (same i hi).symm
      by_cases hit : i=e.1 ∨ i=e.2
      · rw [inputs,if_pos hit,Finset.mem_union] at h
        rcases hit with rfl | rfl
        · exact h.elim id (fun h => False.elim (he (hij.symm.trans (label_of_input w h))))
        · exact h.elim (fun h => False.elim (he ((label_of_input w h).symm.trans hij))) id
      · simpa only [inputs,if_neg hit] using h

end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
