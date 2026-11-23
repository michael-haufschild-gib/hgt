import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Calls

/-! # How many histories of nonmerging calls can the wires distinguish? -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
variable {V : Type*} [DecidableEq V]

/-- A call joining wires within one existing component. -/
def Nonmerging (e : V×V) (w : List (V×V)) : Prop := label w e.1=label w e.2
instance (e : V×V) (w : List (V×V)) : Decidable (Nonmerging e w) :=
  inferInstanceAs (Decidable (label w e.1=label w e.2))

/-- Number of calls whose endpoints were already connected. -/
def redundant : List (V×V) → ℕ
  | [] => 0
  | e::w => redundant w + if Nonmerging e w then 1 else 0

/-- Merge the histories and tag a nonmerging call with its date. -/
def mergeProfiles (e : V×V) (w : List (V×V)) (f : V→Finset ℕ) :=
  let S := f e.1 ∪ f e.2
  if Nonmerging e w then insert w.length S else S

/-- Dates of all nonmerging calls in the causal past of each wire. -/
def profile : List (V×V) → V → Finset ℕ
  | [], _ => ∅
  | e::w, i => if i=e.1 ∨ i=e.2 then mergeProfiles e w (profile w) else profile w i

private def histories : List (V×V) → Finset (Finset ℕ)
  | [] => {∅}
  | e::w => insert (mergeProfiles e w (profile w)) (histories w)

private theorem profile_mem (w : List (V×V)) (i : V) : profile w i ∈ histories w := by
  induction w with
  | nil => exact mem_singleton_self _
  | cons e w ih =>
    by_cases h : i=e.1 ∨ i=e.2
    · simp only [profile,if_pos h,histories,mem_insert_self]
    · rw [profile,if_neg h]
      exact mem_insert_of_mem ih

private def relabel (e : V×V) (w : List (V×V)) (i : V) :=
  if i=label w e.2 then label w e.1 else i

private def occupied : List (V×V) → Finset V
  | [] => ∅
  | e::w =>
    let A := (occupied w).image (relabel e w)
    if Nonmerging e w then insert (label w e.1) A else A

private theorem marked_component (w : List (V×V)) (i : V) (hi : profile w i≠∅) :
    label w i∈occupied w := by
  induction w generalizing i with
  | nil => exact False.elim (hi rfl)
  | cons e w ih =>
    let A := (occupied w).image (relabel e w)
    have lift (v : V) (hv : profile w v≠∅) : relabel e w (label w v)∈A :=
      mem_image_of_mem _ (ih v hv)
    have incl : A⊆occupied (e::w) := by
      by_cases h : Nonmerging e w
      · rw [occupied,if_pos h]
        exact subset_insert ..
      · rw [occupied,if_neg h]
    change relabel e w (label w i)∈_
    by_cases hit : i=e.1 ∨ i=e.2
    · have hj : relabel e w (label w i)=label w e.1 := by
        rcases hit with rfl|rfl <;> simp [relabel]
      rw [hj]
      by_cases h : Nonmerging e w
      · simp only [occupied,if_pos h,mem_insert_self]
      · rw [profile,if_pos hit,mergeProfiles,if_neg h] at hi
        by_cases h₁ : profile w e.1=∅
        · have h₂ : profile w e.2≠∅ := by intro hh; apply hi; rw [h₁,hh,union_empty]
          exact incl (by simpa [relabel] using lift e.2 h₂)
        · exact incl (by simpa [relabel] using lift e.1 h₁)
    · rw [profile,if_neg hit] at hi
      exact incl (lift i hi)

private theorem loses_component (e : V×V) (w : List (V×V)) (h : ¬Nonmerging e w)
    (ha : profile w e.1≠∅) (hb : profile w e.2≠∅) :
    (occupied (e::w)).card+1 ≤ (occupied w).card := by
  let A := occupied w
  have hx := marked_component w e.1 ha
  have hy := marked_component w e.2 hb
  have hs : A.image (relabel e w) ⊆ A.erase (label w e.2) := by
    rintro i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    by_cases hh : j=label w e.2
    · rw [relabel,if_pos hh]; exact mem_erase.mpr ⟨h,hx⟩
    · rw [relabel,if_neg hh]; exact mem_erase.mpr ⟨hh,hj⟩
  have hn := card_erase_add_one hy
  rw [occupied,if_neg h]
  exact (Nat.add_le_add_right (card_le_card hs) 1).trans_eq hn

/-- A newly marked call adds at most one history and activates at most
one component. Merging two active components pays for their new union. -/
private theorem potential (w : List (V×V)) :
    (histories w).card+(occupied w).card ≤ 1+2*redundant w := by
  induction w with
  | nil => simp [histories,occupied,redundant]
  | cons e w ih =>
    have nh := card_insert_le (mergeProfiles e w (profile w)) (histories w)
    have no := card_image_le (s:=occupied w) (f:=relabel e w)
    by_cases h : Nonmerging e w
    · have nm := card_insert_le (label w e.1) ((occupied w).image (relabel e w))
      simp only [histories,occupied,redundant,if_pos h]
      omega
    · rw [redundant,if_neg h,Nat.add_zero]
      by_cases empty : profile w e.1=∅ ∨ profile w e.2=∅
      · have hm : mergeProfiles e w (profile w)∈histories w := by
          rcases empty with h₁|h₂
          · simpa only [mergeProfiles,if_neg h,h₁,empty_union] using profile_mem w e.2
          · simpa only [mergeProfiles,if_neg h,h₂,union_empty] using profile_mem w e.1
        rw [histories,insert_eq_of_mem hm,occupied,if_neg h]
        omega
      · have hc := loses_component e w h (fun he => empty (Or.inl he)) (fun he => empty (Or.inr he))
        change (insert (mergeProfiles e w (profile w)) (histories w)).card+_≤_
        omega

/-- Among all outputs there are at most 2r+1 different sets of
nonmerging events in their past, regardless of the number of wires. -/
theorem number_of_profiles [Fintype V] (w : List (V×V)) :
    (univ.image (profile w)).card ≤ 1+2*redundant w := by
  have hs : univ.image (profile w) ⊆ histories w := by
    intro i hi
    obtain ⟨v,_,rfl⟩ := mem_image.mp hi
    exact profile_mem w v
  exact (card_le_card hs).trans ((Nat.le_add_right ..).trans (potential w))

#print axioms number_of_profiles
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
