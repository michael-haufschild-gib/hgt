import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Calls

/-! # Component mergers pay for the unmarked calls -/
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Distinct component labels after all calls in the word. -/
def parts (w : List (V×V)) := Finset.univ.image (label w)

private theorem parts_join (e : V×V) (w : List (V×V)) (h : label w e.1≠label w e.2) :
    parts (e::w)=(parts w).erase (label w e.2) := by
  ext i
  constructor
  · intro hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    by_cases he : label w j=label w e.2
    · simp only [label,if_pos he]
      exact Finset.mem_erase.mpr ⟨h,Finset.mem_image_of_mem _ (Finset.mem_univ e.1)⟩
    · simp only [label,if_neg he]
      exact Finset.mem_erase.mpr ⟨he,Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
  · intro hi
    obtain ⟨hne,hi⟩ := Finset.mem_erase.mp hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by simp only [label,if_neg hne]⟩

/-- With c components, at most 2(g−N+c) wires are marked after g gates. -/
theorem mark_budget (w : List (V×V)) :
    (marked w).card+2*Fintype.card V ≤ 2*(w.length+(parts w).card) := by
  induction w with
  | nil => simp [marked,parts,label]
  | cons e w ih =>
    by_cases h : label w e.1=label w e.2
    · have he : label (e::w)=label w := by
        funext i
        by_cases hi : label w i=label w e.2 <;> simp only [label,h,hi,ite_self,if_true,if_false]
      have hp : parts (e::w)=parts w := by unfold parts; rw [he]
      rw [marked,if_pos h,hp,List.length_cons]
      have h₁ := Finset.card_insert_le e.2 (marked w)
      have h₂ := Finset.card_insert_le e.1 (insert e.2 (marked w))
      omega
    · have hmem : label w e.2 ∈ parts w := Finset.mem_image_of_mem _ (Finset.mem_univ e.2)
      have hp := Finset.card_erase_add_one hmem
      rw [marked,if_neg h,parts_join e w h,List.length_cons]
      omega

end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
