import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.ComponentCount
import Mathlib.Data.Finset.Prod

/-! # Input and output components must meet at the intermediate wire -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
variable {V : Type*} [DecidableEq V]

/-- Every causal path visits an intermediate wire at any chosen split. -/
theorem input_at_split (u v : List (V×V)) (i j : V) (h : j∈inputs (u++v) i) :
    ∃ k∈inputs u i, j∈inputs v k := by
  induction u generalizing i with
  | nil => exact ⟨i,mem_singleton_self i,h⟩
  | cons e u ih =>
    by_cases hi : i=e.1 ∨ i=e.2
    · simp only [List.cons_append,inputs,if_pos hi,mem_union] at h ⊢
      rcases h with h|h
      · obtain ⟨k,hk,hj⟩ := ih e.1 h
        exact ⟨k,Or.inl hk,hj⟩
      · obtain ⟨k,hk,hj⟩ := ih e.2 h
        exact ⟨k,Or.inr hk,hj⟩
    · simp only [List.cons_append,inputs,if_neg hi] at h ⊢
      exact ih i h

variable [Fintype V]

/-- Ordered wire pairs with no temporal path, in output–input order. -/
def absentPairs (w : List (V×V)) : Finset (V×V) :=
  univ.filter fun p => p.2∉inputs w p.1

/-- Only N pairs of component labels can meet on N intermediate wires.
Every missing pair of labels contributes a distinct missing signal. -/
theorem component_pair_bound (u v : List (V×V)) :
    (parts u).card*(parts v).card ≤ Fintype.card V+(absentPairs (u++v)).card := by
  classical
  let cell (i : V) := (label u i,label v i)
  let coords (p : V×V) := (label u p.1,label v p.2)
  let good := univ.image cell
  let bad := (absentPairs (u++v)).image coords
  have cover : (parts u) ×ˢ (parts v) ⊆ good∪bad := by
    rintro ⟨a,b⟩ hab
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := mem_image.mp hb
    by_cases h : j∈inputs (u++v) i
    · obtain ⟨k,hu,hv⟩ := input_at_split u v i j h
      exact mem_union_left _ (mem_image.mpr ⟨k,mem_univ _,Prod.ext
        (label_of_input u hu) (label_of_input v hv).symm⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨(i,j),mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩)
  have h := (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add card_image_le card_image_le))
  simpa only [card_product,card_univ,good,bad] using h

/-- The component deficit of either half can be estimated using gate
counts alone. This version needs no connectivity data from the circuit. -/
theorem absent_pairs_of_lengths (u v : List (V×V)) :
    (Fintype.card V-u.length)*(Fintype.card V-v.length) ≤ Fintype.card V+(absentPairs (u++v)).card := by
  have h (w : List (V×V)) : Fintype.card V-w.length≤(parts w).card := by
    have := mark_budget w
    omega
  exact (Nat.mul_le_mul (h u) (h v)).trans (component_pair_bound u v)

#print axioms absent_pairs_of_lengths
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal
