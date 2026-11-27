import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.LaminarRanks

/-! # Choosing the side of each nested cut away from a joining port -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
variable {V : Type*} [DecidableEq V]

/-- The side of the cut A in U omitting p. -/
def away (U : Finset V) (p : V) (A : Finset V) := if p∈A then U\A else A

theorem notMem_away (U A : Finset V) (p : V) : p∉away U p A := by
  by_cases hp : p∈A <;> simp [away,hp]

theorem away_subset {U A : Finset V} (ha : A⊆U) (p : V) : away U p A⊆U := by
  unfold away
  split <;> first | exact sdiff_subset | exact ha

private theorem away_of_subset (U : Finset V) (p : V) {A B : Finset V} (h : A⊆B) :
    away U p A⊆away U p B ∨ away U p B⊆away U p A ∨ Disjoint (away U p A) (away U p B) := by
  by_cases ha : p∈A
  · simp only [away,if_pos ha,if_pos (h ha)]
    exact Or.inr (Or.inl (fun _ hx => mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1,fun he => (mem_sdiff.mp hx).2 (h he)⟩))
  by_cases hb : p∈B
  · simp only [away,if_neg ha,if_pos hb]
    exact Or.inr (Or.inr (disjoint_left.mpr fun _ hx hy => (mem_sdiff.mp hy).2 (h hx)))
  · simp only [away,if_neg ha,if_neg hb]
    exact Or.inl h

/-- Reversing all cuts through a port preserves nestedness. Sides from
different old components can therefore be placed below distinct children
of the next merger. -/
theorem away_nested {F : Finset (Finset V)} (hn : NestedFamily F) (U : Finset V) (p : V)
    (hs : ∀ A∈F, A⊆U) : NestedFamily (F.image (away U p)) := by
  intro X hX Y hY
  obtain ⟨A,ha,rfl⟩ := mem_image.mp hX
  obtain ⟨B,hb,rfl⟩ := mem_image.mp hY
  rcases hn A ha B hb with h|h|h
  · exact away_of_subset U p h
  · rcases away_of_subset U p h with h|h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h.symm)
  by_cases hA : p∈A
  · have hB := disjoint_left.mp h hA
    simp only [away,if_pos hA,if_neg hB]
    exact Or.inr (Or.inl (fun _ hx => mem_sdiff.mpr ⟨hs B hb hx,disjoint_left.mp h.symm hx⟩))
  by_cases hB : p∈B
  · simp only [away,if_neg hA,if_pos hB]
    exact Or.inl (fun _ hx => mem_sdiff.mpr ⟨hs A ha hx,disjoint_left.mp h hx⟩)
  · simp only [away,if_neg hA,if_neg hB]
    exact Or.inr (Or.inr h)

#print axioms away_nested
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
