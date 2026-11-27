import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.Cuts.Merger
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.IntervalTests
import Mathlib.Data.Finset.Union

/-! # Order certificates for all missing transmissions in a merger forest -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
variable {V : Type*} [DecidableEq V] [Fintype V]

omit [DecidableEq V] in
private theorem extend_separator {R : V→V→Prop} {A : Finset V} {S : Finset (Port V)} {i j : V}
    (hc : ∀ x y, R x y → (x∈A ↔ y∈A)) (hs : S⊆ports A)
    (h : Separates R A S i j) : Separates R univ S i j := by
  rcases h with ⟨hx,hy,he⟩|⟨hx,hy,he⟩
  · refine Or.inl ⟨hx,hy,?_⟩
    intro x _ y _ hxy hmem
    have hA := inl_mem_disjSum.mp (hs hmem)
    exact he x hA y ((hc x y hxy).mp hA) hxy hmem
  · refine Or.inr ⟨hx,hy,?_⟩
    intro x _ y _ hxy hmem
    have hA := inr_mem_disjSum.mp (hs hmem)
    exact he x ((hc x y hxy).mpr hA) y hA hxy hmem

/-- The component carriers are themselves disjoint cuts. Appending them
to the local families also separates pairs in different components. -/
theorem forest_cuts (w : List (V×V)) (hw : redundant w=0) :
    ∃ F, CutFamily (fun i j => i∈inputs w j) univ F := by
  classical
  choose F hf using component_cuts w hw
  let G l := insert (ports (wires w l)) (F l)
  have hs (l) (S : Finset (Port V)) (h : S∈G l) : S⊆ports (wires w l) :=
    (mem_insert.mp h).elim (fun he => he ▸ Subset.rfl) (fun hh => (hf l).2.1 S hh)
  have hc (l x y : V) (hh : x∈inputs w y) : x∈wires w l ↔ y∈wires w l := by
    simp only [mem_wires,label_of_input w hh]
  have member (l) {S : Finset (Port V)} (h : S∈G l) : S∈univ.biUnion G :=
    mem_biUnion.mpr ⟨l,mem_univ _,h⟩
  refine ⟨univ.biUnion G,?_,?_,?_⟩
  · intro S hS T hT
    obtain ⟨l,_,hl⟩ := mem_biUnion.mp hS
    obtain ⟨m,_,hm⟩ := mem_biUnion.mp hT
    by_cases he : l=m
    · subst m
      exact nested_insert (hf l).1 (hf l).2.1 S hl T hm
    · have hd : Disjoint (wires w l) (wires w m) :=
        disjoint_left.mpr fun x hx hy => he ((mem_wires.mp hx).symm.trans (mem_wires.mp hy))
      exact Or.inr (Or.inr ((ports_disjoint hd).mono (hs _ _ hl) (hs _ _ hm)))
  · intro S hS
    obtain ⟨l,_,hl⟩ := mem_biUnion.mp hS
    exact (hs _ _ hl).trans (disjSum_mono (subset_univ _) (subset_univ _))
  · intro i _ j _ hm
    let l := label w i
    have hi : i∈wires w l := mem_wires.mpr rfl
    by_cases hj : j∈wires w l
    · obtain ⟨S,hS,hh⟩ := (hf l).2.2 i hi j hj hm
      exact ⟨S,member l (mem_insert_of_mem hS),extend_separator (hc l) ((hf l).2.1 S hS) hh⟩
    · refine ⟨_,member l (mem_insert_self ..),Or.inl ⟨inl_mem_disjSum.mpr hi,
        fun he => hj (inr_mem_disjSum.mp he),?_⟩⟩
      intro x _ y _ hxy hx
      exact inr_mem_disjSum.mpr ((hc l x y hxy).mp (inl_mem_disjSum.mp hx))

/-- Four colors suffice for every list of missing pairs in a forest.
Within a color, two pairs cannot have both cross-connections. -/
theorem forest_four_colors {J : Type*} (w : List (V×V)) (hw : redundant w=0) (x y : J→V)
    (hm : ∀ i, x i∉inputs w (y i)) :
    ∃ c : J→Bool×Bool, ∀ i j, c i=c j → ¬(x i∈inputs w (y j) ∧ x j∈inputs w (y i)) := by
  obtain ⟨F,hF⟩ := forest_cuts w hw
  obtain ⟨r,_,hr⟩ := laminar_intervals F hF.1
  apply four_classes (fun i => r (Sum.inl (x i))) (fun i => r (Sum.inr (y i)))
  intro i
  obtain ⟨S,hS,hs⟩ := hF.2.2 (x i) (mem_univ _) (y i) (mem_univ _) (hm i)
  obtain ⟨I,hI,hmem⟩ := hr S hS
  rcases hs with ⟨hx,hy,he⟩|⟨hx,hy,he⟩
  · exact Or.inl ⟨I,hI,(hmem _).mpr hx,fun hh => hy ((hmem _).mp hh),fun j hh =>
      (hmem _).mpr (he _ (mem_univ _) _ (mem_univ _) hh hx)⟩
  · exact Or.inr ⟨I,hI,(hmem _).mpr hy,fun hh => hx ((hmem _).mp hh),fun j hh =>
      (hmem _).mpr (he _ (mem_univ _) _ (mem_univ _) hh hy)⟩

#print axioms forest_four_colors
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
