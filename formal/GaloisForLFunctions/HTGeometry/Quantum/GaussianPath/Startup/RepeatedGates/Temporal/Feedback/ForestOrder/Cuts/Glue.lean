import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.Cuts.Transport

/-! # Joining two components with complete one-way cut certificates -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
variable {V : Type*} [DecidableEq V]

theorem nested_insert {U : Finset V} {F : Finset (Finset V)} (h : NestedFamily F)
    (hs : ∀ S∈F, S⊆U) : NestedFamily (insert U F) := by
  intro A ha B hb
  rcases mem_insert.mp ha with hAU|hAF <;> rcases mem_insert.mp hb with hBU|hBF
  · exact Or.inl (hAU.trans hBU.symm).le
  · exact Or.inr (Or.inl (hAU ▸ hs _ hBF))
  · exact Or.inl (hBU ▸ hs _ hAF)
  · exact h _ hAF _ hBF

theorem nested_union {F G : Finset (Finset V)} (hf : NestedFamily F) (hg : NestedFamily G)
    (hd : ∀ A∈F, ∀ B∈G, Disjoint A B) : NestedFamily (F∪G) := by
  intro A ha B hb
  rcases mem_union.mp ha with ha|ha <;> rcases mem_union.mp hb with hb|hb
  · exact hf _ ha _ hb
  · exact Or.inr (Or.inr (hd _ ha _ hb))
  · exact Or.inr (Or.inr (hd _ hb _ ha).symm)
  · exact hg _ ha _ hb

omit [DecidableEq V] in
theorem ports_disjoint {A B : Finset V} (h : Disjoint A B) : Disjoint (ports A) (ports B) := by
  apply disjoint_left.mpr
  intro p ha hb
  cases p with
  | inl x => exact disjoint_left.mp h (inl_mem_disjSum.mp ha) (inl_mem_disjSum.mp hb)
  | inr x => exact disjoint_left.mp h (inr_mem_disjSum.mp ha) (inr_mem_disjSum.mp hb)

/-- At a join every old cut faces away from its joining port. The old
component with this port removed encloses all these cuts. -/
private theorem enclosed {R : V→V→Prop} {A : Finset V} {a : V} {F : Finset (Finset (Port V))}
    (hf : CutFamily R A F) (hp : ∀ S∈F, Sum.inr a∉S) :
    NestedFamily (insert (wall A a) F) ∧ ∀ S∈insert (wall A a) F, S⊆ports A := by
  refine ⟨nested_insert hf.1 (fun S hS x hx =>
    mem_erase.mpr ⟨fun he => hp S hS (he ▸ hx),hf.2.1 S hS hx⟩),?_⟩
  intro S hS
  rcases mem_insert.mp hS with rfl|hs
  · exact erase_subset _ _
  · exact hf.2.1 S hs

/-- On the old outputs and the other joining port, a missing signal
has a separator inherited from the sender's component. For every other
output outside it, the receiving wall itself is a separator. -/
private theorem sender_separates {R T : V→V→Prop} {A B C : Finset V} {a b i j : V}
    {F : Finset (Finset (Port V))} (hf : CutFamily R A F) (hp : ∀ S∈F, Sum.inr a∉S)
    (ha : a∈A) (hA : SideRule R T A a) (hB : SideRule R T B b)
    (back : ∀ i∈A, ∀ j, (j∈A ∨ j=b) → R i (if j∈A then j else a) → T i j)
    (hi : i∈A) (hin : i∉B) (hj : j∈A ∪ B) (hm : ¬T i j) :
    (∃ S∈F, Separates T C S i j) ∨ Separates T C (wall B b) i j := by
  by_cases h : j∈A ∨ j=b
  · have hproj : (if j∈A then j else a)∈A := by split <;> assumption
    obtain ⟨S,hS,hs⟩ := hf.2.2 i hi _ hproj (fun hh => hm (back i hi j h hh))
    exact Or.inl ⟨S,hS,lift_separator hA ha (hf.2.1 S hS) (hp S hS) i j hs⟩
  · exact Or.inr (wall_separates hB hin ((mem_union.mp hj).resolve_left (fun hh => h (Or.inl hh)))
      (fun hh => h (Or.inr hh)))

/-- The union of rerooted old cuts and the two receiving walls separates
every missing input-output pair after a merger. -/
theorem join_cut_families {R T : V→V→Prop} {A B : Finset V} {a b : V}
    (ha : a∈A) (hb : b∈B) (hd : Disjoint A B)
    {F G : Finset (Finset (Port V))} (hf : CutFamily R A F) (hg : CutFamily R B G)
    (hA : SideRule R T A a) (hB : SideRule R T B b)
    (ba : ∀ i∈A, ∀ j, (j∈A ∨ j=b) → R i (if j∈A then j else a) → T i j)
    (bb : ∀ i∈B, ∀ j, (j∈B ∨ j=a) → R i (if j∈B then j else b) → T i j) :
    ∃ H, CutFamily T (A∪B) H := by
  obtain ⟨hF,hp⟩ := root_cut_family hf (Sum.inr a)
  obtain ⟨hG,hq⟩ := root_cut_family hg (Sum.inr b)
  obtain ⟨hn,hs⟩ := enclosed hF hp
  obtain ⟨hn',hs'⟩ := enclosed hG hq
  refine ⟨_,nested_union hn hn' (fun S hS P hP => (ports_disjoint hd).mono (hs S hS) (hs' P hP)),?_,?_⟩
  · intro S hS
    rcases mem_union.mp hS with h|h
    · exact (hs _ h).trans (disjSum_mono subset_union_left subset_union_left)
    · exact (hs' _ h).trans (disjSum_mono subset_union_right subset_union_right)
  · intro i hi j hj hm
    rcases mem_union.mp hi with hi|hi
    · rcases sender_separates hF hp ha hA hB ba hi (disjoint_left.mp hd hi) hj hm with ⟨S,hS,he⟩|he
      · exact ⟨S,mem_union_left _ (mem_insert_of_mem hS),he⟩
      · exact ⟨_,mem_union_right _ (mem_insert_self ..),he⟩
    · have hj' : j∈B∪A := by rwa [union_comm]
      rcases sender_separates hG hq hb hB hA bb hi (disjoint_left.mp hd.symm hi) hj' hm with ⟨S,hS,he⟩|he
      · exact ⟨S,mem_union_right _ (mem_insert_of_mem hS),he⟩
      · exact ⟨_,mem_union_left _ (mem_insert_self ..),he⟩

#print axioms join_cut_families
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
