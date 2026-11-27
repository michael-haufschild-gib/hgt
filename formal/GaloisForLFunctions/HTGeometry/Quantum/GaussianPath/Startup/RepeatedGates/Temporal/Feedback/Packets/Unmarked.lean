import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.RepeatedBudget

/-! # Missing directed pairs on unmarked disjoint packets -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
variable {J V : Type*} [DecidableEq J] [DecidableEq V] [Nonempty V]

/-- Every packet with at least three wires and no marked endpoint
has a missing input. The discarded packets use distinct marked endpoints. -/
theorem unmarked_missing_pairs (w : List (V×V)) (F : Finset J) (S : J→Finset V)
    (hsize : ∀ i∈F, 2<(S i).card)
    (hd : ∀ i∈F, ∀ j∈F, i≠j → Disjoint (S i) (S j)) :
    ∃ A⊆F, ∃ x y : J→V, (∀ i∈A, x i∈S i ∧ y i∈S i ∧ x i∉inputs w (y i)) ∧
      F.card≤2*redundant w+A.card := by
  classical
  let M := marked w
  let A := F.filter fun i => Disjoint (S i) M
  have hA : A⊆F := filter_subset ..
  have hit (i : ↥(F \ A)) : ∃ v : M, (v:V)∈S i := by
    obtain ⟨hi,he⟩ := mem_sdiff.mp i.property
    have h : ¬Disjoint (S i) M := fun hh => he (mem_filter.mpr ⟨hi,hh⟩)
    obtain ⟨v,hv,hm⟩ := not_disjoint_iff.mp h
    exact ⟨⟨v,hm⟩,hv⟩
  choose f hf using hit
  have hf' : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hn
    have hij := hd i (mem_sdiff.mp i.property).1 j (mem_sdiff.mp j.property).1 hn
    exact disjoint_left.mp hij (hf i) (he.symm ▸ hf j)
  have hbad := card_le_card_of_injective hf'
  have choosePair (i : J) : ∃ x y : V, i∈A → x∈S i ∧ y∈S i ∧ x∉inputs w y := by
    by_cases hi : i∈A
    · have hex : ∃ x∈S i, ∃ y∈S i, x∉inputs w y := by
        by_contra! ha
        obtain ⟨v,hv,hm⟩ := exchanging_meets_marked w (S i) (hsize i (hA hi))
          (fun y hy x hx => ha x hx y hy)
        exact disjoint_left.mp (mem_filter.mp hi).2 hv hm
      obtain ⟨x,hx,y,hy,hm⟩ := hex
      exact ⟨x,y,fun _ => ⟨hx,hy,hm⟩⟩
    · exact ⟨Classical.choice inferInstance,Classical.choice inferInstance,fun h => (hi h).elim⟩
  choose x y hxy using choosePair
  have hsplit := card_sdiff_add_card_eq_card hA
  have hmark := marked_le_twice_redundant w
  change (F \ A).card≤(marked w).card at hbad
  exact ⟨A,hA,x,y,hxy,by omega⟩

#print axioms unmarked_missing_pairs
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
