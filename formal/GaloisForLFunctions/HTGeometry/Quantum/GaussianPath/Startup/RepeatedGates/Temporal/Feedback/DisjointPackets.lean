import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.IndependentTests
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.RepeatedBudget

/-! # Independent missing signals among disjoint packets of at least three wires -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
variable {J V : Type*} [DecidableEq J] [DecidableEq V] [Fintype V] [Nonempty V]

/-- On unmarked packets full exchange is impossible. Removing the packets
with marked endpoints and selecting compatible missing pairs loses at most
the explicit number charged to nonmerging calls. -/
theorem packet_selection (w : List (V×V)) (F : Finset J) (S : J→Finset V)
    (hsize : ∀ i∈F, 2<(S i).card)
    (hd : ∀ i∈F, ∀ j∈F, i≠j → Disjoint (S i) (S j)) :
    ∃ T⊆F, ∃ x y : J→V,
      (∀ i∈T, x i∈S i ∧ y i∈S i ∧ x i∉inputs w (y i)) ∧
      (∀ i∈T, ∀ j∈T, i≠j → ¬conflicting w x y i j) ∧
      F.card≤2*redundant w+(1+2*redundant w)*(T.card*(T.card+1)) := by
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
  obtain ⟨T,hT,ht,hcount⟩ := independent_missing_signals w x y A (fun i hi => (hxy i hi).2.2)
  have hsplit := card_sdiff_add_card_eq_card hA
  have hmark := marked_le_twice_redundant w
  exact ⟨T,hT.trans hA,x,y,fun i hi => hxy i (hT hi),ht,by
    change (F \ A).card≤(marked w).card at hbad
    omega⟩

#print axioms packet_selection
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
