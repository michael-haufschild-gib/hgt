import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.IndependentTests
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.Packets.Unmarked

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
  obtain ⟨A,hA,x,y,hxy,hnum⟩ := unmarked_missing_pairs w F S hsize hd
  obtain ⟨T,hT,ht,hcount⟩ := independent_missing_signals w x y A (fun i hi => (hxy i hi).2.2)
  exact ⟨T,hT.trans hA,x,y,fun i hi => hxy i (hT hi),ht,by omega⟩

#print axioms packet_selection
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
