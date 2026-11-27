import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.Directed.Rank
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ThreeSenders

/-! # Acyclic classes of missing input-output pairs in an arbitrary word -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
open private reduced_inputs_subset from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ThreeSenders
variable {J V : Type*} [DecidableEq V] [Fintype V]

/-- Within a forest color and a common profile, every cross-connection
of the original word has strictly increasing rank. Every nonempty
subfamily therefore has a sink unreachable from all its sources. -/
theorem feedback_ordered_classes (w : List (V×V)) (x y : J→V) (hm : ∀ i, x i∉inputs w (y i)) :
    ∃ (c : J→Bool×Bool) (z : J→ℤ), ∀ i j, c i=c j → profile w (y i)=profile w (y j) →
      x i∈inputs w (y j) → z i<z j := by
  obtain ⟨c,z,h⟩ := forest_ordered_classes (mergingWord w) (redundant_mergingWord w) x y
    (fun i hh => hm i (reduced_inputs_subset w _ hh))
  exact ⟨c,z,fun i j he hp hr => h i j he (cross_connection_in_forest w (hm i) hp.symm hr)⟩

/-- Every subfamily has a common excluded sink. Its least rank has no
incoming edge, including from a source of the same rank. -/
theorem least_sink (z : J→ℤ) (R : J→J→Prop) (T : Finset J) (ht : T.Nonempty)
    (h : ∀ i∈T, ∀ j∈T, R i j → z i<z j) : ∃ j∈T, ∀ i∈T, ¬R i j := by
  obtain ⟨j,hj,hmin⟩ := T.exists_min_image z ht
  exact ⟨j,hj,fun i hi hij => (hmin i hi).not_gt (h i hi j hj hij)⟩

#print axioms feedback_ordered_classes
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
