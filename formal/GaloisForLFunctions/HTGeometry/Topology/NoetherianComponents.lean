import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Separation.Basic

/-!
# Finite discrete connected-component spaces of Noetherian spaces

A totally disconnected Noetherian space is finite: its finite irreducible
cover consists of subsingletons. The connected-component quotient is again
Noetherian, as a continuous surjective image, and is totally disconnected.
It is therefore finite. Its singletons are closed because connected
components are closed, so this finite quotient is discrete.

Consequently every connected component of a Noetherian space is clopen.
No separation hypothesis on the original space is required.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.NoetherianComponents
open TopologicalSpace Set
variable (X : Type*) [TopologicalSpace X]

/-- Total disconnectedness turns a Noetherian finite irreducible cover into a finite point cover. -/
theorem finite_of_noetherian_totallyDisconnected [NoetherianSpace X]
    [TotallyDisconnectedSpace X] : Finite X := by
  obtain ⟨S, hS, _, hI, he⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (α := X) isClosed_univ
  have hf : (Set.univ : Set X).Finite := by
    rw [he]
    exact hS.sUnion (fun s hs => ((hI s hs).isConnected.2.subsingleton).finite)
  exact Set.finite_univ_iff.mp hf

/-- The native connected-component quotient of a Noetherian space is Noetherian. -/
theorem connectedComponents_noetherian [NoetherianSpace X] :
    NoetherianSpace (ConnectedComponents X) :=
  noetherianSpace_of_surjective ConnectedComponents.mk ConnectedComponents.continuous_coe
    ConnectedComponents.surjective_coe

/-- Every Noetherian space has finitely many native connected components. -/
theorem connectedComponents_finite [NoetherianSpace X] : Finite (ConnectedComponents X) := by
  letI := connectedComponents_noetherian X
  exact finite_of_noetherian_totallyDisconnected (ConnectedComponents X)

/-- The finite native component space is discrete, even when the original space is not Hausdorff. -/
theorem connectedComponents_discrete [NoetherianSpace X] :
    DiscreteTopology (ConnectedComponents X) := by
  letI := connectedComponents_finite X
  haveI : T1Space (ConnectedComponents X) := ⟨fun x => by
    rw [← connectedComponent_eq_singleton x]
    exact isClosed_connectedComponent⟩
  infer_instance

/-- Each connected component of a Noetherian space is both closed and open. -/
theorem connectedComponent_isClopen [NoetherianSpace X] (x : X) :
    IsClopen (connectedComponent x) :=
  ⟨isClosed_connectedComponent,
    ConnectedComponents.discreteTopology_iff.mp (connectedComponents_discrete X) x⟩

end GaloisForLFunctions.HTGeometry.NoetherianComponents

#print axioms GaloisForLFunctions.HTGeometry.NoetherianComponents.connectedComponents_finite
#print axioms GaloisForLFunctions.HTGeometry.NoetherianComponents.connectedComponents_discrete
#print axioms GaloisForLFunctions.HTGeometry.NoetherianComponents.connectedComponent_isClopen
