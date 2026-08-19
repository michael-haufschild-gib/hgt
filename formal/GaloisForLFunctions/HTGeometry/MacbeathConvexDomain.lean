import GaloisForLFunctions.HTGeometry.MacbeathConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Macbeath's criterion on a convex domain

An open convex set is contractible, hence simply connected, and — being open in a normed space —
locally path connected.  So Macbeath's criterion applies to any group acting on it: a connected
fundamental open set with finitely many overlaps presents the group.

This is the shape in which the criterion meets arithmetic groups: the space of positive definite
forms is an open convex cone, and a Siegel set supplies the fundamental open set.

* `isFinitelyPresented_of_macbeath_convex` : **the criterion on a convex domain.**
-/

namespace GaloisForLFunctions.HTGeometry

open Set Pointwise Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] [LocallyPathConnectedSpace E]

omit [LocallyPathConnectedSpace E] in
/-- An open convex set is simply connected, locally path connected and connected. -/
theorem simplyConnectedSpace_of_convex {D : Set E} (hDconv : Convex ℝ D) (hDne : D.Nonempty) :
    SimplyConnectedSpace D :=
  haveI := hDconv.contractibleSpace hDne
  SimplyConnectedSpace.ofContractible _

omit [AddCommGroup E] [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E] in
theorem locallyPathConnectedSpace_of_isOpen {D : Set E} (hDopen : IsOpen D) :
    LocallyPathConnectedSpace D :=
  hDopen.isOpenEmbedding_subtypeVal.locallyPathConnectedSpace

omit [LocallyPathConnectedSpace E] in
theorem connectedSpace_of_convex {D : Set E} (hDconv : Convex ℝ D) (hDne : D.Nonempty) :
    ConnectedSpace D := by
  haveI := hDconv.contractibleSpace hDne
  infer_instance

/-- **Macbeath's criterion on a convex domain.**  A group acting on a nonempty open convex set, with
a connected fundamental open set whose overlap set is finite, is finitely presented. -/
theorem isFinitelyPresented_of_macbeath_convex {D : Set E} (hDopen : IsOpen D)
    (hDconv : Convex ℝ D) (hDne : D.Nonempty) {G : Type*} [Group G] [MulAction G D]
    [ContinuousConstSMul G D] {V : Set D} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVconn : IsPreconnected V) (hcover : ⋃ g : G, g • V = (univ : Set D))
    (hfin : (meetSet (G := G) V).Finite) :
    IsFinitelyPresented G := by
  haveI := simplyConnectedSpace_of_convex hDconv hDne
  haveI := locallyPathConnectedSpace_of_isOpen hDopen
  haveI := connectedSpace_of_convex hDconv hDne
  exact isFinitelyPresented_of_macbeathHom_injective hVopen hVne hcover hfin
    (macbeathHom_injective hVopen hVne hVconn hcover)

end GaloisForLFunctions.HTGeometry
