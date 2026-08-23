import GaloisForLFunctions.HTGeometry.GraphLocalHallSaturation

/-!
# Hasse classification by graph-local commutator observations

The complete graph-local Pauli family assembles into one simultaneous observation map.  Its kernel
is the common local kernel; for a connected graph this is exactly the global collective commutant.
Consequently global operators modulo collective symmetry are precisely the graph-local profiles
that are actually realized.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset Matrix

noncomputable section

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- Ambient operator space observed by the graph-local commutator family. -/
abbrev GraphLocalHasseSpace :=
  EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)

/-- Simultaneous graph-local commutator observation. -/
def graphLocalHasseObservation (G : SimpleGraph I) :
    GraphLocalHasseSpace (I := I) (R := R) →ₗ[ℂ]
      (∀ _ : GraphLocalIndex I G, GraphLocalHasseSpace (I := I) (R := R)) where
  toFun x j := graphLocalGenerator I R G j x
  map_add' x y := by
    funext j
    exact map_add _ _ _
  map_smul' c x := by
    funext j
    exact map_smul _ _ _

@[simp] theorem graphLocalHasseObservation_apply (G : SimpleGraph I)
    (x : GraphLocalHasseSpace (I := I) (R := R)) (j : GraphLocalIndex I G) :
    graphLocalHasseObservation (I := I) (R := R) G x j =
      graphLocalGenerator I R G j x :=
  rfl

/-- The kernel of simultaneous graph-local observation is the graph-local common kernel. -/
theorem graphLocalHasseObservation_ker (G : SimpleGraph I) :
    LinearMap.ker (graphLocalHasseObservation (I := I) (R := R) G) =
      graphLocalCommonKernel I R G := by
  ext x
  constructor
  · intro hx
    rw [mem_graphLocalCommonKernel]
    intro j
    exact congrFun (LinearMap.mem_ker.mp hx) j
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext j
    exact (mem_graphLocalCommonKernel G).mp hx j

/-- Global operators modulo simultaneous local invisibility are exactly the realized graph-local
commutator profiles. -/
noncomputable def graphLocalHasseQuotientEquivRealizedProfiles (G : SimpleGraph I) :
    (GraphLocalHasseSpace (I := I) (R := R) ⧸ graphLocalCommonKernel I R G) ≃ₗ[ℂ]
      LinearMap.range (graphLocalHasseObservation (I := I) (R := R) G) :=
  (Submodule.quotEquivOfEq _ _
    (graphLocalHasseObservation_ker (I := I) (R := R) G).symm).trans
      (LinearMap.quotKerEquivRange _)

/-- On a connected graph, quotienting by local invisibility is exactly quotienting by the global
collective commutant. -/
noncomputable def graphLocalConnectedHasseQuotientEquivRealizedProfiles
    (G : SimpleGraph I) (hconn : G.Connected) :
    (GraphLocalHasseSpace (I := I) (R := R) ⧸ collectiveCommutantSubspace I R) ≃ₗ[ℂ]
      LinearMap.range (graphLocalHasseObservation (I := I) (R := R) G) :=
  (Submodule.quotEquivOfEq _ _
    (graphLocalCommonKernel_eq_collectiveCommutant (R := R) G hconn).symm).trans
      (graphLocalHasseQuotientEquivRealizedProfiles (I := I) (R := R) G)

/-- On a connected graph, two global operators differ by a collective-commutant symmetry exactly
when every graph-local commutator observation agrees. -/
theorem graphLocalConnected_congr_hasse_iff
    (G : SimpleGraph I) (hconn : G.Connected)
    (x y : GraphLocalHasseSpace (I := I) (R := R)) :
    x - y ∈ collectiveCommutantSubspace I R ↔
      ∀ j, graphLocalGenerator I R G j x = graphLocalGenerator I R G j y := by
  rw [← graphLocalCommonKernel_eq_collectiveCommutant (R := R) G hconn,
    mem_graphLocalCommonKernel]
  exact forall_congr' fun j => by rw [map_sub, sub_eq_zero]

end

end GaloisForLFunctions.HTGeometry
