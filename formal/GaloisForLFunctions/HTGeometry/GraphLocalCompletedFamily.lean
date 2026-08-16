import GaloisForLFunctions.HTGeometry.GraphLocalPauliFamily
import GaloisForLFunctions.HTGeometry.SelfAdjointFamilyCommonKernel

/-!
# The graph-local family completed by its kernel projector

Every graph-local generator is self-adjoint, so the orthogonal complement of the simultaneous
kernel is the span of the generator ranges.  Adjoining the orthogonal projector onto the
simultaneous kernel produces a family with trivial simultaneous kernel whose Hall condition is
exactly the sharp Hall law of the original family modulo that kernel.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

theorem collectivePauliString_isHermitian (p : I → Option (Fin 3)) :
    (collectivePauliString I R p)ᴴ = collectivePauliString I R p := by
  rw [collectivePauliString]
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun l _ => finitePauliMatrix_isHermitian _

theorem adjoint_graphLocalGenerator (G : SimpleGraph I) (j : GraphLocalIndex I G) :
    LinearMap.adjoint (graphLocalGenerator I R G j) = graphLocalGenerator I R G j := by
  show LinearMap.adjoint (Matrix.toEuclideanLin
      (matrixCommutatorRepresentation (collectivePauliString I R (graphLocalLabel G j)))) = _
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    matrixCommutatorRepresentation_conjTranspose (collectivePauliString_isHermitian _)]
  rfl

variable (I R)

/-- The simultaneous kernel of the complete graph-local Pauli family. -/
def graphLocalCommonKernel (G : SimpleGraph I) :
    Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :=
  familyCommonKernel (graphLocalGenerator I R G)

/-- The graph-local family completed by the projector onto its simultaneous kernel. -/
def graphLocalCompleted (G : SimpleGraph I) :
    Option (GraphLocalIndex I G) →
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ]
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)
  | none => ((graphLocalCommonKernel I R G).starProjection :
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →L[ℂ]
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))
  | some j => graphLocalGenerator I R G j

variable {I R}

@[simp] theorem graphLocalCompleted_some (G : SimpleGraph I) (j : GraphLocalIndex I G) :
    graphLocalCompleted I R G (some j) = graphLocalGenerator I R G j := rfl

@[simp] theorem graphLocalCompleted_none (G : SimpleGraph I)
    (x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :
    graphLocalCompleted I R G none x = (graphLocalCommonKernel I R G).starProjection x := rfl

theorem linearFamilyOperatorSpan_le_completed (G : SimpleGraph I) :
    linearFamilyOperatorSpan (graphLocalGenerator I R G) ≤
      linearFamilyOperatorSpan (graphLocalCompleted I R G) := by
  rw [linearFamilyOperatorSpan, linearFamilyOperatorSpan]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span ⟨some j, rfl⟩

theorem mem_graphLocalCommonKernel (G : SimpleGraph I)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)} :
    x ∈ graphLocalCommonKernel I R G ↔ ∀ j, graphLocalGenerator I R G j x = 0 :=
  mem_familyCommonKernel

/-- The completed shadow adds exactly the kernel component. -/
theorem linearFamilyShadow_completed (G : SimpleGraph I)
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))) :
    linearFamilyShadow (graphLocalCompleted I R G) U =
      linearFamilyShadow (graphLocalGenerator I R G) U ⊔
        U.map ((graphLocalCommonKernel I R G).starProjection :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ]
            EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) := by
  rw [linearFamilyShadow, linearFamilyShadow, iSup_option, sup_comm]
  rfl

/-- Every graph-local image is orthogonal to the simultaneous kernel. -/
theorem linearFamilyShadow_le_commonKernel_orthogonal (G : SimpleGraph I)
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))) :
    linearFamilyShadow (graphLocalGenerator I R G) U ≤ (graphLocalCommonKernel I R G)ᗮ := by
  rw [graphLocalCommonKernel,
    familyCommonKernel_orthogonal_eq (graphLocalGenerator I R G) (adjoint_graphLocalGenerator G)]
  refine iSup_le fun j => ?_
  rintro _ ⟨y, -, rfl⟩
  exact le_iSup (fun k => LinearMap.range (graphLocalGenerator I R G k)) j ⟨y, rfl⟩

end GaloisForLFunctions.HTGeometry
