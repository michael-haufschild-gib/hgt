import GaloisForLFunctions.HTGeometry.FixedEdgeSingletHall
import GaloisForLFunctions.HTGeometry.CollectivePauliString

/-!
# The fixed-edge Hall expansion modulo the collective commutant

Combining the synchronized-kernel theorem with the Hall inequality, the defect in the fixed-edge
Hall expansion on the sitewise singlet sector is exactly the intersection with the global
collective commutant.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The global collective commutant: operators commuting with every collectively replicated
physical Pauli string. -/
def collectiveCommutantSubspace (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R] :
    Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :=
  ⨅ P : I → Option (Fin 3),
    LinearMap.ker (matrixCommutatorRepresentation (collectivePauliString I R P)).toEuclideanLin

theorem mem_collectiveCommutantSubspace_iff
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)} :
    x ∈ collectiveCommutantSubspace I R ↔
      ∀ P : I → Option (Fin 3),
        (matrixCommutatorRepresentation (collectivePauliString I R P)).toEuclideanLin x = 0 := by
  rw [collectiveCommutantSubspace, Submodule.mem_iInf]
  rfl

section Hall

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The fixed-edge Hall expansion with the collective commutant as the exact defect.** -/
theorem finrank_le_edgeImages_add_collectiveCommutant
    (G : SimpleGraph I) (hconn : G.Connected)
    (lf rf : E → I) (a1 a2 : E → Fin 3)
    (hadj : ∀ e : E, G.Adj (lf e) (rf e))
    (hcover : ∀ i j : I, G.Adj i j → ∃ e : E, lf e = i ∧ rf e = j)
    (hsep : ∀ e f : E, e ≠ f → ∃ v : I, (v = lf e ∨ v = rf e) ∧ v ≠ lf f ∧ v ≠ rf f)
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)))
    (hU : U ≤ finiteAllReplicaCollectiveSingletSubspace I R) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ ↥(⨆ e : E, Submodule.map (edgeMap lf rf a1 a2 e) U) +
        Module.finrank ℂ ↥(U ⊓ collectiveCommutantSubspace I R) := by
  classical
  have hne : ∀ e : E, lf e ≠ rf e := fun e => (hadj e).ne
  have hkey : U ⊓ ⨅ e : E, LinearMap.ker (edgeMap lf rf a1 a2 e) =
      U ⊓ collectiveCommutantSubspace I R := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxU, hxk⟩
      refine ⟨hxU, mem_collectiveCommutantSubspace_iff.mpr fun P => ?_⟩
      rw [SetLike.mem_coe, Submodule.mem_iInf] at hxk
      refine collectivePauliString_commutator_apply_eq_zero G hconn (hU hxU) ?_ P
      intro i j hij a b
      obtain ⟨e, hle, hre⟩ := hcover i j hij
      have hzero : edgeMap lf rf a1 a2 e x = 0 := hxk e
      rw [edgeMap, hle, hre] at hzero
      exact fixedEdge_apply_eq_zero_of_axes hij.ne (a1 e) (a2 e) (hU hxU) hzero a b
    · rintro x ⟨hxU, hxc⟩
      refine ⟨hxU, ?_⟩
      rw [SetLike.mem_coe, Submodule.mem_iInf]
      intro e
      have hall := (singlet_and_edge_of_collectivePauliString_commutator
        (mem_collectiveCommutantSubspace_iff.mp hxc)).2
      exact hall (lf e) (rf e) (hne e) (a1 e) (a2 e)
  rw [← hkey]
  exact finrank_le_edgeImages_add_kernel lf rf a1 a2 hne hsep U hU

end Hall

end GaloisForLFunctions.HTGeometry
