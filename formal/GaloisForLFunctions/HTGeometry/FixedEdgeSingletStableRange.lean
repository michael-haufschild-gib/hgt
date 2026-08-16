import GaloisForLFunctions.HTGeometry.ReplicaConfigurationBridge
import GaloisForLFunctions.HTGeometry.FixedEdgeSingletHallCommutant
import GaloisForLFunctions.HTGeometry.FiniteReplicaCollectiveCommutantBound

/-!
# The stable-range form of the fixed-edge Hall expansion

In the stable range the global collective commutant has dimension at most `r!`, so the defect in
the fixed-edge Hall expansion on the sitewise singlet sector is at most `r!`.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The replica regrouping of the operator space, as a linear map into the corpus's indexing. -/
def bridgeMap : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ]
    Matrix (Fin (Fintype.card R) → Fin (Fintype.card (FiniteQubitConfiguration I)))
      (Fin (Fintype.card R) → Fin (Fintype.card (FiniteQubitConfiguration I))) ℂ where
  toFun x :=
    (((vecLinearEquiv (FiniteQubitConfiguration (I × R))).symm x).submatrix
        (configCurry I R).symm (configCurry I R).symm).submatrix
      ((piRelabelEquiv (Fintype.equivFin R)
        (Fintype.equivFin (FiniteQubitConfiguration I))).symm)
      ((piRelabelEquiv (Fintype.equivFin R)
        (Fintype.equivFin (FiniteQubitConfiguration I))).symm)
  map_add' x y := by
    rw [map_add]
    rfl
  map_smul' c x := by
    rw [map_smul]
    rfl

variable {I R}

theorem submatrix_equiv_injective {m n : Type*} (e : n ≃ m) :
    Function.Injective (fun M : Matrix m m ℂ => M.submatrix e e) := by
  intro M N h
  funext i j
  have hij := congrFun (congrFun h (e.symm i)) (e.symm j)
  simpa using hij

theorem bridgeMap_injective : Function.Injective (bridgeMap I R) := by
  intro x y hxy
  refine (vecLinearEquiv (FiniteQubitConfiguration (I × R))).symm.injective ?_
  refine submatrix_equiv_injective (configCurry I R).symm ?_
  refine submatrix_equiv_injective (piRelabelEquiv (Fintype.equivFin R)
    (Fintype.equivFin (FiniteQubitConfiguration I))).symm ?_
  exact hxy


theorem bridgeMap_mem_commutant {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ collectiveCommutantSubspace I R) :
    bridgeMap I R x ∈ finiteReplicaCollectiveCommutant (Fintype.card R)
      (Fintype.card (FiniteQubitConfiguration I)) := by
  classical
  intro b a
  have hcomm : ∀ P : I → Option (Fin 3),
      collectivePauliString I R P *
          (vecLinearEquiv (FiniteQubitConfiguration (I × R))).symm x =
        (vecLinearEquiv (FiniteQubitConfiguration (I × R))).symm x *
          collectivePauliString I R P := by
    intro P
    have hzero := (mem_collectiveCommutantSubspace_iff.mp hx) P
    rw [show x = vecLinearEquiv (FiniteQubitConfiguration (I × R))
      ((vecLinearEquiv (FiniteQubitConfiguration (I × R))).symm x) from
      ((vecLinearEquiv (FiniteQubitConfiguration (I × R))).apply_symm_apply x).symm] at hzero
    exact (commutator_toEuclideanLin_eq_zero_iff _ _).mp hzero
  have hcomm1 : ∀ P : I → Option (Fin 3),
      finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) (finitePauliMatrix P) *
          (((vecLinearEquiv (FiniteQubitConfiguration (I × R))).symm x).submatrix
            (configCurry I R).symm (configCurry I R).symm) =
        (((vecLinearEquiv (FiniteQubitConfiguration (I × R))).symm x).submatrix
            (configCurry I R).symm (configCurry I R).symm) *
          finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) (finitePauliMatrix P) := by
    intro P
    rw [← submatrix_collectivePauliString P, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hcomm P]
  have hcommM := commute_finiteReplicaCollectiveMatrix_of_pauli hcomm1
  have hMback : ((Matrix.single b a (1 : ℂ)).submatrix (Fintype.equivFin
      (FiniteQubitConfiguration I)) (Fintype.equivFin (FiniteQubitConfiguration I))).submatrix
      (Fintype.equivFin (FiniteQubitConfiguration I)).symm
      (Fintype.equivFin (FiniteQubitConfiguration I)).symm = Matrix.single b a (1 : ℂ) := by
    rw [Matrix.submatrix_submatrix]
    simp
  have htrans := submatrix_finiteReplicaCollectiveMatrix (Fintype.equivFin R)
    (Fintype.equivFin (FiniteQubitConfiguration I))
    ((Matrix.single b a (1 : ℂ)).submatrix (Fintype.equivFin (FiniteQubitConfiguration I))
      (Fintype.equivFin (FiniteQubitConfiguration I)))
  rw [hMback] at htrans
  have hmove := finiteReplicaCollectiveMatrix_single_eq_replicaMoveMatrix
    (Fintype.card R) (Fintype.card (FiniteQubitConfiguration I)) b a
  rw [← hmove, ← htrans]
  have hgoal : ((finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I)
        ((Matrix.single b a (1 : ℂ)).submatrix
          (Fintype.equivFin (FiniteQubitConfiguration I))
          (Fintype.equivFin (FiniteQubitConfiguration I)))).submatrix
        ((piRelabelEquiv (Fintype.equivFin R)
          (Fintype.equivFin (FiniteQubitConfiguration I))).symm)
        ((piRelabelEquiv (Fintype.equivFin R)
          (Fintype.equivFin (FiniteQubitConfiguration I))).symm)) *
      ((((vecLinearEquiv (FiniteQubitConfiguration (I × R))).symm x).submatrix
          (configCurry I R).symm (configCurry I R).symm).submatrix
        ((piRelabelEquiv (Fintype.equivFin R)
          (Fintype.equivFin (FiniteQubitConfiguration I))).symm)
        ((piRelabelEquiv (Fintype.equivFin R)
          (Fintype.equivFin (FiniteQubitConfiguration I))).symm)) =
      ((((vecLinearEquiv (FiniteQubitConfiguration (I × R))).symm x).submatrix
          (configCurry I R).symm (configCurry I R).symm).submatrix
        ((piRelabelEquiv (Fintype.equivFin R)
          (Fintype.equivFin (FiniteQubitConfiguration I))).symm)
        ((piRelabelEquiv (Fintype.equivFin R)
          (Fintype.equivFin (FiniteQubitConfiguration I))).symm)) *
      ((finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I)
        ((Matrix.single b a (1 : ℂ)).submatrix
          (Fintype.equivFin (FiniteQubitConfiguration I))
          (Fintype.equivFin (FiniteQubitConfiguration I)))).submatrix
        ((piRelabelEquiv (Fintype.equivFin R)
          (Fintype.equivFin (FiniteQubitConfiguration I))).symm)
        ((piRelabelEquiv (Fintype.equivFin R)
          (Fintype.equivFin (FiniteQubitConfiguration I))).symm)) := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hcommM]
  exact hgoal

/-- **The global collective commutant has dimension at most `r!` in the stable range.** -/
theorem finrank_collectiveCommutantSubspace_le_factorial
    (hrd : Fintype.card R ≤ Fintype.card (FiniteQubitConfiguration I)) :
    Module.finrank ℂ (collectiveCommutantSubspace I R) ≤ Nat.factorial (Fintype.card R) := by
  classical
  set F : collectiveCommutantSubspace I R →ₗ[ℂ]
      finiteReplicaCollectiveCommutant (Fintype.card R)
        (Fintype.card (FiniteQubitConfiguration I)) :=
    { toFun := fun z => ⟨bridgeMap I R z.1, bridgeMap_mem_commutant z.2⟩
      map_add' := by
        intro z w
        exact Subtype.ext (map_add (bridgeMap I R) z.1 w.1)
      map_smul' := by
        intro c z
        exact Subtype.ext (map_smul (bridgeMap I R) c z.1) } with hF
  have hinj : Function.Injective F := by
    intro z w hzw
    exact Subtype.ext (bridgeMap_injective (congrArg Subtype.val hzw))
  calc Module.finrank ℂ (collectiveCommutantSubspace I R)
      ≤ Module.finrank ℂ (finiteReplicaCollectiveCommutant (Fintype.card R)
          (Fintype.card (FiniteQubitConfiguration I))) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ ≤ Nat.factorial (Fintype.card R) :=
        finiteReplicaCollectiveCommutant_finrank_le_factorial hrd


section StableRange

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The stable-range fixed-edge Hall expansion.**

In the stable range the defect of the fixed-edge Hall expansion on the sitewise singlet sector is
at most `r!`. -/
theorem finrank_le_edgeImages_add_factorial
    (G : SimpleGraph I) (hconn : G.Connected)
    (lf rf : E → I) (a1 a2 : E → Fin 3)
    (hadj : ∀ e : E, G.Adj (lf e) (rf e))
    (hcover : ∀ i j : I, G.Adj i j → ∃ e : E, lf e = i ∧ rf e = j)
    (hsep : ∀ e f : E, e ≠ f → ∃ v : I, (v = lf e ∨ v = rf e) ∧ v ≠ lf f ∧ v ≠ rf f)
    (hrd : Fintype.card R ≤ Fintype.card (FiniteQubitConfiguration I))
    (U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)))
    (hU : U ≤ finiteAllReplicaCollectiveSingletSubspace I R) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ ↥(⨆ e : E, Submodule.map (edgeMap lf rf a1 a2 e) U) +
        Nat.factorial (Fintype.card R) := by
  refine le_trans (finrank_le_edgeImages_add_collectiveCommutant G hconn lf rf a1 a2 hadj hcover
    hsep U hU) ?_
  refine Nat.add_le_add_left ?_ _
  calc Module.finrank ℂ ↥(U ⊓ collectiveCommutantSubspace I R)
      ≤ Module.finrank ℂ ↥(collectiveCommutantSubspace I R) :=
        Submodule.finrank_mono inf_le_right
    _ ≤ Nat.factorial (Fintype.card R) := finrank_collectiveCommutantSubspace_le_factorial hrd

end StableRange

end GaloisForLFunctions.HTGeometry
