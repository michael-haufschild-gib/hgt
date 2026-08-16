import GaloisForLFunctions.HTGeometry.CollectivePauliString
import GaloisForLFunctions.HTGeometry.AllReplicaTwoLocalPauliLieGeneration
import GaloisForLFunctions.HTGeometry.FiniteQubitPauliComplexBasis

/-!
# Regrouping a replicated qubit register by replica

A configuration of the register indexed by site-replica pairs is the same thing as a function from
replicas to configurations of the physical register.  Under that regrouping a Pauli string placed
on one replica becomes the corresponding physical Pauli string tensored with identities, so a
collective string becomes the collective replication of the physical Pauli matrix.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- Regrouping a replicated register configuration by replica. -/
def configCurry : FiniteQubitConfiguration (I × R) ≃ (R → FiniteQubitConfiguration I) where
  toFun x := fun r i => x (i, r)
  invFun f := fun q => f q.2 q.1
  left_inv x := by funext q; rfl
  right_inv f := by funext r i; rfl

variable {I R}

theorem configCurry_symm_apply (X : R → FiniteQubitConfiguration I) (q : I × R) :
    (configCurry I R).symm X q = X q.2 q.1 := rfl

/-- **A one-replica Pauli string is the physical string tensored with identities.** -/
theorem submatrix_finitePauliMatrix_replicaLabel (P : I → Option (Fin 3)) (l : R) :
    (finitePauliMatrix (replicaLabel I R P l)).submatrix (configCurry I R).symm
        (configCurry I R).symm =
      finiteTensorSingleSiteMatrix l (finitePauliMatrix P) := by
  classical
  ext X Y
  rw [Matrix.submatrix_apply, finitePauliMatrix, finiteTensorSingleSiteMatrix,
    finiteTensorLocalMatrix]
  rw [Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun r _ => ?_
  by_cases hrl : r = l
  · subst hrl
    rw [if_pos rfl, finitePauliMatrix]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [configCurry_symm_apply, configCurry_symm_apply, replicaLabel_apply, if_pos rfl]
  · rw [if_neg hrl]
    have hnone : ∀ i : I, replicaLabel I R P l (i, r) = none := by
      intro i
      rw [replicaLabel_apply, if_neg hrl]
    have hconst : (∏ i : I, boolPauliOptionEntry (replicaLabel I R P l (i, r))
        ((configCurry I R).symm X (i, r), (configCurry I R).symm Y (i, r))) =
        finitePauliMatrix (fun _ : I => (none : Option (Fin 3))) (X r) (Y r) := by
      rw [finitePauliMatrix]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hnone i, configCurry_symm_apply, configCurry_symm_apply]
    rw [hconst, finitePauliMatrix_const_none]

theorem submatrix_collectivePauliString (P : I → Option (Fin 3)) :
    (collectivePauliString I R P).submatrix (configCurry I R).symm (configCurry I R).symm =
      finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) (finitePauliMatrix P) := by
  classical
  rw [collectivePauliString, finiteReplicaCollectiveMatrix]
  ext X Y
  rw [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Matrix.submatrix_apply (finitePauliMatrix (replicaLabel I R P l))
    (configCurry I R).symm (configCurry I R).symm X Y,
    submatrix_finitePauliMatrix_replicaLabel]


/-- Commuting with every collectively replicated Pauli string means commuting with the collective
replication of every physical operator. -/
theorem commute_finiteReplicaCollectiveMatrix_of_pauli
    {Y : Matrix (R → FiniteQubitConfiguration I) (R → FiniteQubitConfiguration I) ℂ}
    (h : ∀ P : I → Option (Fin 3),
      finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) (finitePauliMatrix P) * Y =
        Y * finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) (finitePauliMatrix P))
    (M : Matrix (FiniteQubitConfiguration I) (FiniteQubitConfiguration I) ℂ) :
    finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) M * Y =
      Y * finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) M := by
  classical
  set S : Submodule ℂ (Matrix (FiniteQubitConfiguration I) (FiniteQubitConfiguration I) ℂ) :=
    { carrier := {N | finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) N * Y =
        Y * finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) N}
      zero_mem' := by
        have hz : finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) 0 = 0 :=
          map_zero (finiteReplicaCollectiveMatrixLinear R (FiniteQubitConfiguration I))
        show finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) 0 * Y = _
        rw [hz, Matrix.zero_mul, Matrix.mul_zero]
      add_mem' := by
        intro N1 N2 h1 h2
        have hadd : finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) (N1 + N2) =
            finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) N1 +
              finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) N2 :=
          map_add (finiteReplicaCollectiveMatrixLinear R (FiniteQubitConfiguration I)) N1 N2
        show finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) (N1 + N2) * Y = _
        rw [hadd, Matrix.add_mul, Matrix.mul_add, h1, h2]
      smul_mem' := by
        intro c N hN
        have hsm : finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) (c • N) =
            c • finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) N :=
          map_smul (finiteReplicaCollectiveMatrixLinear R (FiniteQubitConfiguration I)) c N
        show finiteReplicaCollectiveMatrix R (FiniteQubitConfiguration I) (c • N) * Y = _
        rw [hsm, Matrix.smul_mul, Matrix.mul_smul, hN] } with hS
  have hrange : Set.range (finitePauliMatrix : (I → Option (Fin 3)) →
      Matrix (FiniteQubitConfiguration I) (FiniteQubitConfiguration I) ℂ) ⊆ (S : Set _) := by
    rintro _ ⟨P, rfl⟩
    exact h P
  have htop : (⊤ : Submodule ℂ (Matrix (FiniteQubitConfiguration I)
      (FiniteQubitConfiguration I) ℂ)) ≤ S := by
    have hspan := (finitePauliMatrixBasis I).span_eq
    rw [coe_finitePauliMatrixBasis] at hspan
    rw [← hspan]
    exact Submodule.span_le.mpr hrange
  exact htop Submodule.mem_top

variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
variable {R' : Type*} [Fintype R'] [DecidableEq R']

/-- The collective replication transports along a relabelling of replicas and of the one-particle
space. -/
theorem submatrix_finiteReplicaCollectiveMatrix (eR : R ≃ R') (eD : D ≃ D')
    (M : Matrix D D ℂ) :
    (finiteReplicaCollectiveMatrix R D M).submatrix
        (fun X : R' → D' => fun r : R => eD.symm (X (eR r)))
        (fun X : R' → D' => fun r : R => eD.symm (X (eR r))) =
      finiteReplicaCollectiveMatrix R' D' (M.submatrix eD.symm eD.symm) := by
  classical
  ext X Y
  rw [Matrix.submatrix_apply, finiteReplicaCollectiveMatrix, finiteReplicaCollectiveMatrix,
    Matrix.sum_apply, Matrix.sum_apply]
  refine Fintype.sum_equiv eR _ _ fun r => ?_
  rw [finiteTensorSingleSiteMatrix, finiteTensorSingleSiteMatrix, finiteTensorLocalMatrix,
    finiteTensorLocalMatrix]
  refine Fintype.prod_equiv eR _ _ fun s => ?_
  by_cases hsr : s = r
  · rw [if_pos hsr, if_pos (by rw [hsr] : eR s = eR r), Matrix.submatrix_apply]
  · rw [if_neg hsr, if_neg (fun hc => hsr (eR.injective hc))]
    show (1 : Matrix D D ℂ) (eD.symm (X (eR s))) (eD.symm (Y (eR s))) =
      (1 : Matrix D' D' ℂ) (X (eR s)) (Y (eR s))
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hxy : X (eR s) = Y (eR s)
    · rw [if_pos hxy, if_pos (by rw [hxy])]
    · rw [if_neg hxy, if_neg (fun hc => hxy (eD.symm.injective hc))]


/-- Relabelling both the index type and the value type of a function space. -/
def piRelabelEquiv (eR : R ≃ R') (eD : D ≃ D') : (R → D) ≃ (R' → D') where
  toFun f := fun r' => eD (f (eR.symm r'))
  invFun g := fun r => eD.symm (g (eR r))
  left_inv f := by
    funext r
    simp
  right_inv g := by
    funext r'
    simp

theorem piRelabelEquiv_symm_apply (eR : R ≃ R') (eD : D ≃ D') (g : R' → D') (r : R) :
    (piRelabelEquiv eR eD).symm g r = eD.symm (g (eR r)) := rfl

/-- Vectorisation of matrices as a linear equivalence onto the Euclidean operator space. -/
def vecLinearEquiv (C : Type*) [Fintype C] [DecidableEq C] :
    Matrix C C ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (C × C) where
  toFun X := WithLp.toLp 2 (Matrix.vec X)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := Matrix.of fun i j => WithLp.ofLp x (j, i)
  left_inv _ := rfl
  right_inv _ := rfl

theorem commutator_toEuclideanLin_eq_zero_iff {C : Type*} [Fintype C] [DecidableEq C]
    (M X : Matrix C C ℂ) :
    (matrixCommutatorRepresentation M).toEuclideanLin (vecLinearEquiv C X) = 0 ↔
      M * X = X * M := by
  classical
  have hval : (matrixCommutatorRepresentation M).toEuclideanLin (vecLinearEquiv C X) =
      WithLp.toLp 2 (Matrix.vec (ringCommutator M X)) := by
    rw [Matrix.toLpLin_apply]
    exact congrArg (WithLp.toLp 2) (matrixCommutatorRepresentation_mulVec_vec M X)
  rw [hval]
  constructor
  · intro h
    have hz : Matrix.vec (ringCommutator M X) = Matrix.vec (0 : Matrix C C ℂ) := by
      funext p
      have := congrFun (congrArg WithLp.ofLp h) p
      simpa using this
    have := Matrix.vec_bijective.1 hz
    rwa [ringCommutator, sub_eq_zero] at this
  · intro h
    have hz : ringCommutator M X = 0 := by rw [ringCommutator, h, sub_self]
    rw [hz]
    have hvz : Matrix.vec (0 : Matrix C C ℂ) = 0 := by
      funext p
      rfl
    rw [hvz]
    rfl

end GaloisForLFunctions.HTGeometry
