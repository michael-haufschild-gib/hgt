import GaloisForLFunctions.HTGeometry.GraphLocalPauliCovariance
import GaloisForLFunctions.HTGeometry.PauliConjugationGrading

/-!
# All-replica Pauli conjugation as a symmetry of the graph-local family

Conjugation by the all-replica Pauli string at one physical site is a self-adjoint involution that
multiplies every collective graph-local string by a single-site sign.  It therefore preserves the
family span, the simultaneous kernel with its orthogonal complement, and hence the canonical
greatest Hall obstruction.  It also fixes every sitewise singlet, so the singlet sector and its
orthogonal complement are preserved as well.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

theorem siteConjString_mul_self_smul (v : I) (c : Fin 3) :
    siteConjString I R v c * siteConjString I R v c =
      (1 : ℂ) • (1 : Matrix (FiniteQubitConfiguration (I × R))
        (FiniteQubitConfiguration (I × R)) ℂ) := by
  rw [siteConjString_mul_self, one_smul]

variable (I R)

/-- Conjugation by the all-replica site string, on the vectorized operator space. -/
def siteConjEquiv (v : I) (c : Fin 3) :
    EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) ≃ₗ[ℂ]
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
  euclideanSandwichEquiv (siteConjString I R v c) (siteConjString I R v c) 1 one_ne_zero
    (siteConjString_mul_self_smul v c) (siteConjString_mul_self_smul v c)

variable {I R}

theorem siteConjEquiv_apply_vec (v : I) (c : Fin 3)
    (X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :
    siteConjEquiv I R v c (vecLinearEquiv _ X) =
      vecLinearEquiv _ (siteConjString I R v c * X * siteConjString I R v c) := rfl

theorem siteConjEquiv_symm_apply_vec (v : I) (c : Fin 3)
    (X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :
    (siteConjEquiv I R v c).symm (vecLinearEquiv _ X) =
      vecLinearEquiv _ ((1 * 1 : ℂ)⁻¹ •
        (siteConjString I R v c * X * siteConjString I R v c)) := rfl

theorem siteConjEquiv_forward (G : SimpleGraph I) (v : I) (c : Fin 3)
    (j : GraphLocalIndex I G) :
    (((siteConjEquiv I R v c : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
        (graphLocalGenerator I R G j)).comp
      ((siteConjEquiv I R v c).symm :
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) ∈
      linearFamilyOperatorSpan (graphLocalGenerator I R G) := by
  rw [graphLocalGenerator, siteConjEquiv, euclideanSandwichEquiv_conj_commutatorOperator,
    siteConjString_conj_collectivePauliString]
  exact commutatorOperator_mem_operatorSpan G (Submodule.smul_mem _ _
    (Submodule.smul_mem _ _ (collectivePauliString_mem_graphLocalStringSpan G j)))

theorem siteConjEquiv_backward (G : SimpleGraph I) (v : I) (c : Fin 3)
    (j : GraphLocalIndex I G) :
    ((((siteConjEquiv I R v c).symm :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
        (graphLocalGenerator I R G j)).comp
      ((siteConjEquiv I R v c) :
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) ∈
      linearFamilyOperatorSpan (graphLocalGenerator I R G) := by
  rw [graphLocalGenerator, siteConjEquiv, euclideanSandwichEquiv_symm_conj_commutatorOperator,
    siteConjString_conj_collectivePauliString]
  exact commutatorOperator_mem_operatorSpan G (Submodule.smul_mem _ _
    (Submodule.smul_mem _ _ (collectivePauliString_mem_graphLocalStringSpan G j)))

theorem siteConjEquiv_starProjection_comm (G : SimpleGraph I) (v : I) (c : Fin 3)
    (x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :
    (graphLocalCommonKernel I R G).starProjection (siteConjEquiv I R v c x) =
      siteConjEquiv I R v c ((graphLocalCommonKernel I R G).starProjection x) :=
  starProjection_map_comm _ _
    (map_familyCommonKernel_le (graphLocalGenerator I R G) _ (siteConjEquiv_backward G v c))
    (map_familyCommonKernel_orthogonal_le (graphLocalGenerator I R G)
      (adjoint_graphLocalGenerator G) _ (siteConjEquiv_forward G v c)) x

theorem siteConjEquiv_forward_completed (G : SimpleGraph I) (v : I) (c : Fin 3)
    (j : Option (GraphLocalIndex I G)) :
    (((siteConjEquiv I R v c : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
        (graphLocalCompleted I R G j)).comp
      ((siteConjEquiv I R v c).symm :
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) ∈
      linearFamilyOperatorSpan (graphLocalCompleted I R G) := by
  cases j with
  | some j => exact linearFamilyOperatorSpan_le_completed G (siteConjEquiv_forward G v c j)
  | none =>
      have hfix : (((siteConjEquiv I R v c :
            EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
          (graphLocalCompleted I R G none)).comp
        ((siteConjEquiv I R v c).symm :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) =
          graphLocalCompleted I R G none := by
        refine LinearMap.ext fun x => ?_
        show siteConjEquiv I R v c
          ((graphLocalCommonKernel I R G).starProjection
            ((siteConjEquiv I R v c).symm x)) = _
        rw [← siteConjEquiv_starProjection_comm G v c ((siteConjEquiv I R v c).symm x),
          LinearEquiv.apply_symm_apply]
        rfl
      rw [hfix]
      exact Submodule.subset_span ⟨none, rfl⟩

theorem siteConjEquiv_backward_completed (G : SimpleGraph I) (v : I) (c : Fin 3)
    (j : Option (GraphLocalIndex I G)) :
    ((((siteConjEquiv I R v c).symm :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
        (graphLocalCompleted I R G j)).comp
      ((siteConjEquiv I R v c) :
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) ∈
      linearFamilyOperatorSpan (graphLocalCompleted I R G) := by
  cases j with
  | some j => exact linearFamilyOperatorSpan_le_completed G (siteConjEquiv_backward G v c j)
  | none =>
      have hfix : ((((siteConjEquiv I R v c).symm :
            EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
          (graphLocalCompleted I R G none)).comp
        ((siteConjEquiv I R v c) :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) =
          graphLocalCompleted I R G none := by
        refine LinearMap.ext fun x => ?_
        show (siteConjEquiv I R v c).symm
          ((graphLocalCommonKernel I R G).starProjection (siteConjEquiv I R v c x)) = _
        rw [siteConjEquiv_starProjection_comm G v c x, LinearEquiv.symm_apply_apply]
        rfl
      rw [hfix]
      exact Submodule.subset_span ⟨none, rfl⟩

/-- **The canonical greatest obstruction is preserved by every all-replica Pauli conjugation.** -/
theorem siteConjEquiv_mem_obstruction (G : SimpleGraph I) (v : I) (c : Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ graphLocalObstruction I R G) :
    siteConjEquiv I R v c x ∈ graphLocalObstruction I R G := by
  have hfix := linearFamilyGreatestMaximizer_map_eq_of_spanCovariant
    (graphLocalCompleted I R G) (siteConjEquiv I R v c) (siteConjEquiv I R v c)
    (siteConjEquiv_forward_completed G v c) (siteConjEquiv_backward_completed G v c)
  rw [graphLocalObstruction, ← hfix]
  exact Submodule.mem_map_of_mem hx

/-! ## The singlet sector -/

theorem graphLocalGenerator_inl (G : SimpleGraph I) (v : I) (c : Fin 3) :
    graphLocalGenerator I R G (Sum.inl (v, c)) =
      (finiteAllReplicaCollectiveCommutatorMatrix I R v c).toEuclideanLin := by
  rw [graphLocalGenerator, graphLocalLabel_inl, collectivePauliString_siteLabel]
  rfl

/-- The conjugation fixes every sitewise singlet. -/
theorem siteConjEquiv_apply_of_mem_singlet (v : I) (c : Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    siteConjEquiv I R v c x = x := by
  obtain ⟨X, rfl⟩ := (vecLinearEquiv (FiniteQubitConfiguration (I × R))).surjective x
  have hcomm : Commute (finiteReplicatedSiteCollectivePauli I R v c) X := by
    have h0 := mem_singlet_iff.mp hx v c
    rw [finiteAllReplicaCollectiveCommutatorMatrix] at h0
    exact commutator_toEuclideanLin_eq_zero_iff _ X |>.mp h0
  rw [siteConjEquiv_apply_vec, siteConjString_conj_of_commute hcomm]

/-- The conjugation is a self-adjoint involution. -/
theorem adjoint_siteConjEquiv (v : I) (c : Fin 3) :
    LinearMap.adjoint
        ((siteConjEquiv I R v c :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) =
      (siteConjEquiv I R v c : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _) := by
  have hval : (siteConjEquiv I R v c :
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _) =
      (matrixConjRepresentation (siteConjString I R v c)).toEuclideanLin := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨X, rfl⟩ := (vecLinearEquiv (FiniteQubitConfiguration (I × R))).surjective x
    rw [toEuclideanLin_conjRep_vec]
    exact siteConjEquiv_apply_vec v c X
  rw [hval, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    matrixConjRepresentation_conjTranspose (siteConjString_conjTranspose v c)]

/-- The conjugation preserves the orthogonal complement of the singlet sector. -/
theorem siteConjEquiv_mem_singlet_orthogonal (v : I) (c : Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ) :
    siteConjEquiv I R v c x ∈ (finiteAllReplicaCollectiveSingletSubspace I R)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hmove : (inner ℂ u (siteConjEquiv I R v c x) : ℂ) =
      inner ℂ (siteConjEquiv I R v c u) x := by
    rw [show ((siteConjEquiv I R v c) x) =
      (siteConjEquiv I R v c : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _) x
      from rfl, ← adjoint_siteConjEquiv (I := I) (R := R) v c, LinearMap.adjoint_inner_right]
    rfl
  rw [hmove, siteConjEquiv_apply_of_mem_singlet v c hu]
  exact (Submodule.mem_orthogonal _ _).mp hx u hu

end GaloisForLFunctions.HTGeometry
