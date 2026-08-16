import GaloisForLFunctions.HTGeometry.GraphLocalCompletedFamily
import GaloisForLFunctions.HTGeometry.VandermondeCoefficientMembership

/-!
# Rational rotation covariance of the graph-local Pauli family

The replicated rational rotation at one physical site conjugates every collective graph-local
string back into the family span, so it preserves the simultaneous kernel, the orthogonal
complement of that kernel, and hence the kernel projector.  It therefore preserves the canonical
greatest Hall obstruction of the completed family.  Its conjugation action on any fixed operator is
a polynomial in the rotation scale whose linear coefficient is the collective commutator of the
rotation generator, so evaluating at enough scales forces the obstruction to absorb every one-site
collective commutator, with no limit and no averaging.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The gate scalar: the replica power of `1 + s²`. -/
def replicaGateScalar (R : Type*) [Fintype R] (s : ℂ) : ℂ := (1 + s ^ 2) ^ Fintype.card R

theorem replicaGate_mul_neg_univ (v : I) (c : Fin 3) (s : ℂ) :
    replicaGate I R v c Finset.univ s * replicaGate I R v c Finset.univ (-s) =
      replicaGateScalar R s • 1 := by
  rw [replicaGate_mul_neg, replicaGateScalar, Finset.card_univ]

theorem replicaGate_neg_mul_univ (v : I) (c : Fin 3) (s : ℂ) :
    replicaGate I R v c Finset.univ (-s) * replicaGate I R v c Finset.univ s =
      replicaGateScalar R s • 1 := by
  have h := replicaGate_mul_neg (I := I) (R := R) v c Finset.univ (-s)
  rw [neg_neg] at h
  rw [h, replicaGateScalar, Finset.card_univ, neg_pow_two]

/-- Conjugation by the gate keeps every collective graph-local string in the family span. -/
theorem replicaGate_conj_mem_graphLocalStringSpan (G : SimpleGraph I) (v : I) (c : Fin 3) (s : ℂ)
    (j : GraphLocalIndex I G) :
    replicaGate I R v c Finset.univ s * collectivePauliString I R (graphLocalLabel G j) *
        replicaGate I R v c Finset.univ (-s) ∈ graphLocalStringSpan I R G := by
  classical
  rw [replicaGate_conj_collectivePauliString]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _
    (collectivePauliString_mem_graphLocalStringSpan G j)) ?_
  by_cases hphase : optPhaseProd (siteLabel v c) (graphLocalLabel G j) =
      optPhaseProd (graphLocalLabel G j) (siteLabel v c)
  · rw [hphase, sub_self, mul_zero, mul_zero, zero_smul]
    exact Submodule.zero_mem _
  · obtain ⟨a, hpv, hac⟩ := exists_letter_of_phase_ne hphase
    obtain ⟨j', hj'⟩ := exists_graphLocalLabel_optMul G v c j hpv hac
    rw [← hj']
    exact Submodule.smul_mem _ _ (collectivePauliString_mem_graphLocalStringSpan G j')

/-! ## The gate as a symmetry -/

variable (I R)

/-- The rational rotation gate acting on the vectorized operator space. -/
def replicaGateEquiv (v : I) (c : Fin 3) (s : ℂ) (hs : replicaGateScalar R s ≠ 0) :
    EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) ≃ₗ[ℂ]
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
  euclideanSandwichEquiv (replicaGate I R v c Finset.univ s)
    (replicaGate I R v c Finset.univ (-s)) (replicaGateScalar R s) hs
    (replicaGate_mul_neg_univ v c s) (replicaGate_neg_mul_univ v c s)

variable {I R}

theorem replicaGateEquiv_apply_vec (v : I) (c : Fin 3) (s : ℂ) (hs : replicaGateScalar R s ≠ 0)
    (X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :
    replicaGateEquiv I R v c s hs (vecLinearEquiv _ X) =
      vecLinearEquiv _ (replicaGate I R v c Finset.univ s * X *
        replicaGate I R v c Finset.univ (-s)) := rfl

theorem replicaGateEquiv_forward (G : SimpleGraph I) (v : I) (c : Fin 3) (s : ℂ)
    (hs : replicaGateScalar R s ≠ 0) (j : GraphLocalIndex I G) :
    (((replicaGateEquiv I R v c s hs :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
        (graphLocalGenerator I R G j)).comp
      ((replicaGateEquiv I R v c s hs).symm :
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) ∈
      linearFamilyOperatorSpan (graphLocalGenerator I R G) := by
  rw [graphLocalGenerator, replicaGateEquiv, euclideanSandwichEquiv_conj_commutatorOperator]
  exact commutatorOperator_mem_operatorSpan G (Submodule.smul_mem _ _
    (replicaGate_conj_mem_graphLocalStringSpan G v c s j))

theorem replicaGateEquiv_backward (G : SimpleGraph I) (v : I) (c : Fin 3) (s : ℂ)
    (hs : replicaGateScalar R s ≠ 0) (j : GraphLocalIndex I G) :
    ((((replicaGateEquiv I R v c s hs).symm :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
        (graphLocalGenerator I R G j)).comp
      ((replicaGateEquiv I R v c s hs) :
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) ∈
      linearFamilyOperatorSpan (graphLocalGenerator I R G) := by
  rw [graphLocalGenerator, replicaGateEquiv, euclideanSandwichEquiv_symm_conj_commutatorOperator]
  have hmem := replicaGate_conj_mem_graphLocalStringSpan (I := I) (R := R) G v c (-s) j
  rw [neg_neg] at hmem
  exact commutatorOperator_mem_operatorSpan G (Submodule.smul_mem _ _ hmem)

theorem replicaGateEquiv_starProjection_comm (G : SimpleGraph I) (v : I) (c : Fin 3) (s : ℂ)
    (hs : replicaGateScalar R s ≠ 0)
    (x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :
    (graphLocalCommonKernel I R G).starProjection (replicaGateEquiv I R v c s hs x) =
      replicaGateEquiv I R v c s hs ((graphLocalCommonKernel I R G).starProjection x) :=
  starProjection_map_comm _ _
    (map_familyCommonKernel_le (graphLocalGenerator I R G) _
      (replicaGateEquiv_backward G v c s hs))
    (map_familyCommonKernel_orthogonal_le (graphLocalGenerator I R G)
      (adjoint_graphLocalGenerator G) _ (replicaGateEquiv_forward G v c s hs)) x

theorem replicaGateEquiv_forward_completed (G : SimpleGraph I) (v : I) (c : Fin 3) (s : ℂ)
    (hs : replicaGateScalar R s ≠ 0) (j : Option (GraphLocalIndex I G)) :
    (((replicaGateEquiv I R v c s hs :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
        (graphLocalCompleted I R G j)).comp
      ((replicaGateEquiv I R v c s hs).symm :
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) ∈
      linearFamilyOperatorSpan (graphLocalCompleted I R G) := by
  cases j with
  | some j =>
      exact linearFamilyOperatorSpan_le_completed G (replicaGateEquiv_forward G v c s hs j)
  | none =>
      have hfix : (((replicaGateEquiv I R v c s hs :
            EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
          (graphLocalCompleted I R G none)).comp
        ((replicaGateEquiv I R v c s hs).symm :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) =
          graphLocalCompleted I R G none := by
        refine LinearMap.ext fun x => ?_
        show replicaGateEquiv I R v c s hs
          ((graphLocalCommonKernel I R G).starProjection
            ((replicaGateEquiv I R v c s hs).symm x)) = _
        rw [← replicaGateEquiv_starProjection_comm G v c s hs
          ((replicaGateEquiv I R v c s hs).symm x), LinearEquiv.apply_symm_apply]
        rfl
      rw [hfix]
      exact Submodule.subset_span ⟨none, rfl⟩

theorem replicaGateEquiv_backward_completed (G : SimpleGraph I) (v : I) (c : Fin 3) (s : ℂ)
    (hs : replicaGateScalar R s ≠ 0) (j : Option (GraphLocalIndex I G)) :
    ((((replicaGateEquiv I R v c s hs).symm :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
        (graphLocalCompleted I R G j)).comp
      ((replicaGateEquiv I R v c s hs) :
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) ∈
      linearFamilyOperatorSpan (graphLocalCompleted I R G) := by
  cases j with
  | some j =>
      exact linearFamilyOperatorSpan_le_completed G (replicaGateEquiv_backward G v c s hs j)
  | none =>
      have hfix : ((((replicaGateEquiv I R v c s hs).symm :
            EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
          (graphLocalCompleted I R G none)).comp
        ((replicaGateEquiv I R v c s hs) :
          EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) =
          graphLocalCompleted I R G none := by
        refine LinearMap.ext fun x => ?_
        show (replicaGateEquiv I R v c s hs).symm
          ((graphLocalCommonKernel I R G).starProjection
            (replicaGateEquiv I R v c s hs x)) = _
        rw [replicaGateEquiv_starProjection_comm G v c s hs x, LinearEquiv.symm_apply_apply]
        rfl
      rw [hfix]
      exact Submodule.subset_span ⟨none, rfl⟩

/-! ## The canonical greatest obstruction -/

variable (I R)

/-- The canonical greatest Hall obstruction of the completed graph-local Pauli family. -/
def graphLocalObstruction (G : SimpleGraph I) :
    Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :=
  linearFamilyGreatestMaximizer (graphLocalCompleted I R G)

/-- The greatest obstruction pulled back to the matrix algebra. -/
def graphLocalObstructionMatrix (G : SimpleGraph I) :
    Submodule ℂ (Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :=
  (graphLocalObstruction I R G).comap
    ((vecLinearEquiv (FiniteQubitConfiguration (I × R)) : _ ≃ₗ[ℂ] _) :
      Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ →ₗ[ℂ]
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))

variable {I R}

theorem mem_graphLocalObstructionMatrix (G : SimpleGraph I)
    {X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ} :
    X ∈ graphLocalObstructionMatrix I R G ↔
      vecLinearEquiv (FiniteQubitConfiguration (I × R)) X ∈ graphLocalObstruction I R G :=
  Iff.rfl

/-- **Every rational rotation gate preserves the canonical greatest obstruction.** -/
theorem replicaGate_sandwich_mem_obstruction (G : SimpleGraph I) (v : I) (c : Fin 3) (s : ℂ)
    (hs : replicaGateScalar R s ≠ 0)
    {X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ}
    (hX : X ∈ graphLocalObstructionMatrix I R G) :
    replicaGate I R v c Finset.univ s * X * replicaGate I R v c Finset.univ (-s) ∈
      graphLocalObstructionMatrix I R G := by
  have hfix := linearFamilyGreatestMaximizer_map_eq_of_spanCovariant
    (graphLocalCompleted I R G) (replicaGateEquiv I R v c s hs) (replicaGateEquiv I R v c s hs)
    (replicaGateEquiv_forward_completed G v c s hs) (replicaGateEquiv_backward_completed G v c s hs)
  have hmem : replicaGateEquiv I R v c s hs
      (vecLinearEquiv (FiniteQubitConfiguration (I × R)) X) ∈ graphLocalObstruction I R G := by
    rw [graphLocalObstruction, ← hfix]
    exact Submodule.mem_map_of_mem hX
  rwa [replicaGateEquiv_apply_vec] at hmem

/-- **The canonical greatest obstruction absorbs every one-site collective commutator.** -/
theorem ringCommutator_siteLabel_mem_obstruction (G : SimpleGraph I) (v : I) (c : Fin 3)
    {X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ}
    (hX : X ∈ graphLocalObstructionMatrix I R G) :
    ringCommutator (collectivePauliString I R (siteLabel v c)) X ∈
      graphLocalObstructionMatrix I R G := by
  classical
  set n := 2 * Fintype.card R + 2 with hn
  have hdeg : ∀ a : Finset R × Finset R, a.1.card + a.2.card < n := by
    intro a
    have h1 : a.1.card ≤ Fintype.card R := by
      simpa [Finset.card_univ] using Finset.card_le_univ a.1
    have h2 : a.2.card ≤ Fintype.card R := by
      simpa [Finset.card_univ] using Finset.card_le_univ a.2
    omega
  set d : Finset R × Finset R → Fin n := fun a => ⟨a.1.card + a.2.card, hdeg a⟩ with hd
  set w : Finset R × Finset R →
      Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ :=
    fun a => (Complex.I ^ a.1.card * (-Complex.I) ^ a.2.card) •
      (finitePauliMatrix (replicaSetLabel I R v c a.1) * X *
        finitePauliMatrix (replicaSetLabel I R v c a.2)) with hw
  set pts : Fin n → ℂ := fun i => ((i : ℕ) : ℂ) with hpts
  have hptsinj : Function.Injective pts := by
    intro i j hij
    exact Fin.ext (Nat.cast_injective hij)
  have hscalar : ∀ i : Fin n, replicaGateScalar R (pts i) ≠ 0 := by
    intro i
    refine pow_ne_zero _ ?_
    have hcast : (1 : ℂ) + ((i : ℕ) : ℂ) ^ 2 = ((1 + (i : ℕ) ^ 2 : ℕ) : ℂ) := by
      push_cast
      ring
    rw [hpts, hcast]
    exact Nat.cast_ne_zero.mpr (by positivity)
  have hmem : ∀ i : Fin n, (∑ a : Finset R × Finset R, pts i ^ ((d a : ℕ)) • w a) ∈
      graphLocalObstructionMatrix I R G := by
    intro i
    have hsum := replicaGate_sandwich_eq_gradedSum (I := I) (R := R) v c (pts i) X
    rw [hd, hw, ← hsum]
    exact replicaGate_sandwich_mem_obstruction G v c (pts i) (hscalar i) hX
  have hone : (1 : ℕ) < n := by omega
  have hextract := mem_of_forall_gradedSum_mem (graphLocalObstructionMatrix I R G) d w pts
    hptsinj hmem ⟨1, hone⟩
  have hfilter : (Finset.univ.filter fun a : Finset R × Finset R => d a = ⟨1, hone⟩) =
      (Finset.univ.filter fun a : Finset R × Finset R => a.1.card + a.2.card = 1) := by
    apply Finset.filter_congr
    intro a _
    rw [hd]
    exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  rw [hfilter, hw] at hextract
  have hval := replicaGate_gradedSum_degree_one (I := I) (R := R) v c X
  rw [hval] at hextract
  have hsmul := Submodule.smul_mem (graphLocalObstructionMatrix I R G) Complex.I⁻¹ hextract
  rwa [smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul] at hsmul

end GaloisForLFunctions.HTGeometry
