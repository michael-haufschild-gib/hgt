import GaloisForLFunctions.HTGeometry.GraphLocalPauliFamily
import GaloisForLFunctions.HTGeometry.VandermondeCoefficientMembership

/-!
# Rational rotation covariance of the graph-local Pauli family

The replicated rational rotation at one physical site conjugates every collective graph-local
string back into the family span, so it preserves the canonical greatest Hall obstruction.  Its
conjugation action on any fixed operator is a polynomial in the rotation scale whose linear
coefficient is the collective commutator of the rotation generator.  Evaluating at enough scales
therefore forces the obstruction to be invariant under every one-site collective commutator, with
no limit and no averaging.
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

section Invariance

variable (I R)

/-- The canonical greatest Hall obstruction of the complete graph-local Pauli family. -/
def graphLocalObstruction (G : SimpleGraph I) :
    Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :=
  linearFamilyGreatestMaximizer (graphLocalGenerator I R G)

variable {I R}

/-- The greatest obstruction pulled back to the matrix algebra. -/
def graphLocalObstructionMatrix (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R]
    [DecidableEq R] (G : SimpleGraph I) :
    Submodule ℂ (Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :=
  (graphLocalObstruction I R G).comap
    ((vecLinearEquiv (FiniteQubitConfiguration (I × R)) : _ ≃ₗ[ℂ] _) :
      Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ →ₗ[ℂ]
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))

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
  classical
  set Gm := replicaGate I R v c Finset.univ s with hGm
  set Hm := replicaGate I R v c Finset.univ (-s) with hHm
  set κ := replicaGateScalar R s with hκdef
  have h1 : Gm * Hm = κ • 1 := replicaGate_mul_neg_univ v c s
  have h2 : Hm * Gm = κ • 1 := replicaGate_neg_mul_univ v c s
  set e := euclideanSandwichEquiv Gm Hm κ hs h1 h2 with he
  have hforward : ∀ j : GraphLocalIndex I G,
      (((e : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
          (graphLocalGenerator I R G j)).comp
        (e.symm : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) ∈
        linearFamilyOperatorSpan (graphLocalGenerator I R G) := by
    intro j
    rw [graphLocalGenerator, he, euclideanSandwichEquiv_conj_commutatorOperator]
    exact commutatorOperator_mem_operatorSpan G (Submodule.smul_mem _ _
      (replicaGate_conj_mem_graphLocalStringSpan G v c s j))
  have hbackward : ∀ j : GraphLocalIndex I G,
      (((e.symm : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _).comp
          (graphLocalGenerator I R G j)).comp
        (e : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _)) ∈
        linearFamilyOperatorSpan (graphLocalGenerator I R G) := by
    intro j
    rw [graphLocalGenerator, he, euclideanSandwichEquiv_symm_conj_commutatorOperator]
    have hmem := replicaGate_conj_mem_graphLocalStringSpan (I := I) (R := R) G v c (-s) j
    rw [neg_neg] at hmem
    exact commutatorOperator_mem_operatorSpan G (Submodule.smul_mem _ _ hmem)
  have hfix := linearFamilyGreatestMaximizer_map_eq_of_spanCovariant
    (graphLocalGenerator I R G) e e hforward hbackward
  have hmem : e (vecLinearEquiv (FiniteQubitConfiguration (I × R)) X) ∈
      graphLocalObstruction I R G := by
    rw [graphLocalObstruction, ← hfix]
    exact Submodule.mem_map_of_mem hX
  rwa [he, euclideanSandwichEquiv_apply_vec] at hmem

end Invariance

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
    rw [hd, hw]
    rw [← hsum]
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
  have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have := Submodule.smul_mem (graphLocalObstructionMatrix I R G) Complex.I⁻¹ hextract
  rwa [smul_smul, inv_mul_cancel₀ hIne, one_smul] at this

end GaloisForLFunctions.HTGeometry
