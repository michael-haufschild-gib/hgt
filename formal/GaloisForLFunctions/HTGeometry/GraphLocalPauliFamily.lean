import GaloisForLFunctions.HTGeometry.ReplicaRationalGate
import GaloisForLFunctions.HTGeometry.MatrixSandwichEquiv
import GaloisForLFunctions.HTGeometry.LinearFamilyGreatestMaximizer

/-!
# The complete one-site and graph-edge local Pauli family

The generators of the card are the collective commutators of the physical Pauli words supported on
a single site or on a single graph edge.  Indexing the one-site layer by a site and a letter and
the edge layer by the word itself makes the index map injective, which is what the character
separation argument needs.

Multiplying a single letter into a local word either commutes with it, or leaves its support
unchanged and therefore stays in the family.  This closure is what makes the rational rotation
gate a symmetry of the family span.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A physical Pauli word supported exactly on one edge of the graph. -/
def IsEdgeWord (G : SimpleGraph I) (p : I → Option (Fin 3)) : Prop :=
  ∃ i j : I, G.Adj i j ∧ labelSupport p = {i, j}

noncomputable instance isEdgeWordDecidablePred (G : SimpleGraph I) :
    DecidablePred (IsEdgeWord G) := fun _ => Classical.dec _

/-- The index of the complete one-site and graph-edge local Pauli family. -/
abbrev GraphLocalIndex (I : Type*) [Fintype I] [DecidableEq I] (G : SimpleGraph I) : Type _ :=
  (I × Fin 3) ⊕ {p : I → Option (Fin 3) // IsEdgeWord G p}

/-- The physical Pauli word of a family index. -/
def graphLocalLabel (G : SimpleGraph I) : GraphLocalIndex I G → (I → Option (Fin 3))
  | Sum.inl q => siteLabel q.1 q.2
  | Sum.inr p => p.1

@[simp] theorem graphLocalLabel_inl (G : SimpleGraph I) (q : I × Fin 3) :
    graphLocalLabel G (Sum.inl q) = siteLabel q.1 q.2 := rfl

@[simp] theorem graphLocalLabel_inr (G : SimpleGraph I)
    (p : {p : I → Option (Fin 3) // IsEdgeWord G p}) :
    graphLocalLabel G (Sum.inr p) = p.1 := rfl

/-! ## Single-letter multiplication and the family -/

theorem optPhaseProd_siteLabel_left (v : I) (c : Fin 3) (p : I → Option (Fin 3)) :
    optPhaseProd (siteLabel v c) p = optPhase (some c) (p v) := by
  classical
  rw [optPhaseProd, Finset.prod_eq_single v]
  · rw [siteLabel_apply, if_pos rfl]
  · intro i _ hi
    rw [siteLabel_apply, if_neg hi, optPhase_none_left]
  · intro hcon
    exact absurd (Finset.mem_univ v) hcon

theorem optPhaseProd_siteLabel_right (v : I) (c : Fin 3) (p : I → Option (Fin 3)) :
    optPhaseProd p (siteLabel v c) = optPhase (p v) (some c) := by
  classical
  rw [optPhaseProd, Finset.prod_eq_single v]
  · rw [siteLabel_apply, if_pos rfl]
  · intro i _ hi
    rw [siteLabel_apply, if_neg hi, optPhase_none_right]
  · intro hcon
    exact absurd (Finset.mem_univ v) hcon

/-- A letter fails to commute with a word only at a site carrying a different letter. -/
theorem exists_letter_of_phase_ne {v : I} {c : Fin 3} {p : I → Option (Fin 3)}
    (h : optPhaseProd (siteLabel v c) p ≠ optPhaseProd p (siteLabel v c)) :
    ∃ a : Fin 3, p v = some a ∧ a ≠ c := by
  rw [optPhaseProd_siteLabel_left, optPhaseProd_siteLabel_right] at h
  cases hpv : p v with
  | none =>
      rw [hpv, optPhase_none_right, optPhase_none_left] at h
      exact absurd rfl h
  | some a =>
      rw [hpv] at h
      refine ⟨a, rfl, fun hac => ?_⟩
      rw [hac] at h
      exact h rfl

/-- Multiplying a different letter into a word does not move its support. -/
theorem labelSupport_optMulLabel_siteLabel {v : I} {c a : Fin 3} {p : I → Option (Fin 3)}
    (hpv : p v = some a) (hac : a ≠ c) :
    labelSupport (optMulLabel (siteLabel v c) p) = labelSupport p := by
  classical
  ext i
  rw [mem_labelSupport, mem_labelSupport]
  show optMul (siteLabel v c i) (p i) ≠ none ↔ p i ≠ none
  rw [siteLabel_apply]
  by_cases hi : i = v
  · subst hi
    rw [if_pos rfl, hpv]
    constructor
    · intro _
      exact Option.some_ne_none a
    · intro _
      rw [Ne, optMul_eq_none_iff]
      exact fun hc => hac (Option.some.inj hc).symm
  · rw [if_neg hi]
    exact Iff.rfl

theorem eq_siteLabel_of_labelSupport_singleton {q : I → Option (Fin 3)} {w : I}
    (h : labelSupport q = {w}) : ∃ b : Fin 3, q = siteLabel w b := by
  classical
  have hw : q w ≠ none :=
    mem_labelSupport.mp (by rw [h]; exact Finset.mem_singleton_self w)
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hw
  refine ⟨b, ?_⟩
  funext i
  rw [siteLabel_apply]
  by_cases hi : i = w
  · rw [if_pos hi, hi, hb]
  · rw [if_neg hi]
    by_contra hc
    have hmem : i ∈ labelSupport q := mem_labelSupport.mpr hc
    rw [h, Finset.mem_singleton] at hmem
    exact hi hmem

/-- **The family is closed under multiplying a single letter into one of its words**, whenever
that multiplication does not simply commute. -/
theorem exists_graphLocalLabel_optMul (G : SimpleGraph I) (v : I) (c : Fin 3)
    (j : GraphLocalIndex I G) {a : Fin 3} (hpv : graphLocalLabel G j v = some a) (hac : a ≠ c) :
    ∃ j' : GraphLocalIndex I G,
      graphLocalLabel G j' = optMulLabel (siteLabel v c) (graphLocalLabel G j) := by
  classical
  have hsupp := labelSupport_optMulLabel_siteLabel hpv hac
  cases j with
  | inl q =>
      rw [graphLocalLabel_inl] at hsupp ⊢
      rw [labelSupport_siteLabel] at hsupp
      obtain ⟨b, hb⟩ := eq_siteLabel_of_labelSupport_singleton hsupp
      exact ⟨Sum.inl (q.1, b), hb.symm⟩
  | inr p =>
      rw [graphLocalLabel_inr] at hsupp ⊢
      obtain ⟨i, k, hik, hp⟩ := p.2
      exact ⟨Sum.inr ⟨optMulLabel (siteLabel v c) p.1, ⟨i, k, hik, hsupp.trans hp⟩⟩, rfl⟩

/-! ## The generator family -/

variable (I) (R : Type*) [Fintype R] [DecidableEq R]

/-- The collective commutator generators of the complete graph-local Pauli family. -/
def graphLocalGenerator (G : SimpleGraph I) (j : GraphLocalIndex I G) :
    EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ]
      EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) :=
  collectiveCommutatorOperator (FiniteQubitConfiguration (I × R))
    (collectivePauliString I R (graphLocalLabel G j))

variable {I R}

theorem graphLocalGenerator_apply (G : SimpleGraph I) (j : GraphLocalIndex I G)
    (X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :
    graphLocalGenerator I R G j (vecLinearEquiv _ X) =
      vecLinearEquiv _ (ringCommutator (collectivePauliString I R (graphLocalLabel G j)) X) :=
  collectiveCommutatorOperator_apply _ _

/-- The linear span of the collective strings of the family. -/
def graphLocalStringSpan (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (G : SimpleGraph I) :
    Submodule ℂ (Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :=
  Submodule.span ℂ (Set.range fun j : GraphLocalIndex I G =>
    collectivePauliString I R (graphLocalLabel G j))

theorem collectivePauliString_mem_graphLocalStringSpan (G : SimpleGraph I)
    (j : GraphLocalIndex I G) :
    collectivePauliString I R (graphLocalLabel G j) ∈ graphLocalStringSpan I R G :=
  Submodule.subset_span ⟨j, rfl⟩

/-- Every commutator action of a string in the family span lies in the family operator span. -/
theorem commutatorOperator_mem_operatorSpan (G : SimpleGraph I)
    {M : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ}
    (hM : M ∈ graphLocalStringSpan I R G) :
    collectiveCommutatorOperator (FiniteQubitConfiguration (I × R)) M ∈
      linearFamilyOperatorSpan (graphLocalGenerator I R G) := by
  classical
  have hmap : (graphLocalStringSpan I R G).map
      (collectiveCommutatorOperator (FiniteQubitConfiguration (I × R))) ≤
      linearFamilyOperatorSpan (graphLocalGenerator I R G) := by
    rw [graphLocalStringSpan, Submodule.map_span, linearFamilyOperatorSpan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨j, rfl⟩
  exact hmap ⟨M, hM, rfl⟩

end GaloisForLFunctions.HTGeometry
