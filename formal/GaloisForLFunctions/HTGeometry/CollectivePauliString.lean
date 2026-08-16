import GaloisForLFunctions.HTGeometry.PauliLabelGraphGeneration
import GaloisForLFunctions.HTGeometry.FixedEdgeSingletDefect
import GaloisForLFunctions.HTGeometry.PauliCharacterProjectorExtraction

/-!
# Collective replication of a physical Pauli string

A Pauli label on the physical sites is replicated by placing it on one replica at a time and
summing.  Replicas are disjointly supported, so the bracket of two collective strings is the
collective string of their label product, scaled by the same phase difference as on one replica.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- A physical label placed on one replica. -/
def replicaLabel (P : I → Option (Fin 3)) (ℓ : R) : (I × R) → Option (Fin 3) :=
  fun q => if q.2 = ℓ then P q.1 else none

/-- The collective replication of a physical Pauli label. -/
def collectivePauliString (P : I → Option (Fin 3)) :
    Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ :=
  ∑ ℓ : R, finitePauliMatrix (replicaLabel I R P ℓ)

variable {I R}

theorem replicaLabel_apply (P : I → Option (Fin 3)) (ℓ : R) (q : I × R) :
    replicaLabel I R P ℓ q = if q.2 = ℓ then P q.1 else none := rfl

theorem replicaLabel_siteLabel (v : I) (a : Fin 3) (ℓ : R) :
    replicaLabel I R (siteLabel v a) ℓ = siteLabel ((v, ℓ) : I × R) a := by
  funext q
  rw [replicaLabel_apply, siteLabel_apply, siteLabel_apply]
  by_cases h2 : q.2 = ℓ
  · by_cases h1 : q.1 = v
    · rw [if_pos h2, if_pos h1, if_pos (Prod.ext h1 h2)]
    · rw [if_pos h2, if_neg h1, if_neg (fun hc => h1 (congrArg Prod.fst hc))]
  · rw [if_neg h2, if_neg (fun hc => h2 (congrArg Prod.snd hc))]

theorem replicaLabel_pairLabel (i j : I) (a b : Fin 3) (ℓ : R) :
    replicaLabel I R (pairLabel i j a b) ℓ = pairLabel ((i, ℓ) : I × R) (j, ℓ) a b := by
  funext q
  rw [replicaLabel_apply, pairLabel_apply, pairLabel_apply]
  by_cases h2 : q.2 = ℓ
  · by_cases h1 : q.1 = i
    · rw [if_pos h2, if_pos h1, if_pos (Prod.ext h1 h2)]
    · by_cases h1' : q.1 = j
      · rw [if_pos h2, if_neg h1, if_pos h1',
          if_neg (fun hc => h1 (congrArg Prod.fst hc)), if_pos (Prod.ext h1' h2)]
      · rw [if_pos h2, if_neg h1, if_neg h1',
          if_neg (fun hc => h1 (congrArg Prod.fst hc)),
          if_neg (fun hc => h1' (congrArg Prod.fst hc))]
  · rw [if_neg h2, if_neg (fun hc => h2 (congrArg Prod.snd hc)),
      if_neg (fun hc => h2 (congrArg Prod.snd hc))]

theorem labelSupport_replicaLabel_subset (P : I → Option (Fin 3)) (ℓ : R) :
    labelSupport (replicaLabel I R P ℓ) ⊆ Finset.univ.filter fun q : I × R => q.2 = ℓ := by
  classical
  intro q hq
  rw [mem_labelSupport, replicaLabel_apply] at hq
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hc
  rw [if_neg hc] at hq
  exact hq rfl

theorem disjoint_replicaLabel {ℓ m : R} (hlm : ℓ ≠ m) (P Q : I → Option (Fin 3)) :
    Disjoint (labelSupport (replicaLabel I R P ℓ)) (labelSupport (replicaLabel I R Q m)) := by
  classical
  refine Finset.disjoint_left.mpr fun q hq hq' => ?_
  have h1 := labelSupport_replicaLabel_subset P ℓ hq
  have h2 := labelSupport_replicaLabel_subset Q m hq'
  rw [Finset.mem_filter] at h1 h2
  exact hlm (h1.2.symm.trans h2.2)

theorem optMulLabel_replicaLabel (P Q : I → Option (Fin 3)) (ℓ : R) :
    optMulLabel (replicaLabel I R P ℓ) (replicaLabel I R Q ℓ) =
      replicaLabel I R (optMulLabel P Q) ℓ := by
  funext q
  show optMul (replicaLabel I R P ℓ q) (replicaLabel I R Q ℓ q) = _
  rw [replicaLabel_apply, replicaLabel_apply, replicaLabel_apply]
  by_cases h2 : q.2 = ℓ
  · rw [if_pos h2, if_pos h2, if_pos h2]
    rfl
  · rw [if_neg h2, if_neg h2, if_neg h2]
    rfl

theorem optPhaseProd_replicaLabel (P Q : I → Option (Fin 3)) (ℓ : R) :
    optPhaseProd (replicaLabel I R P ℓ) (replicaLabel I R Q ℓ) = optPhaseProd P Q := by
  classical
  rw [optPhaseProd, optPhaseProd, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_eq_single ℓ (fun m _ hm => ?_) (fun hc => absurd (Finset.mem_univ ℓ) hc)]
  · rw [replicaLabel_apply, replicaLabel_apply, if_pos rfl, if_pos rfl]
  · rw [replicaLabel_apply, replicaLabel_apply, if_neg hm, if_neg hm, optPhase_none_left]


section SiteProducts

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem optMulLabel_siteLabel_siteLabel {v w : σ} (hvw : v ≠ w) (a b : Fin 3) :
    optMulLabel (siteLabel v a) (siteLabel w b) = pairLabel v w a b := by
  classical
  funext t
  show optMul (siteLabel v a t) (siteLabel w b t) = _
  rw [siteLabel_apply, siteLabel_apply, pairLabel_apply]
  by_cases htv : t = v <;> by_cases htw : t = w <;>
    simp [htv, htw, hvw, Ne.symm hvw, optMul_none_right, optMul]

theorem optPhaseProd_siteLabel_siteLabel {v w : σ} (hvw : v ≠ w) (a b : Fin 3) :
    optPhaseProd (siteLabel v a) (siteLabel w b) = 1 := by
  classical
  refine optPhaseProd_eq_one_of_disjoint ?_
  rw [labelSupport_siteLabel, labelSupport_siteLabel]
  exact Finset.disjoint_singleton.mpr hvw

end SiteProducts

theorem collectivePauliString_siteLabel (v : I) (a : Fin 3) :
    collectivePauliString I R (siteLabel v a) = finiteReplicatedSiteCollectivePauli I R v a := by
  rw [collectivePauliString, finiteReplicatedSiteCollectivePauli]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [replicaLabel_siteLabel, finiteSingleSiteMatrix_pauli]
  rfl

theorem collectivePauliString_pairLabel {i j : I} (hij : i ≠ j) (a b : Fin 3) :
    collectivePauliString I R (pairLabel i j a b) = fixedEdgeCollectivePauli I R i j a b := by
  rw [collectivePauliString, fixedEdgeCollectivePauli]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hne : ((i, l) : I × R) ≠ (j, l) := fun hc => hij (congrArg Prod.fst hc)
  rw [replicaLabel_pairLabel, finiteSingleSiteMatrix_pauli, finiteSingleSiteMatrix_pauli]
  have hmul : finitePauliMatrix (finiteSingleSitePauliLabel ((i, l) : I × R) a) *
      finitePauliMatrix (finiteSingleSitePauliLabel ((j, l) : I × R) b) =
      finitePauliMatrix (pairLabel ((i, l) : I × R) (j, l) a b) := by
    rw [finitePauliMatrix_mul]
    show optPhaseProd (siteLabel ((i, l) : I × R) a) (siteLabel ((j, l) : I × R) b) •
      finitePauliMatrix (fun s => optMul (siteLabel ((i, l) : I × R) a s)
        (siteLabel ((j, l) : I × R) b s)) = _
    rw [optPhaseProd_siteLabel_siteLabel hne, one_smul]
    show finitePauliMatrix (optMulLabel (siteLabel ((i, l) : I × R) a)
      (siteLabel ((j, l) : I × R) b)) = _
    rw [optMulLabel_siteLabel_siteLabel hne]
  rw [hmul]

/-- **The bracket of two collective strings is the collective string of the label product.** -/
theorem collectivePauliString_bracket (P Q : I → Option (Fin 3)) :
    ringCommutator (collectivePauliString I R P) (collectivePauliString I R Q) =
      (optPhaseProd P Q - optPhaseProd Q P) • collectivePauliString I R (optMulLabel P Q) := by
  classical
  rw [collectivePauliString, collectivePauliString, ringCommutator_sum_diagonal]
  · rw [collectivePauliString, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ringCommutator, finitePauliMatrix_mul, finitePauliMatrix_mul]
    show optPhaseProd (replicaLabel I R P l) (replicaLabel I R Q l) •
        finitePauliMatrix (optMulLabel (replicaLabel I R P l) (replicaLabel I R Q l)) -
        optPhaseProd (replicaLabel I R Q l) (replicaLabel I R P l) •
          finitePauliMatrix (optMulLabel (replicaLabel I R Q l) (replicaLabel I R P l)) = _
    rw [optMulLabel_comm (replicaLabel I R P l) (replicaLabel I R Q l),
      optMulLabel_replicaLabel, optPhaseProd_replicaLabel, optPhaseProd_replicaLabel, ← sub_smul]
  · intro l m hlm
    have hdisj := disjoint_replicaLabel hlm P Q
    rw [finitePauliMatrix_mul, finitePauliMatrix_mul]
    show optPhaseProd (replicaLabel I R P l) (replicaLabel I R Q m) •
        finitePauliMatrix (optMulLabel (replicaLabel I R P l) (replicaLabel I R Q m)) =
        optPhaseProd (replicaLabel I R Q m) (replicaLabel I R P l) •
          finitePauliMatrix (optMulLabel (replicaLabel I R Q m) (replicaLabel I R P l))
    rw [optPhaseProd_eq_one_of_disjoint hdisj, optPhaseProd_eq_one_of_disjoint hdisj.symm,
      optMulLabel_comm (replicaLabel I R P l) (replicaLabel I R Q m)]


theorem collectivePauliString_of_support_empty {P : I → Option (Fin 3)}
    (hP : labelSupport P = ∅) :
    matrixCommutatorRepresentation (collectivePauliString I R P) = 0 := by
  classical
  have hnone : ∀ i : I, P i = none := by
    intro i
    by_contra hc
    have : i ∈ labelSupport P := mem_labelSupport.mpr hc
    rw [hP] at this
    exact absurd this (Finset.notMem_empty i)
  have hrep : ∀ l : R, replicaLabel I R P l = fun _ : I × R => (none : Option (Fin 3)) := by
    intro l
    funext q
    rw [replicaLabel_apply]
    by_cases h2 : q.2 = l
    · rw [if_pos h2, hnone]
    · rw [if_neg h2]
  have hval : collectivePauliString I R P = (Fintype.card R) •
      (1 : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) := by
    rw [collectivePauliString]
    have hone : ∀ l : R, finitePauliMatrix (replicaLabel I R P l) =
        (1 : Matrix (FiniteQubitConfiguration (I × R))
          (FiniteQubitConfiguration (I × R)) ℂ) := by
      intro l
      rw [hrep l, finitePauliMatrix_const_none]
    rw [Finset.sum_congr rfl fun l _ => hone l, Finset.sum_const, Finset.card_univ]
  have hone : matrixCommutatorRepresentation (1 : Matrix (FiniteQubitConfiguration (I × R))
      (FiniteQubitConfiguration (I × R)) ℂ) = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    obtain ⟨X, rfl⟩ := Matrix.vec_bijective.2 v
    rw [matrixCommutatorRepresentation_mulVec_vec, ringCommutator, Matrix.one_mul, Matrix.mul_one,
      sub_self]
    simp
  rw [hval, map_nsmul, hone, smul_zero]

/-- **Theorem 3: the exact synchronized edge kernel.**

A sitewise singlet annihilated by every fixed-orientation edge commutator of a connected graph
commutes with the collective replication of every physical Pauli string. -/
theorem collectivePauliString_commutator_apply_eq_zero
    (G : SimpleGraph I) (hconn : G.Connected)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R)
    (hedges : ∀ i j : I, G.Adj i j → ∀ a b : Fin 3,
      (fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x = 0)
    (P : I → Option (Fin 3)) :
    (matrixCommutatorRepresentation (collectivePauliString I R P)).toEuclideanLin x = 0 := by
  classical
  by_cases hsupp : (labelSupport P).Nonempty
  · refine label_mem_of_connected G
      {Q : I → Option (Fin 3) |
        (matrixCommutatorRepresentation (collectivePauliString I R Q)).toEuclideanLin x = 0}
      hconn ?_ ?_ ?_ P hsupp
    · intro v a
      show (matrixCommutatorRepresentation
        (collectivePauliString I R (siteLabel v a))).toEuclideanLin x = 0
      rw [collectivePauliString_siteLabel]
      exact (mem_singlet_iff.mp hx) v a
    · intro i j hadj a b
      show (matrixCommutatorRepresentation
        (collectivePauliString I R (pairLabel i j a b))).toEuclideanLin x = 0
      rw [collectivePauliString_pairLabel hadj.ne]
      exact hedges i j hadj a b
    · intro Q1 Q2 h1 h2 hanti
      show (matrixCommutatorRepresentation
        (collectivePauliString I R (optMulLabel Q1 Q2))).toEuclideanLin x = 0
      have hbr := collectivePauliString_bracket (I := I) (R := R) Q1 Q2
      have hmap := congrArg matrixCommutatorRepresentation hbr
      rw [map_smul] at hmap
      have hcomm : matrixCommutatorRepresentation (ringCommutator
          (collectivePauliString I R Q1) (collectivePauliString I R Q2)) =
          matrixCommutatorRepresentation (collectivePauliString I R Q1) *
            matrixCommutatorRepresentation (collectivePauliString I R Q2) -
          matrixCommutatorRepresentation (collectivePauliString I R Q2) *
            matrixCommutatorRepresentation (collectivePauliString I R Q1) :=
        (matrixCommutatorRepresentation_bracket _ _).symm
      rw [hcomm] at hmap
      have happ := congrArg (fun M : Matrix (FiniteAllReplicaOperatorIndex I R)
        (FiniteAllReplicaOperatorIndex I R) ℂ => M.toEuclideanLin x) hmap
      simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply] at happ
      rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, h1, h2, map_zero, map_zero,
        sub_zero] at happ
      have hne : optPhaseProd Q1 Q2 - optPhaseProd Q2 Q1 ≠ 0 := sub_ne_zero_of_ne hanti
      exact (smul_eq_zero.mp happ.symm).resolve_left hne
  · rw [Finset.not_nonempty_iff_eq_empty] at hsupp
    rw [collectivePauliString_of_support_empty hsupp]
    simp


/-- **The exact synchronized edge kernel, from one fixed orientation per edge.**

A sitewise singlet annihilated by one fixed-orientation edge commutator at every edge of a
connected graph commutes with the collective replication of every physical Pauli string. -/
theorem collectivePauliString_commutator_apply_eq_zero_of_fixed
    (G : SimpleGraph I) (hconn : G.Connected) (ax1 ax2 : I → I → Fin 3)
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R)
    (hfix : ∀ i j : I, G.Adj i j →
      (fixedEdgeCommutatorMatrix I R i j (ax1 i j) (ax2 i j)).toEuclideanLin x = 0)
    (P : I → Option (Fin 3)) :
    (matrixCommutatorRepresentation (collectivePauliString I R P)).toEuclideanLin x = 0 :=
  collectivePauliString_commutator_apply_eq_zero G hconn hx
    (fun i j hadj a b =>
      fixedEdge_apply_eq_zero_of_axes hadj.ne (ax1 i j) (ax2 i j) hx (hfix i j hadj) a b) P

/-- The converse: an operator commuting with every collective string is a singlet annihilated by
every edge commutator. -/
theorem singlet_and_edge_of_collectivePauliString_commutator
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (h : ∀ P : I → Option (Fin 3),
      (matrixCommutatorRepresentation (collectivePauliString I R P)).toEuclideanLin x = 0) :
    x ∈ finiteAllReplicaCollectiveSingletSubspace I R ∧
      ∀ (i j : I) (_ : i ≠ j) (a b : Fin 3),
        (fixedEdgeCommutatorMatrix I R i j a b).toEuclideanLin x = 0 := by
  constructor
  · refine mem_singlet_iff.mpr fun v a => ?_
    have hv := h (siteLabel v a)
    rwa [collectivePauliString_siteLabel] at hv
  · intro i j hij a b
    have hij' := h (pairLabel i j a b)
    rwa [collectivePauliString_pairLabel hij] at hij'

end GaloisForLFunctions.HTGeometry
