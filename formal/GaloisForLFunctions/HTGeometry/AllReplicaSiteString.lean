import GaloisForLFunctions.HTGeometry.CollectivePauliString
import GaloisForLFunctions.HTGeometry.CommutingInvolutionProduct

/-!
# The all-replica string at one physical site

Placing the same Pauli letter on one physical site in every replica gives a Pauli string that is
the product of the replica-wise single-site strings.  Since those are pairwise commuting
involutions whose sum is the collective generator at that site, every sitewise singlet commutes
with the all-replica string.
-/

open Finset Matrix

open scoped Matrix.Norms.Frobenius

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- The Pauli label carrying one letter on one physical site in every replica of a given set. -/
def replicaSetLabel (v : I) (a : Fin 3) (T : Finset R) : (I × R) → Option (Fin 3) :=
  fun q => if q.1 = v ∧ q.2 ∈ T then some a else none

variable {I R}

theorem replicaSetLabel_apply (v : I) (a : Fin 3) (T : Finset R) (q : I × R) :
    replicaSetLabel I R v a T q = if q.1 = v ∧ q.2 ∈ T then some a else none := rfl

theorem labelSupport_replicaSetLabel (v : I) (a : Fin 3) (T : Finset R) :
    labelSupport (replicaSetLabel I R v a T) =
      Finset.univ.filter fun q : I × R => q.1 = v ∧ q.2 ∈ T := by
  classical
  ext q
  rw [mem_labelSupport, replicaSetLabel_apply, Finset.mem_filter]
  by_cases h : q.1 = v ∧ q.2 ∈ T
  · simp [h]
  · simp [h]

theorem disjoint_siteLabel_replicaSetLabel {v : I} {a : Fin 3} {l : R} {T : Finset R}
    (hl : l ∉ T) :
    Disjoint (labelSupport (siteLabel ((v, l) : I × R) a))
      (labelSupport (replicaSetLabel I R v a T)) := by
  classical
  rw [labelSupport_siteLabel, labelSupport_replicaSetLabel]
  refine Finset.disjoint_left.mpr fun q hq hq' => ?_
  rw [Finset.mem_singleton] at hq
  rw [Finset.mem_filter] at hq'
  have h2 : q.2 = l := by rw [hq]
  exact hl (h2 ▸ hq'.2.2)

theorem optMulLabel_siteLabel_replicaSetLabel {v : I} {a : Fin 3} {l : R} {T : Finset R}
    (hl : l ∉ T) :
    optMulLabel (siteLabel ((v, l) : I × R) a) (replicaSetLabel I R v a T) =
      replicaSetLabel I R v a (insert l T) := by
  classical
  funext q
  show optMul (siteLabel ((v, l) : I × R) a q) (replicaSetLabel I R v a T q) = _
  rw [siteLabel_apply, replicaSetLabel_apply, replicaSetLabel_apply]
  by_cases hv : q.1 = v
  · by_cases h2l : q.2 = l
    · have hq : q = (v, l) := Prod.ext hv h2l
      rw [if_pos hq, if_neg (fun hc => hl (h2l ▸ hc.2)),
        if_pos ⟨hv, h2l ▸ Finset.mem_insert_self l T⟩]
      rfl
    · have hq : q ≠ (v, l) := fun hc => h2l (congrArg Prod.snd hc)
      by_cases ht : q.2 ∈ T
      · rw [if_neg hq, if_pos ⟨hv, ht⟩, if_pos ⟨hv, Finset.mem_insert_of_mem ht⟩]
        rfl
      · rw [if_neg hq, if_neg (fun hc => ht hc.2),
          if_neg (fun hc => (Finset.mem_insert.mp hc.2).elim h2l ht)]
        rfl
  · have hq : q ≠ (v, l) := fun hc => hv (congrArg Prod.fst hc)
    rw [if_neg hq, if_neg (fun hc => hv hc.1), if_neg (fun hc => hv hc.1)]
    rfl

/-- **The all-replica site string is the product of the replica-wise single-site strings.** -/
theorem noncommProd_siteLabel_eq (v : I) (a : Fin 3) (T : Finset R)
    (hcomm : (↑T : Set R).Pairwise (Function.onFun Commute
      (fun l => finitePauliMatrix (siteLabel ((v, l) : I × R) a)))) :
    T.noncommProd (fun l => finitePauliMatrix (siteLabel ((v, l) : I × R) a)) hcomm =
      finitePauliMatrix (replicaSetLabel I R v a T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      rw [Finset.noncommProd_empty]
      have hnone : replicaSetLabel I R v a ∅ = fun _ : I × R => (none : Option (Fin 3)) := by
        funext q
        rw [replicaSetLabel_apply, if_neg (fun hc => absurd hc.2 (Finset.notMem_empty q.2))]
      rw [hnone, finitePauliMatrix_const_none]
  | insert l T hl ih =>
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hl,
        ih (hcomm.mono (by exact_mod_cast Finset.subset_insert l T)),
        finitePauliMatrix_mul]
      show optPhaseProd (siteLabel ((v, l) : I × R) a) (replicaSetLabel I R v a T) •
        finitePauliMatrix (fun s => optMul (siteLabel ((v, l) : I × R) a s)
          (replicaSetLabel I R v a T s)) = _
      rw [optPhaseProd_eq_one_of_disjoint (disjoint_siteLabel_replicaSetLabel hl), one_smul]
      show finitePauliMatrix (optMulLabel (siteLabel ((v, l) : I × R) a)
        (replicaSetLabel I R v a T)) = _
      rw [optMulLabel_siteLabel_replicaSetLabel hl]


theorem commute_finitePauliMatrix_siteLabel {j k : I × R} (hjk : j ≠ k) (a b : Fin 3) :
    Commute (finitePauliMatrix (siteLabel j a)) (finitePauliMatrix (siteLabel k b)) := by
  show finitePauliMatrix (finiteSingleSitePauliLabel j a) *
      finitePauliMatrix (finiteSingleSitePauliLabel k b) =
    finitePauliMatrix (finiteSingleSitePauliLabel k b) *
      finitePauliMatrix (finiteSingleSitePauliLabel j a)
  rw [← finiteSingleSiteMatrix_pauli, ← finiteSingleSiteMatrix_pauli]
  exact finiteSingleSiteMatrix_pauli_comm_of_ne hjk a b

theorem sum_finitePauliMatrix_siteLabel (v : I) (a : Fin 3) :
    (∑ l : R, finitePauliMatrix (siteLabel ((v, l) : I × R) a)) =
      finiteReplicatedSiteCollectivePauli I R v a := by
  rw [finiteReplicatedSiteCollectivePauli]
  exact Finset.sum_congr rfl fun l _ => (finiteSingleSiteMatrix_pauli _ a).symm

/-- **Every sitewise singlet commutes with the all-replica string at that site.** -/
theorem commute_allReplicaSiteString_of_commute_collective {v : I} {a : Fin 3}
    {X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ}
    (hX : Commute (finiteReplicatedSiteCollectivePauli I R v a) X) :
    Commute (finitePauliMatrix (replicaSetLabel I R v a Finset.univ)) X := by
  classical
  have hall : ∀ l m : R, Commute (finitePauliMatrix (siteLabel ((v, l) : I × R) a))
      (finitePauliMatrix (siteLabel ((v, m) : I × R) a)) := by
    intro l m
    by_cases hlm : l = m
    · rw [hlm]
    · exact commute_finitePauliMatrix_siteLabel
        (fun hc => hlm (congrArg Prod.snd hc)) a a
  have hsq : ∀ l : R, finitePauliMatrix (siteLabel ((v, l) : I × R) a) *
      finitePauliMatrix (siteLabel ((v, l) : I × R) a) = 1 := fun l =>
    finitePauliMatrix_mul_self _
  have hsum : Commute (∑ l : R, finitePauliMatrix (siteLabel ((v, l) : I × R) a)) X := by
    rw [sum_finitePauliMatrix_siteLabel]
    exact hX
  have hres := commute_noncommProd_of_commute_sum
    (fun l : R => finitePauliMatrix (siteLabel ((v, l) : I × R) a)) hall hsq hsum
  rwa [noncommProd_siteLabel_eq v a Finset.univ] at hres


/-- The all-replica conjugating string at one physical site. -/
def siteConjString (I R : Type*) [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (v : I) (c : Fin 3) :
    Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ :=
  finitePauliMatrix (replicaSetLabel I R v c Finset.univ)

theorem finitePauliConjugationSign_replicaSet_replicaLabel (v : I) (c : Fin 3)
    (p : I → Option (Fin 3)) (l : R) :
    finitePauliConjugationSign (replicaSetLabel I R v c Finset.univ) (replicaLabel I R p l) =
      boolPauliConjugationSign (some c) (p v) := by
  classical
  rw [finitePauliConjugationSign, Fintype.prod_prod_type]
  rw [Finset.prod_eq_single v]
  · rw [Finset.prod_eq_single l]
    · rw [replicaSetLabel_apply, replicaLabel_apply, if_pos ⟨rfl, Finset.mem_univ l⟩, if_pos rfl]
    · intro m _ hm
      rw [replicaLabel_apply, if_neg hm, boolPauliConjugationSign]
      simp
    · intro hcon
      exact absurd (Finset.mem_univ l) hcon
  · intro i _ hi
    refine Finset.prod_eq_one fun m _ => ?_
    rw [replicaSetLabel_apply, if_neg (fun hc => hi hc.1), boolPauliConjugationSign]
    simp
  · intro hcon
    exact absurd (Finset.mem_univ v) hcon

/-- **Conjugating a collective string by an all-replica site string reproduces it with one
single-site sign.** -/
theorem siteConjString_conj_collectivePauliString (v : I) (c : Fin 3) (p : I → Option (Fin 3)) :
    siteConjString I R v c * collectivePauliString I R p * siteConjString I R v c =
      boolPauliConjugationSign (some c) (p v) • collectivePauliString I R p := by
  classical
  rw [siteConjString, collectivePauliString, Matrix.mul_sum, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [finitePauliMatrix_conj, finitePauliConjugationSign_replicaSet_replicaLabel]

end GaloisForLFunctions.HTGeometry
