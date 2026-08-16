import GaloisForLFunctions.HTGeometry.PauliCommutatorCoefficient

/-!
# Supports of Pauli labels under multiplication

The support of a product of Pauli labels lies inside the union of the two supports and contains
their symmetric difference.  Labels with disjoint supports commute, so only overlapping pairs can
contribute to a commutator coefficient, and a product supported on three sites forces both factors
to be two-site labels overlapping in exactly one site.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The set of sites where a Pauli label is nontrivial. -/
def labelSupport (S : σ → Option (Fin 3)) : Finset σ :=
  Finset.univ.filter fun s => S s ≠ none

theorem mem_labelSupport {S : σ → Option (Fin 3)} {s : σ} :
    s ∈ labelSupport S ↔ S s ≠ none := by
  rw [labelSupport, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem optMul_eq_none_iff (p q : Option (Fin 3)) : optMul p q = none ↔ p = q := by
  cases p with
  | none =>
      cases q with
      | none => simp [optMul]
      | some b => simp [optMul]
  | some a =>
      cases q with
      | none => simp [optMul]
      | some b =>
          by_cases h : a = b
          · subst h
            simp [optMul]
          · simp [optMul, h]

theorem labelSupport_optMulLabel_subset (S T : σ → Option (Fin 3)) :
    labelSupport (optMulLabel S T) ⊆ labelSupport S ∪ labelSupport T := by
  intro s hs
  rw [mem_labelSupport] at hs
  rw [Finset.mem_union, mem_labelSupport, mem_labelSupport]
  by_contra hcon
  refine hs ?_
  have hS : S s = none := not_not.mp fun h => hcon (Or.inl h)
  have hT : T s = none := not_not.mp fun h => hcon (Or.inr h)
  show optMul (S s) (T s) = none
  rw [hS, hT]
  rfl

theorem mem_labelSupport_optMulLabel_of_left {S T : σ → Option (Fin 3)} {s : σ}
    (hS : S s ≠ none) (hT : T s = none) : s ∈ labelSupport (optMulLabel S T) := by
  rw [mem_labelSupport]
  show optMul (S s) (T s) ≠ none
  rw [hT, optMul_none_right]
  exact hS

theorem mem_labelSupport_optMulLabel_of_right {S T : σ → Option (Fin 3)} {s : σ}
    (hS : S s = none) (hT : T s ≠ none) : s ∈ labelSupport (optMulLabel S T) := by
  rw [mem_labelSupport]
  show optMul (S s) (T s) ≠ none
  rw [hS]
  exact hT

/-- **Labels with disjoint supports commute.** -/
theorem optPhaseProd_eq_one_of_disjoint {S T : σ → Option (Fin 3)}
    (h : Disjoint (labelSupport S) (labelSupport T)) : optPhaseProd S T = 1 := by
  rw [optPhaseProd]
  refine Finset.prod_eq_one fun s _ => ?_
  by_cases hS : S s = none
  · rw [hS]
    rfl
  · have hT : T s = none := by
      by_contra hcon
      exact (Finset.disjoint_left.mp h (mem_labelSupport.mpr hS)) (mem_labelSupport.mpr hcon)
    rw [hT]
    exact optPhase_none_right (S s)

theorem optPhaseProd_sub_eq_zero_of_disjoint {S T : σ → Option (Fin 3)}
    (h : Disjoint (labelSupport S) (labelSupport T)) :
    optPhaseProd S T - optPhaseProd T S = 0 := by
  rw [optPhaseProd_eq_one_of_disjoint h, optPhaseProd_eq_one_of_disjoint h.symm, sub_self]

/-- **A three-site product forces two overlapping two-site factors.** -/
theorem card_inter_eq_one_of_card_three {S T R : σ → Option (Fin 3)}
    (hS : (labelSupport S).card ≤ 2) (hT : (labelSupport T).card ≤ 2)
    (hR : (labelSupport R).card = 3) (hmul : R = optMulLabel S T)
    (hdisj : ¬ Disjoint (labelSupport S) (labelSupport T)) :
    (labelSupport S).card = 2 ∧ (labelSupport T).card = 2 ∧
      (labelSupport S ∩ labelSupport T).card = 1 ∧
      labelSupport S ∪ labelSupport T = labelSupport R := by
  classical
  have hsub : labelSupport R ⊆ labelSupport S ∪ labelSupport T := by
    rw [hmul]
    exact labelSupport_optMulLabel_subset S T
  have hunion : 3 ≤ (labelSupport S ∪ labelSupport T).card := by
    rw [← hR]
    exact Finset.card_le_card hsub
  have hcards : (labelSupport S ∪ labelSupport T).card +
      (labelSupport S ∩ labelSupport T).card =
      (labelSupport S).card + (labelSupport T).card := Finset.card_union_add_card_inter _ _
  have hinterpos : 1 ≤ (labelSupport S ∩ labelSupport T).card := by
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    exact hdisj (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero))
  have hS2 : (labelSupport S).card = 2 := by omega
  have hT2 : (labelSupport T).card = 2 := by omega
  have hint1 : (labelSupport S ∩ labelSupport T).card = 1 := by omega
  refine ⟨hS2, hT2, hint1, ?_⟩
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  omega

end GaloisForLFunctions.HTGeometry
