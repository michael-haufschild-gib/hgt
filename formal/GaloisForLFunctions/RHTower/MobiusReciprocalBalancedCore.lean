import GaloisForLFunctions.RHTower.MobiusReciprocalUnbalancedTail

/-!
# Exact power-balanced decomposition of the coupled reciprocal source

The literal finite Möbius quadratic form splits into two absolutely controlled
power-unbalanced sectors, one balanced sector, and their singleton overlap.
-/

open Finset
namespace RHTower
noncomputable section

private theorem sum_two_predicate_partition {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℝ) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (∑ x ∈ S, f x) =
      (∑ x ∈ S.filter P, f x) +
      (∑ x ∈ S.filter Q, f x) +
      (∑ x ∈ S.filter (fun x => ¬ P x ∧ ¬ Q x), f x) -
      (∑ x ∈ S.filter (fun x => P x ∧ Q x), f x) := by
  classical
  calc
    (∑ x ∈ S, f x) =
        ∑ x ∈ S,
          ((if P x then f x else 0) + (if Q x then f x else 0) +
            (if ¬ P x ∧ ¬ Q x then f x else 0) -
            (if P x ∧ Q x then f x else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_filter]

/-- Signed atom of the coupled-order finite reciprocal form. -/
def coupledReciprocalSignedAtom (δ : ℝ) (m n : ℕ) : ℝ :=
  mobiusRealCoefficient m * mobiusRealCoefficient n *
    (((m : ℝ) ^ 2 * (n : ℝ) ^ 2) /
      (((m : ℝ) + (n : ℝ)) ^ (5 + δ)))

private theorem coupledReciprocalSignedAtom_symm (δ : ℝ) (m n : ℕ) :
    coupledReciprocalSignedAtom δ m n = coupledReciprocalSignedAtom δ n m := by
  unfold coupledReciprocalSignedAtom
  rw [show (m : ℝ) + n = (n : ℝ) + m by ring]
  ring

/-- Full literal signed quadratic form, before its Gamma normalization. -/
def coupledReciprocalFullEnergy (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ nm ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
    coupledReciprocalSignedAtom δ nm.2 nm.1

/-- The unresolved power-balanced signed part. -/
def coupledReciprocalBalancedEnergy (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ nm ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun nm => ¬ nm.2 ^ 3 ≤ nm.1 ^ 2 ∧ ¬ nm.1 ^ 3 ≤ nm.2 ^ 2),
    coupledReciprocalSignedAtom δ nm.2 nm.1

/-- The transposed power-unbalanced signed sector. -/
def coupledReciprocalOppositeUnbalancedEnergy (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ nm ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun nm => nm.1 ^ 3 ≤ nm.2 ^ 2),
    coupledReciprocalSignedAtom δ nm.2 nm.1

/-- The overlap of the two power-unbalanced sectors. -/
def coupledReciprocalOverlapEnergy (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ nm ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun nm => nm.2 ^ 3 ≤ nm.1 ^ 2 ∧ nm.1 ^ 3 ≤ nm.2 ^ 2),
    coupledReciprocalSignedAtom δ nm.2 nm.1

/-- Exact finite inclusion--exclusion; no estimate is used. -/
theorem coupledReciprocalFullEnergy_eq_partition (δ : ℝ) (N : ℕ) :
    coupledReciprocalFullEnergy δ N =
      unbalancedReciprocalSignedEnergy δ N +
        coupledReciprocalOppositeUnbalancedEnergy δ N +
          coupledReciprocalBalancedEnergy δ N -
            coupledReciprocalOverlapEnergy δ N := by
  let S := Finset.Icc 1 N
  let F : ℕ × ℕ → ℝ := fun nm => coupledReciprocalSignedAtom δ nm.2 nm.1
  have hU : unbalancedReciprocalSignedEnergy δ N =
      ∑ nm ∈ (S.product S).filter (fun nm => nm.2 ^ 3 ≤ nm.1 ^ 2), F nm := by
    unfold unbalancedReciprocalSignedEnergy
    simp only [Finset.sum_filter]
    exact (Finset.sum_product S S (fun nm : ℕ × ℕ =>
      if nm.2 ^ 3 ≤ nm.1 ^ 2 then F nm else 0)).symm
  rw [hU]
  unfold coupledReciprocalFullEnergy coupledReciprocalOppositeUnbalancedEnergy
    coupledReciprocalBalancedEnergy coupledReciprocalOverlapEnergy
  change (∑ nm ∈ S.product S, F nm) =
    (∑ nm ∈ (S.product S).filter (fun nm => nm.2 ^ 3 ≤ nm.1 ^ 2), F nm) +
    (∑ nm ∈ (S.product S).filter (fun nm => nm.1 ^ 3 ≤ nm.2 ^ 2), F nm) +
    (∑ nm ∈ (S.product S).filter
      (fun nm => ¬ nm.2 ^ 3 ≤ nm.1 ^ 2 ∧ ¬ nm.1 ^ 3 ≤ nm.2 ^ 2), F nm) -
    (∑ nm ∈ (S.product S).filter
      (fun nm => nm.2 ^ 3 ≤ nm.1 ^ 2 ∧ nm.1 ^ 3 ≤ nm.2 ^ 2), F nm)
  exact sum_two_predicate_partition (S.product S) F
      (fun nm => nm.2 ^ 3 ≤ nm.1 ^ 2)
      (fun nm => nm.1 ^ 3 ≤ nm.2 ^ 2)

/-- Swapping the two indices identifies the two unbalanced contributions. -/
theorem coupledReciprocalOppositeUnbalancedEnergy_eq_unbalanced
    (δ : ℝ) (N : ℕ) :
    coupledReciprocalOppositeUnbalancedEnergy δ N =
      unbalancedReciprocalSignedEnergy δ N := by
  let S := Finset.Icc 1 N
  unfold coupledReciprocalOppositeUnbalancedEnergy unbalancedReciprocalSignedEnergy
  simp only [Finset.sum_filter]
  change (∑ nm ∈ S.product S,
      if nm.1 ^ 3 ≤ nm.2 ^ 2 then coupledReciprocalSignedAtom δ nm.2 nm.1 else 0) =
    ∑ n ∈ S, ∑ m ∈ S,
      if m ^ 3 ≤ n ^ 2 then coupledReciprocalSignedAtom δ m n else 0
  calc
    _ = ∑ n ∈ S, ∑ m ∈ S,
          if n ^ 3 ≤ m ^ 2 then coupledReciprocalSignedAtom δ m n else 0 :=
      Finset.sum_product S S (fun nm : ℕ × ℕ =>
        if nm.1 ^ 3 ≤ nm.2 ^ 2 then coupledReciprocalSignedAtom δ nm.2 nm.1 else 0)
    _ = ∑ n ∈ S, ∑ m ∈ S,
          if m ^ 3 ≤ n ^ 2 then coupledReciprocalSignedAtom δ n m else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      split_ifs with h
      · exact coupledReciprocalSignedAtom_symm δ n m
      · rfl

/-- The overlap set is literally the unit pair when the cutoff contains one. -/
theorem coupledReciprocalOverlapEnergy_eq_unit_atom
    (δ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    coupledReciprocalOverlapEnergy δ N =
      coupledReciprocalSignedAtom δ 1 1 := by
  let S := Finset.Icc 1 N
  have hset :
      ((S.product S).filter
        (fun nm => nm.2 ^ 3 ≤ nm.1 ^ 2 ∧ nm.1 ^ 3 ≤ nm.2 ^ 2)) =
        {(1, 1)} := by
    ext nm
    rcases nm with ⟨n, m⟩
    constructor
    · intro h
      obtain ⟨hpair, hboth⟩ := Finset.mem_filter.mp h
      obtain ⟨hnS, hmS⟩ := Finset.mem_product.mp hpair
      have hn : 0 < n := (Finset.mem_Icc.mp hnS).1
      have hm : 0 < m := (Finset.mem_Icc.mp hmS).1
      obtain ⟨hm1, hn1⟩ := cubic_unbalanced_overlap_only_one hm hn hboth.1 hboth.2
      simp [hm1, hn1]
    · intro h
      have hn1 : n = 1 := by simpa using congrArg Prod.fst (Finset.mem_singleton.mp h)
      have hm1 : m = 1 := by simpa using congrArg Prod.snd (Finset.mem_singleton.mp h)
      subst n
      subst m
      simp [S, hN]
  unfold coupledReciprocalOverlapEnergy
  rw [hset]
  simp

private theorem coupledReciprocalSignedAtom_one_one (δ : ℝ) :
    coupledReciprocalSignedAtom δ 1 1 = (2 : ℝ) ^ (-(5 + δ)) := by
  unfold coupledReciprocalSignedAtom mobiusRealCoefficient
  norm_num
  rw [show -δ + -5 = -(5 + δ) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Exact balanced-only form of the finite signed source for every cutoff containing one. -/
theorem coupledReciprocalFullEnergy_eq_balanced_add_two_unbalanced
    (δ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    coupledReciprocalFullEnergy δ N =
      coupledReciprocalBalancedEnergy δ N +
        2 * unbalancedReciprocalSignedEnergy δ N -
          (2 : ℝ) ^ (-(5 + δ)) := by
  rw [coupledReciprocalFullEnergy_eq_partition,
    coupledReciprocalOppositeUnbalancedEnergy_eq_unbalanced,
    coupledReciprocalOverlapEnergy_eq_unit_atom δ N hN,
    coupledReciprocalSignedAtom_one_one]
  ring

end
end RHTower
