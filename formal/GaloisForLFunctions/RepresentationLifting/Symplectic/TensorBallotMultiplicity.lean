import GaloisForLFunctions.RepresentationLifting.Symplectic.SL2TensorCharacters
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exact tensor multiplicities as ballot numbers

The existing branching list is a nonnegative walk on highest weights.
Pascal's identity solves its recurrence: weight k in tensor degree k+2r
occurs choose(k+2r,r)-choose(k+2r,r-1) times. At r=0 the second term
vanishes. This makes the individual multiplicities explicit, beyond
their aggregate dimension, Casimir moments, and multiplicity energy.
-/

namespace GaloisForLFunctions.RepresentationLifting.Symplectic

private theorem count_spinBranch_succ (j k : ℕ) :
    (spinBranch j).count (k + 1) =
      (if j = k then 1 else 0) + (if j = k + 2 then 1 else 0) := by
  cases j with
  | zero => cases k <;> simp [spinBranch]
  | succ j =>
    simp only [spinBranch, List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega

private theorem count_flatMap_spin_zero (l : List ℕ) :
    (l.flatMap spinBranch).count 0 = l.count 1 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.flatMap_cons, List.count_append, ih]
    cases j with
    | zero => simp [spinBranch]
    | succ j =>
      cases j with
      | zero => simp [spinBranch, Nat.add_comm]
      | succ j => simp [spinBranch]

private theorem count_flatMap_spin_succ (l : List ℕ) (k : ℕ) :
    (l.flatMap spinBranch).count (k + 1) = l.count k + l.count (k + 2) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.flatMap_cons, List.count_append, count_spinBranch_succ, ih]
    simp only [List.count_cons, beq_iff_eq]
    omega

theorem tensorSpin_count_zero_succ (n : ℕ) :
    (tensorSpinWeights (n + 1)).count 0 = (tensorSpinWeights n).count 1 :=
  count_flatMap_spin_zero _

theorem tensorSpin_count_succ_succ (n k : ℕ) :
    (tensorSpinWeights (n + 1)).count (k + 1) =
      (tensorSpinWeights n).count k + (tensorSpinWeights n).count (k + 2) :=
  count_flatMap_spin_succ _ _

/-- Weights beyond the tensor degree never occur. -/
theorem tensorSpin_count_above {n k : ℕ} (hnk : n < k) :
    (tensorSpinWeights n).count k = 0 := by
  apply List.count_eq_zero.mpr
  intro hk
  exact (Nat.not_le_of_gt hnk) (tensorSpinWeights_le n k hk)

/-- The top highest weight occurs once in every tensor power. -/
theorem tensorSpin_count_top (n : ℕ) : (tensorSpinWeights n).count n = 1 := by
  induction n with
  | zero => simp [tensorSpinWeights]
  | succ n ih =>
    rw [tensorSpin_count_succ_succ, ih, tensorSpin_count_above (by omega), add_zero]

/-- Every constituent has the same parity as the tensor degree. -/
theorem tensorSpinWeights_parity (n : ℕ) :
    ∀ k ∈ tensorSpinWeights n, k % 2 = n % 2 := by
  induction n with
  | zero => simp [tensorSpinWeights]
  | succ n ih =>
    intro k hk
    obtain ⟨j, hj, hk⟩ := List.mem_flatMap.mp hk
    have hp := ih j hj
    cases j <;> simp [spinBranch] at hk <;> omega

/-- The opposite parity sector is absent. -/
theorem tensorSpin_count_wrong_parity {n k : ℕ} (h : k % 2 ≠ n % 2) :
    (tensorSpinWeights n).count k = 0 :=
  List.count_eq_zero.mpr (fun hk => h (tensorSpinWeights_parity n k hk))

/-- An additive ballot identity avoids truncated subtraction at the boundary. -/
theorem tensorSpin_count_ballot (k r : ℕ) :
    (tensorSpinWeights (k + 2 * r)).count k + (k + 2 * r + 1).choose r =
      2 * (k + 2 * r).choose r := by
  have hmain : ∀ n k r, n = k + 2 * r →
      (tensorSpinWeights n).count k + (n + 1).choose r = 2 * n.choose r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k r hn
      cases r with
      | zero =>
        subst n
        simp [tensorSpin_count_top]
      | succ r =>
        cases k with
        | zero =>
          let m := 1 + 2 * r
          have hm : m < n := by dsimp [m]; omega
          have hi := ih m hm 1 r rfl
          have hn' : n = m + 1 := by dsimp [m]; omega
          rw [hn', tensorSpin_count_zero_succ]
          have hs : m.choose (r + 1) = m.choose r := by
            have ht := Nat.choose_symm (show r ≤ m by dsimp [m]; omega)
            have he : m - r = r + 1 := by dsimp [m]; omega
            rw [he] at ht
            exact ht
          have hp := Nat.choose_succ_succ m r
          have hp' := Nat.choose_succ_succ (m + 1) r
          simp only [Nat.succ_eq_add_one] at hp hp'
          omega
        | succ k =>
          let m := k + 2 * (r + 1)
          have hm : m < n := by dsimp [m]; omega
          have hi := ih m hm k (r + 1) rfl
          have hi' := ih m hm (k + 2) r (by dsimp [m]; omega)
          have hn' : n = m + 1 := by dsimp [m]; omega
          rw [hn', tensorSpin_count_succ_succ]
          have hp := Nat.choose_succ_succ m r
          have hp' := Nat.choose_succ_succ (m + 1) r
          simp only [Nat.succ_eq_add_one] at hp hp'
          omega
  exact hmain _ _ _ rfl

/-- Exact multiplicity of every admissible highest weight in a tensor power. -/
theorem tensorSpin_count_binomial (k r : ℕ) :
    (tensorSpinWeights (k + 2 * r)).count k =
      (k + 2 * r).choose r - if r = 0 then 0 else (k + 2 * r).choose (r - 1) := by
  cases r with
  | zero => simp [tensorSpin_count_top]
  | succ r =>
    have hb := tensorSpin_count_ballot k (r + 1)
    have hp := Nat.choose_succ_succ (k + 2 * (r + 1)) r
    have hr : r + 1 ≠ 0 := by omega
    simp only [Nat.succ_eq_add_one] at hp ⊢
    simp only [hr, ↓reduceIte, Nat.add_sub_cancel]
    omega

end GaloisForLFunctions.RepresentationLifting.Symplectic

#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorSpin_count_ballot
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorSpin_count_binomial

