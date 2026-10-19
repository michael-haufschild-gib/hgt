import GaloisForLFunctions.RHTower.PrimeBarycentricCoefficientDivergence

/-!
# Finite reciprocal-prime capacity and disjoint parity banks

The parity ratio of a finite prime bank is bounded by the reciprocal of one
plus twice its reciprocal-prime mass. The proof reuses the existing corpus
product lower bound. Unbounded finite reciprocal subsums produce arbitrarily
many disjoint nonempty banks with a prescribed small parity ratio.

These classical finite-product and selection tools support the positive
counterexample construction for native dyadic-antichain Fermi observability.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- Ratio of the parity and constant eigenmasses of a finite prime cube. -/
def fermiPrimeBankParityRatio (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, ((p : ℝ) - 1) / ((p : ℝ) + 1)

/-- Every local prime factor, hence the finite bank ratio, is positive. -/
theorem fermiPrimeBankParityRatio_pos (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) : 0 < fermiPrimeBankParityRatio P := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
  exact div_pos (by linarith) (by linarith)

/-- Reciprocal-prime mass controls the bank parity ratio quantitatively. -/
theorem fermiPrimeBankParityRatio_capacity_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    fermiPrimeBankParityRatio P ≤ 1 / (1 + 2 * ∑ p ∈ P, 1 / (p : ℝ)) := by
  let B : ℝ := ∏ p ∈ P, ((p : ℝ) + 1) / ((p : ℝ) - 1)
  have hlocal (p : ℕ) (hp : p ∈ P) :
      1 + 2 * (1 / (p : ℝ)) ≤ ((p : ℝ) + 1) / ((p : ℝ) - 1) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    apply (le_div_iff₀ (by linarith : 0 < (p : ℝ) - 1)).2
    have hr := one_div_mul_cancel hp0
    have hn : 0 ≤ 1 / (p : ℝ) := by positivity
    nlinarith
  have hsum : 1 + 2 * ∑ p ∈ P, 1 / (p : ℝ) ≤ B := by
    calc
      _ = 1 + ∑ p ∈ P, 2 * (1 / (p : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ ∏ p ∈ P, (1 + 2 * (1 / (p : ℝ))) :=
        RHTower.one_add_sum_le_prod_one_add P _ (fun p _ => by positivity)
      _ ≤ B := Finset.prod_le_prod (fun p _ => by positivity) hlocal
  have hmass : 0 < 1 + 2 * ∑ p ∈ P, 1 / (p : ℝ) := by positivity
  have hB : 0 < B := lt_of_lt_of_le hmass hsum
  have hidentity : fermiPrimeBankParityRatio P * B = 1 := by
    rw [fermiPrimeBankParityRatio, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hm : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp' : (p : ℝ) + 1 ≠ 0 := by linarith
    field_simp
  have heq : fermiPrimeBankParityRatio P = 1 / B :=
    (eq_div_iff (ne_of_gt hB)).2 hidentity
  rw [heq]
  exact one_div_le_one_div_of_le hmass hsum

/-- Mass at least twice a positive length makes the bank ratio smaller than its target. -/
theorem fermiPrimeBankParityRatio_small (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {L : ℝ} (hL : 0 < L)
    (hcap : 2 * L ≤ ∑ p ∈ P, 1 / (p : ℝ)) :
    0 < fermiPrimeBankParityRatio P ∧ fermiPrimeBankParityRatio P < 1 / (4 * L) := by
  refine ⟨fermiPrimeBankParityRatio_pos P hP, ?_⟩
  apply lt_of_le_of_lt (fermiPrimeBankParityRatio_capacity_bound P hP)
  exact (one_div_lt_one_div_of_lt (by positivity) (by linarith))

private theorem exists_prime_bank_outside (allowed : Set ℕ)
    (hdiv : ∀ M : ℝ, ∃ P : Finset ℕ,
      (∀ p ∈ P, p ∈ allowed) ∧ M < ∑ p ∈ P, 1 / (p : ℝ))
    (U : Finset ℕ) (M : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p ∈ allowed) ∧ Disjoint U P ∧
      M < ∑ p ∈ P, 1 / (p : ℝ) := by
  obtain ⟨P, hP, hmass⟩ := hdiv (M + ∑ p ∈ U, 1 / (p : ℝ))
  refine ⟨P \ U, fun p hp => hP p (Finset.mem_sdiff.mp hp).1,
    Finset.disjoint_sdiff, ?_⟩
  have hsplit := Finset.sum_inter_add_sum_sdiff P U (fun p => 1 / (p : ℝ))
  have hsmall : (∑ p ∈ P ∩ U, 1 / (p : ℝ)) ≤ ∑ p ∈ U, 1 / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun p _ _ => by positivity)
  linarith

/-- Removing finitely many used coordinates preserves unbounded finite capacity. -/
theorem exists_fermiDisjointCapacityBanks (allowed : Set ℕ)
    (hdiv : ∀ M : ℝ, ∃ P : Finset ℕ,
      (∀ p ∈ P, p ∈ allowed) ∧ M < ∑ p ∈ P, 1 / (p : ℝ))
    (L : ℕ) (M : ℝ) :
    ∃ T : Fin L → Finset ℕ,
      (∀ i, (∀ p ∈ T i, p ∈ allowed) ∧ M < ∑ p ∈ T i, 1 / (p : ℝ)) ∧
      Pairwise (fun i j => Disjoint (T i) (T j)) := by
  classical
  induction L with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  | succ L ih =>
    obtain ⟨T, hT, hdis⟩ := ih
    let U := Finset.univ.biUnion T
    obtain ⟨Q, hQ, hQU, hmass⟩ := exists_prime_bank_outside allowed hdiv U M
    have hsub (i : Fin L) : T i ⊆ U :=
      Finset.subset_biUnion_of_mem T (Finset.mem_univ i)
    refine ⟨Fin.cons Q T, ?_, ?_⟩
    · intro i
      exact Fin.cases ⟨hQ, hmass⟩ (fun j => hT j) i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro h
          exact (h rfl).elim
        · intro _
          simpa using hQU.symm.mono_right (hsub j)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          simpa using hQU.mono_left (hsub i)
        · intro hij
          simpa using hdis (fun h => hij (congrArg Fin.succ h))

/-- Disjoint nonempty prime banks with uniformly small positive parity ratios. -/
theorem exists_fermiSmallParityRatioBanks (allowed : Set ℕ)
    (hprime : ∀ p ∈ allowed, p.Prime)
    (hdiv : ∀ M : ℝ, ∃ P : Finset ℕ,
      (∀ p ∈ P, p ∈ allowed) ∧ M < ∑ p ∈ P, 1 / (p : ℝ))
    {L : ℕ} (hL : 0 < L) :
    ∃ T : Fin L → Finset ℕ,
      Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      ∀ i, (T i).Nonempty ∧ (∀ p ∈ T i, p ∈ allowed) ∧
        0 < fermiPrimeBankParityRatio (T i) ∧
        fermiPrimeBankParityRatio (T i) < 1 / (4 * (L : ℝ)) := by
  obtain ⟨T, hT, hd⟩ := exists_fermiDisjointCapacityBanks allowed hdiv L (2 * (L : ℝ))
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨T, hd, fun i => ?_⟩
  obtain ⟨hTi, hm⟩ := hT i
  have hne : (T i).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, Finset.sum_empty] at hm
    linarith
  exact ⟨hne, hTi, fermiPrimeBankParityRatio_small (T i)
    (fun p hp => hprime p (hTi p hp)) hLr hm.le⟩

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
