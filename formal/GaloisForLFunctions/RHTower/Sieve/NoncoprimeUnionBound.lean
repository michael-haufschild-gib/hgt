import GaloisForLFunctions.RHTower.Sieve.SharedSectorLimit

/-!
# The union bound over shared primes

A balanced pair that is not coprime shares a prime, and that prime divides `n₁ ≤ 2√x`, so it lies in
`primesLE ⌊2√x⌋`.  Hence the noncoprime pair count is at most the sum of the shared-prime sector
counts over that range:

    B(x,h) ≤ ∑_{p ≤ 2√x} C_p(x,h).

This is the union bound of the card's step 3, and it is exact arithmetic — no analytic input.
-/

namespace RHTower.Sieve

open Finset

/-- A union costs at most the sum, for a nonnegative weight. -/
theorem sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {A B : Finset α} {f : α → ℝ}
    (hf : ∀ q, 0 ≤ f q) :
    ∑ q ∈ A ∪ B, f q ≤ ∑ q ∈ A, f q + ∑ q ∈ B, f q := by
  have hkey := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have hpos : 0 ≤ ∑ q ∈ A ∩ B, f q := Finset.sum_nonneg fun q _ => hf q
  linarith

/-- A biUnion costs at most the sum of the pieces, for a nonnegative weight. -/
theorem sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq α] {s : Finset ι}
    {t : ι → Finset α} {f : α → ℝ} (hf : ∀ q, 0 ≤ f q) :
    ∑ q ∈ s.biUnion t, f q ≤ ∑ i ∈ s, ∑ q ∈ t i, f q := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact le_trans (sum_union_le_of_nonneg hf) (by linarith [ih])

/-- The noncoprime balanced pair count. -/
noncomputable def noncoprimePairCount (x h : ℝ) : ℝ :=
  ∑ q ∈ (balancedPairs x h).filter (fun q => ¬ Nat.Coprime q.1 q.2),
    ((ArithmeticFunction.moebius q.1 : ℤ) : ℝ) ^ 2
      * ((ArithmeticFunction.moebius q.2 : ℤ) : ℝ) ^ 2

/-- Every noncoprime balanced pair shares a prime below `2√x`. -/
theorem exists_shared_prime {x h : ℝ} (hx : 0 < x) {q : ℕ × ℕ}
    (hq : q ∈ balancedPairs x h) (hnc : ¬ Nat.Coprime q.1 q.2) :
    ∃ p ∈ Nat.primesLE ⌊2 * Real.sqrt x⌋₊, p ∣ q.1 ∧ p ∣ q.2 := by
  rw [mem_balancedPairs hx] at hq
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hprodpos : 0 < q.1 * q.2 := by
    by_contra hc
    have hz : q.1 * q.2 = 0 := by omega
    rw [hz] at h1
    simp at h1
    linarith
  have hq1 : 0 < q.1 := by
    rcases Nat.eq_zero_or_pos q.1 with hz | hz
    · rw [hz] at hprodpos; simp at hprodpos
    · exact hz
  have hg : Nat.gcd q.1 q.2 ≠ 1 := hnc
  have hg0 : Nat.gcd q.1 q.2 ≠ 0 := by
    intro hz
    have := Nat.eq_zero_of_gcd_eq_zero_left hz
    omega
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hpd1 : p ∣ q.1 := dvd_trans hpg (Nat.gcd_dvd_left _ _)
  have hpd2 : p ∣ q.2 := dvd_trans hpg (Nat.gcd_dvd_right _ _)
  refine ⟨p, ?_, hpd1, hpd2⟩
  rw [Nat.mem_primesLE]
  refine ⟨?_, hp⟩
  have hple : p ≤ q.1 := Nat.le_of_dvd hq1 hpd1
  have hcast : ((q.1 : ℕ) : ℝ) ≤ 2 * Real.sqrt x := h4
  have hfl : q.1 ≤ ⌊2 * Real.sqrt x⌋₊ := Nat.le_floor hcast
  omega

/-- **The union bound.**  Card equation `(10)`, as a count. -/
theorem noncoprimePairCount_le {x h : ℝ} (hx : 0 < x) :
    noncoprimePairCount x h
      ≤ ∑ p ∈ Nat.primesLE ⌊2 * Real.sqrt x⌋₊, sharedSectorCount x h p := by
  classical
  set w : ℕ × ℕ → ℝ := fun q => ((ArithmeticFunction.moebius q.1 : ℤ) : ℝ) ^ 2
    * ((ArithmeticFunction.moebius q.2 : ℤ) : ℝ) ^ 2 with hw
  have hw0 : ∀ q, 0 ≤ w q := by
    intro q
    rw [hw]
    positivity
  have hsub : (balancedPairs x h).filter (fun q => ¬ Nat.Coprime q.1 q.2)
      ⊆ (Nat.primesLE ⌊2 * Real.sqrt x⌋₊).biUnion
        (fun p => (balancedPairs x h).filter (fun q => p ∣ q.1 ∧ p ∣ q.2)) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hmem, hnc⟩ := hq
    obtain ⟨p, hp, hpd1, hpd2⟩ := exists_shared_prime hx hmem hnc
    rw [Finset.mem_biUnion]
    exact ⟨p, hp, Finset.mem_filter.2 ⟨hmem, hpd1, hpd2⟩⟩
  calc noncoprimePairCount x h
      ≤ ∑ q ∈ (Nat.primesLE ⌊2 * Real.sqrt x⌋₊).biUnion
          (fun p => (balancedPairs x h).filter (fun q => p ∣ q.1 ∧ p ∣ q.2)), w q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw0 q)
    _ ≤ ∑ p ∈ Nat.primesLE ⌊2 * Real.sqrt x⌋₊, sharedSectorCount x h p :=
        sum_biUnion_le_of_nonneg hw0

end RHTower.Sieve
