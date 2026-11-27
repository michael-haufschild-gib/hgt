import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Spectrum

/-! # Reflection at uniform capacity, including the bosonic and squarefree sectors -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount

open Finset

private theorem uniform_capacity (S : Finset Nat.Primes) (k : ℕ) :
    capacity (fun _ : S => k) = S.card*k := by simp [capacity]

private theorem uniform_pair_sum (S : Finset Nat.Primes) (k m : ℕ) :
    (∑ i : S, pairCount (fun _ : S => k) m i) =
      S.card * (m - (S.card*k-k) + min m k) := by
  simp [pairCount, lower, upper, uniform_capacity]

/-- In the interior, three or more modes rule out both partially filled endpoint regimes. -/
private theorem interior_uniform {r k m : ℕ} (hr : 2 < r) (hm : 0 < m) (ht : m < r*k) :
    r*(m-(r*k-k)+min m k) = 2*m ↔ 2*m = r*k := by
  have h₂ : 2*k ≤ r*k := Nat.mul_le_mul_right k hr.le
  constructor
  · intro h
    by_cases hlo : m < k
    · rw [show m-(r*k-k)+min m k = m by omega] at h
      exact (hr.ne' (Nat.eq_of_mul_eq_mul_right hm h)).elim
    by_cases hhi : r*k-m < k
    · rw [show m-(r*k-k)+min m k = 2*k-(r*k-m) by omega, Nat.mul_sub,
        show r*(2*k) = 2*(r*k) by ring] at h
      have hh : r*(r*k-m) = 2*(r*k-m) := by omega
      exact (hr.ne' (Nat.eq_of_mul_eq_mul_right (by omega) hh)).elim
    rw [show m-(r*k-k)+min m k = k by omega] at h
    exact h.symm
  · intro h
    rw [show m-(r*k-k)+min m k = k by omega, h]

private theorem uniform_arithmetic (r k m : ℕ) (hm : m ≤ r*k) :
    r*(m-(r*k-k)+min m k) = 2*m ↔ r ≤ 2 ∨ m = 0 ∨ m = r*k ∨ 2*m = r*k := by
  by_cases hr : r ≤ 2
  · refine iff_of_true ?_ (Or.inl hr)
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
    · simp only [Nat.zero_mul] at hm ⊢; omega
    · simp only [Nat.one_mul] at hm ⊢; omega
    · omega
  have h₂ := Nat.mul_le_mul_right k (show 2 ≤ r by omega)
  by_cases h₀ : m = 0
  · subst m; simp
  by_cases hF : m = r*k
  · subst m
    refine iff_of_true ?_ (Or.inr (Or.inr (Or.inl rfl)))
    rw [show r*k-(r*k-k)+min (r*k) k = 2*k by omega]
    ring
  simpa only [hr, h₀, hF, false_or] using
    (interior_uniform (k := k) (by omega : 2 < r) (by omega : 0 < m) (by omega))

/-- With uniform cap, all sectors on at most two modes reflect. For three or more modes
the only possibilities are vacuum, full occupancy and half filling. -/
theorem uniform_reflection_iff (S : Finset Nat.Primes) (k m : ℕ) :
    Reflects S (fun _ => k) m ↔ m ≤ S.card*k ∧
      (S.card ≤ 2 ∨ m = 0 ∨ m = S.card*k ∨ 2*m = S.card*k) := by
  rw [reflection_iff, uniform_capacity, uniform_pair_sum]
  exact and_congr_right fun hm => uniform_arithmetic _ _ _ hm

/-- At particle number m, cap m allows every unrestricted occupation vector of that degree. -/
theorem unrestricted_counts_iff (S : Finset Nat.Primes) (m : ℕ) (v : S → ℕ) :
    (∃ x : State (fun _ : S => m) m, count x = v) ↔ ∑ p, v p = m := by
  constructor
  · rintro ⟨x, rfl⟩; exact count_sum x
  · intro hv
    have bound (i : S) : v i ≤ m := hv ▸ single_le_sum (s := univ) (fun j _ => Nat.zero_le (v j)) (mem_univ i)
    exact ⟨⟨fun i => ⟨v i, Nat.lt_succ_of_le (bound i)⟩, hv⟩, rfl⟩

/-- A nonvacuum unrestricted sector reflects exactly on packets of one or two primes. -/
theorem unrestricted_reflection_iff (S : Finset Nat.Primes) (m : ℕ) :
    Reflects S (fun _ => m) m ↔ m = 0 ∨ (0 < S.card ∧ S.card ≤ 2) := by
  by_cases h₀ : m = 0
  · subst m; simp [uniform_reflection_iff]
  have hm : 0 < m := by omega
  have feas : m ≤ S.card*m ↔ 0 < S.card := by
    have h := Nat.mul_le_mul_right_iff (n := 1) (m := S.card) hm
    rw [Nat.one_mul] at h
    omega
  have full : m = S.card*m ↔ S.card = 1 := by
    constructor
    · intro h; exact Nat.eq_of_mul_eq_mul_right hm (h.symm.trans (Nat.one_mul m).symm)
    · intro h; rw [h, Nat.one_mul]
  have half : 2*m = S.card*m ↔ S.card = 2 := by
    constructor
    · intro h; exact Nat.eq_of_mul_eq_mul_right hm h.symm
    · intro h; rw [h]
  rw [uniform_reflection_iff, feas, full, half]
  omega

/-- All squarefree particle sectors, including the empty packet, vacuum and full occupancy. -/
theorem squarefree_reflection_iff (S : Finset Nat.Primes) (m : ℕ) :
    Reflects S (fun _ => 1) m ↔
      m ≤ S.card ∧ (m = 0 ∨ m = S.card ∨ 2*m = S.card) := by
  rw [uniform_reflection_iff, Nat.mul_one]
  omega

#print axioms uniform_reflection_iff
#print axioms unrestricted_counts_iff
#print axioms unrestricted_reflection_iff
#print axioms squarefree_reflection_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount
