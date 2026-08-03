import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTail

/-!
# The shared-prime tail of a balanced pair count

A pair `(n₁, n₂)` sharing a prime `p` has `p ∣ n₁` and `p ∣ n₂`, so it is counted by the product of
two interval multiple counts, each at most `length/p + 1`.  Expanding the product and summing over
the primes of a window `(P, Q]` gives four pieces, all already owned:

`∑_{P < p ≤ Q} (ℓ₁/p + 1)(ℓ₂/p + 1) ≤ ℓ₁ℓ₂/P + (ℓ₁ + ℓ₂)·∑_{p ≤ Q} 1/p + #(P, Q]`,

with the inverse-square piece bounded by the telescoping tail of `InverseSquareTail.lean` and the
reciprocal piece by Mertens' second theorem.  Choosing `P` large makes the first term small and the
remaining terms are lower order against `ℓ₁ℓ₂`.

Everything here is uniform in the intervals; no distribution theorem enters.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **Pairs sharing a prime.**  Each entry is a multiple of `p` in its own interval. -/
theorem card_pair_dvd_le {p : ℕ} (hp : 0 < p) {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    ((#{n ∈ Finset.Ioc a b | p ∣ n} : ℕ) : ℝ) * ((#{n ∈ Finset.Ioc c d | p ∣ n} : ℕ) : ℝ)
      ≤ (((b : ℝ) - a) / p + 1) * (((d : ℝ) - c) / p + 1) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h1 := abs_card_filter_dvd_Ioc_sub_lt p a b hp hab
  have h2 := abs_card_filter_dvd_Ioc_sub_lt p c d hp hcd
  have hb1 : ((#{n ∈ Finset.Ioc a b | p ∣ n} : ℕ) : ℝ) ≤ ((b : ℝ) - a) / p + 1 := by
    have := (abs_lt.1 h1).2
    linarith
  have hb2 : ((#{n ∈ Finset.Ioc c d | p ∣ n} : ℕ) : ℝ) ≤ ((d : ℝ) - c) / p + 1 := by
    have := (abs_lt.1 h2).2
    linarith
  have hnn1 : (0 : ℝ) ≤ ((#{n ∈ Finset.Ioc a b | p ∣ n} : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnn2 : (0 : ℝ) ≤ ((#{n ∈ Finset.Ioc c d | p ∣ n} : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpos1 : (0 : ℝ) ≤ ((b : ℝ) - a) / p + 1 := le_trans hnn1 hb1
  exact mul_le_mul hb1 hb2 hnn2 hpos1

/-- The prime window sits inside its integer window. -/
theorem bigPrimeSet_subset_Icc (P Q : ℕ) : bigPrimeSet P Q ⊆ Finset.Icc (P + 1) Q :=
  Finset.filter_subset _ _

/-- The prime window sits inside the initial prime set. -/
theorem bigPrimeSet_subset_primesLE (P Q : ℕ) : bigPrimeSet P Q ⊆ Nat.primesLE Q := by
  intro p hp
  obtain ⟨hmem, hprime⟩ := Finset.mem_filter.1 hp
  exact Nat.mem_primesLE.2 ⟨(Finset.mem_Icc.1 hmem).2, hprime⟩

/-- The inverse-square weight of a prime window. -/
theorem sum_inv_sq_bigPrimeSet_le {P : ℕ} (hP : 1 ≤ P) (Q : ℕ) :
    ∑ p ∈ bigPrimeSet P Q, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (P : ℝ) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (bigPrimeSet_subset_Icc P Q) ?_) ?_
  · intro d _ _
    positivity
  · exact sum_Icc_inv_sq_le hP Q

/-- The reciprocal weight of a prime window is bounded by Mertens' sum. -/
theorem sum_inv_bigPrimeSet_le (P Q : ℕ) :
    ∑ p ∈ bigPrimeSet P Q, (1 : ℝ) / (p : ℝ) ≤ mertensS Q := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (bigPrimeSet_subset_primesLE P Q) ?_
  intro p _ _
  positivity

/-- The prime window has at most `Q` members. -/
theorem card_bigPrimeSet_le (P Q : ℕ) : ((bigPrimeSet P Q).card : ℝ) ≤ (Q : ℝ) := by
  have hnat : (bigPrimeSet P Q).card ≤ Q := by
    refine le_trans (Finset.card_le_card (bigPrimeSet_subset_Icc P Q)) ?_
    rw [Nat.card_Icc]
    omega
  exact_mod_cast hnat

/-- **Shared-prime tail bound.**  Summing the pair bound over the primes of a window separates into
an inverse-square piece, a Mertens piece, and a counting piece. -/
theorem sum_pair_tail_le {P : ℕ} (hP : 1 ≤ P) (Q : ℕ) {l₁ l₂ : ℝ} (h1 : 0 ≤ l₁) (h2 : 0 ≤ l₂) :
    ∑ p ∈ bigPrimeSet P Q, (l₁ / (p : ℝ) + 1) * (l₂ / (p : ℝ) + 1)
      ≤ l₁ * l₂ / (P : ℝ) + (l₁ + l₂) * mertensS Q + (Q : ℝ) := by
  classical
  have hexpand : ∀ p ∈ bigPrimeSet P Q,
      (l₁ / (p : ℝ) + 1) * (l₂ / (p : ℝ) + 1)
        = l₁ * l₂ * (1 / (p : ℝ) ^ 2) + l₁ * (1 / (p : ℝ)) + l₂ * (1 / (p : ℝ)) + 1 := by
    intro p hp
    have hprime : p.Prime := prime_of_mem_bigPrimeSet hp
    have hpne : ((p : ℝ)) ≠ 0 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
      intro hcon
      rw [hcon] at this
      linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    mul_one]
  have hsq := sum_inv_sq_bigPrimeSet_le hP Q
  have hrec := sum_inv_bigPrimeSet_le P Q
  have hcard := card_bigPrimeSet_le P Q
  have hprod : l₁ * l₂ * ∑ p ∈ bigPrimeSet P Q, (1 : ℝ) / (p : ℝ) ^ 2 ≤ l₁ * l₂ * (1 / (P : ℝ)) :=
    mul_le_mul_of_nonneg_left hsq (mul_nonneg h1 h2)
  have hr1 : l₁ * ∑ p ∈ bigPrimeSet P Q, (1 : ℝ) / (p : ℝ) ≤ l₁ * mertensS Q :=
    mul_le_mul_of_nonneg_left hrec h1
  have hr2 : l₂ * ∑ p ∈ bigPrimeSet P Q, (1 : ℝ) / (p : ℝ) ≤ l₂ * mertensS Q :=
    mul_le_mul_of_nonneg_left hrec h2
  have hfin : l₁ * l₂ * (1 / (P : ℝ)) = l₁ * l₂ / (P : ℝ) := by ring
  have hfin2 : l₁ * mertensS Q + l₂ * mertensS Q = (l₁ + l₂) * mertensS Q := by ring
  linarith

end RHTower.Sieve
