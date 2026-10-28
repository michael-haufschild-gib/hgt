import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheValuationTowerIsExactlySolvable

/-!
# Weighted Mangoldt sums on one valuation ladder

The nonzero Mangoldt atoms divisible by a prime are exactly its positive powers.
The same injection reindexes the infinite upward row and finite divisor row.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction

/-- A summable prime-power row is the corresponding Mangoldt row on all integers. -/
theorem hasSum_primePower_mangoldt {p : ℕ} (hp : p.Prime) (F : ℕ → ℝ) {L : ℝ}
    (h : HasSum (fun j : ℕ => F (p ^ (j + 1)) * Real.log p / (p : ℝ) ^ (j + 1)) L) :
    HasSum (fun t : ℕ => if p ∣ t then F t * Λ t / (t : ℝ) else 0) L := by
  have hinj : Function.Injective (fun j : ℕ => p ^ (j + 1)) := by
    intro a b hab
    have he := Nat.pow_right_injective hp.two_le hab
    omega
  have hz : ∀ t, t ∉ Set.range (fun j : ℕ => p ^ (j + 1)) →
      (if p ∣ t then F t * Λ t / (t : ℝ) else 0) = 0 := by
    intro t ht
    by_cases hpt : p ∣ t
    · rw [if_pos hpt]
      by_cases hΛ : Λ t = 0
      · rw [hΛ, mul_zero, zero_div]
      · obtain ⟨k, hk, rfl⟩ := eq_pow_of_dvd_of_vonMangoldt_ne_zero hp hpt hΛ
        exact False.elim (ht ⟨k - 1, by
          change p ^ (k - 1 + 1) = p ^ k
          rw [Nat.sub_add_cancel hk]⟩)
    · rw [if_neg hpt]
  apply (hinj.hasSum_iff hz).mp
  refine h.congr_fun fun j => ?_
  simp only [Function.comp_apply, if_pos (dvd_pow_self p (Nat.succ_ne_zero j)),
    vonMangoldt_prime_pow hp (Nat.succ_pos j), Nat.cast_pow]

/-- Reindex every weighted prime-supported divisor atom by its positive valuation. -/
theorem sum_divisors_primePower_mangoldt {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (F : ℕ → ℝ) :
    (∑ t ∈ n.divisors, if p ∣ t then F t * Λ t else 0) =
      ∑ j ∈ range (n.factorization p), F (p ^ (j + 1)) * Real.log p := by
  let s := (range (n.factorization p)).image (fun j => p ^ (j + 1))
  have hsub : s ⊆ n.divisors := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ht
    rw [Nat.mem_divisors]
    exact ⟨(hp.pow_dvd_iff_le_factorization hn).mpr (by have := mem_range.mp hj; omega), hn⟩
  have hz : ∀ t ∈ n.divisors, t ∉ s → (if p ∣ t then F t * Λ t else 0) = 0 := by
    intro t ht hts
    by_cases hpt : p ∣ t
    · rw [if_pos hpt]
      by_cases hΛ : Λ t = 0
      · rw [hΛ, mul_zero]
      · obtain ⟨k, hk, rfl⟩ := eq_pow_of_dvd_of_vonMangoldt_ne_zero hp hpt hΛ
        have hkv : k ≤ n.factorization p :=
          (hp.pow_dvd_iff_le_factorization hn).mp (Nat.dvd_of_mem_divisors ht)
        exact False.elim (hts (mem_image.mpr ⟨k - 1, mem_range.mpr (by omega),
          by rw [Nat.sub_add_cancel hk]⟩))
    · rw [if_neg hpt]
  rw [← sum_subset hsub hz]
  dsimp only [s]
  rw [sum_image (fun a _ b _ hab => by
    have h := Nat.pow_right_injective hp.two_le hab
    omega)]
  exact sum_congr rfl fun j _ => by
    rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero j)),
      vonMangoldt_prime_pow hp (Nat.succ_pos j)]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
