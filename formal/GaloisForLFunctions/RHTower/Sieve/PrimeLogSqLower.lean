import GaloisForLFunctions.RHTower.Sieve.PrimePowerWeightTail
import GaloisForLFunctions.RHTower.VonMangoldtLogHarmonicSummatory

/-!
# An explicit lower bound for `∑_{p ≤ N} (log p)²/p`

Splitting the `Λ·log/id` summatory at `N` into primes and proper prime powers, the prime part is
exactly `∑_{p ≤ N}(log p)²/p`, and the proper prime powers are carried by the map
`(p, j) ↦ p^{j+2}`, which is injective.  Their contribution is `O(log N)`, so

`∑_{p ≤ N}(log p)²/p ≥ ½log²N - 39 log N - 25`.

The main term comes from `RHTower.abs_sum_vonMangoldt_log_div_sub_le`; everything else here is the
bookkeeping that separates the primes from their powers.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The shifted prime-power parametrisation is injective. -/
theorem primePowShift_injOn {N M : ℕ} :
    ∀ x ∈ Nat.primesLE N ×ˢ Finset.range M, ∀ y ∈ Nat.primesLE N ×ˢ Finset.range M,
      x.1 ^ (x.2 + 2) = y.1 ^ (y.2 + 2) → x = y := by
  rintro ⟨p, j⟩ hx ⟨q, k⟩ hy hxy
  obtain ⟨hp, _⟩ := Finset.mem_product.1 hx
  obtain ⟨hq, _⟩ := Finset.mem_product.1 hy
  have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
  have hqp : q.Prime := Nat.prime_of_mem_primesLE hq
  have hpq : p = q := by
    have hdvd : p ∣ q ^ (k + 2) := by
      rw [← hxy]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hpp hqp).1 (hpp.dvd_of_dvd_pow hdvd)
  subst hpq
  have hjk : j + 2 = k + 2 := Nat.pow_right_injective hpp.two_le hxy
  have : j = k := by omega
  subst this
  rfl

/-- Every non-prime with a nonzero von Mangoldt weight is a shifted prime power. -/
theorem mem_image_of_nonprime {N : ℕ} {m : ℕ} (hmN : m ≤ N)
    (hnp : ¬ m.Prime) (hΛ : vonMangoldt m ≠ 0) :
    m ∈ (Nat.primesLE N ×ˢ Finset.range (Nat.log 2 N)).image (fun x => x.1 ^ (x.2 + 2)) := by
  classical
  obtain ⟨p, k, hp, hk, hpk⟩ := isPrimePow_nat_iff m |>.mp (vonMangoldt_ne_zero_iff.mp hΛ)
  have hk2 : 2 ≤ k := by
    by_contra hcon
    have hk1 : k = 1 := by omega
    rw [hk1, pow_one] at hpk
    exact hnp (hpk ▸ hp)
  have hple : p ≤ m := by
    rw [← hpk]
    exact Nat.le_self_pow (by omega) p
  have hpow : 2 ^ k ≤ N := by
    calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      _ = m := hpk
      _ ≤ N := hmN
  have hklog : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hpow
  refine Finset.mem_image.mpr ⟨(p, k - 2), ?_, ?_⟩
  · refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Nat.mem_primesLE.mpr ⟨le_trans hple hmN, hp⟩
    · rw [Finset.mem_range]
      omega
  · rw [show k - 2 + 2 = k by omega]
    exact hpk

/-- **The non-prime part of the `Λ·log/id` summatory is `O(log N)`.** -/
theorem sum_nonprime_vonMangoldt_log_div_le (N : ℕ) :
    ∑ m ∈ {m ∈ Finset.Icc 1 N | ¬ m.Prime}, vonMangoldt m * Real.log m / m
      ≤ 24 * (1 + Real.log N) := by
  classical
  set M := Nat.log 2 N with hM
  set prod := Nat.primesLE N ×ˢ Finset.range M with hprodef
  set I := prod.image (fun x => x.1 ^ (x.2 + 2)) with hIdef
  set A := {m ∈ Finset.Icc 1 N | ¬ m.Prime} with hAdef
  set F : ℕ → ℝ := fun m => vonMangoldt m * Real.log m / m with hFdef
  have hFnn : ∀ m : ℕ, 0 ≤ F m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hFdef]
    · have h1 : 0 ≤ vonMangoldt m := vonMangoldt_nonneg
      have h2 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
      have h3 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hFdef]
      positivity
  have hzero : ∀ m ∈ A \ I, F m = 0 := by
    intro m hm
    rw [Finset.mem_sdiff] at hm
    obtain ⟨hmA, hmI⟩ := hm
    rw [hAdef, Finset.mem_filter, Finset.mem_Icc] at hmA
    obtain ⟨⟨_, hmN⟩, hnp⟩ := hmA
    by_cases hΛ : vonMangoldt m = 0
    · rw [hFdef]; simp [hΛ]
    · exact absurd (mem_image_of_nonprime hmN hnp hΛ) hmI
  have hAI : ∑ m ∈ A, F m = ∑ m ∈ A ∩ I, F m := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro m hmA hmnot
    have hmI : m ∉ I := fun h => hmnot (Finset.mem_inter.mpr ⟨hmA, h⟩)
    exact hzero m (Finset.mem_sdiff.mpr ⟨hmA, hmI⟩)
  have hle : ∑ m ∈ A ∩ I, F m ≤ ∑ m ∈ I, F m :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun m _ _ => hFnn m
  have himg : ∑ m ∈ I, F m
      = ∑ x ∈ prod, (((x.2 : ℝ) + 2) * Real.log (x.1 : ℝ) ^ 2 / ((x.1 : ℝ) ^ (x.2 + 2))) := by
    rw [hIdef, Finset.sum_image primePowShift_injOn]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hp, _⟩ := Finset.mem_product.1 hx
    have hpp : x.1.Prime := Nat.prime_of_mem_primesLE hp
    have hΛ : vonMangoldt (x.1 ^ (x.2 + 2)) = Real.log (x.1 : ℝ) := by
      rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hpp]
    rw [hFdef]
    simp only
    rw [hΛ]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [hAI]
  refine le_trans hle ?_
  rw [himg, hprodef]
  exact sum_primePower_weight_le N M

/-- The primes below `N`, as a filtered interval. -/
theorem filter_prime_Icc_eq_primesLE (N : ℕ) :
    {m ∈ Finset.Icc 1 N | m.Prime} = Nat.primesLE N := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2.one_lt.le, h1⟩, h2⟩

/-- **An explicit lower bound for `∑_{p ≤ N} (log p)²/p`.** -/
theorem sum_prime_log_sq_div_ge (N : ℕ) (hN : 1 ≤ N) :
    Real.log N ^ 2 / 2 - 39 * Real.log N - 25
      ≤ ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) ^ 2 / (p : ℝ) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime
    (fun m => vonMangoldt m * Real.log m / m)
  have hval : ∑ p ∈ {m ∈ Finset.Icc 1 N | m.Prime}, vonMangoldt p * Real.log p / p
      = ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) ^ 2 / (p : ℝ) := by
    rw [filter_prime_Icc_eq_primesLE]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]
    ring
  have hnp := sum_nonprime_vonMangoldt_log_div_le N
  have hmain := RHTower.abs_sum_vonMangoldt_log_div_sub_le N hN
  rw [abs_le] at hmain
  rw [hval] at hsplit
  linarith [hmain.1, hmain.2, hsplit, hnp]

end RHTower.Sieve
