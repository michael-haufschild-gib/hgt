import GaloisForLFunctions.RHTower.Sieve.ReciprocalPhaseStability

/-!
# The parity correction of a von Mangoldt sum

Restricting a von Mangoldt sum by a congruence modulo two removes nothing but the powers of two,
because `Λ` is supported on prime powers and the only even prime power is a power of two.  Since
the powers of two below `N` number `log₂ N`, each carrying the weight `log 2`, the whole correction
is at most `log N` — polylogarithmic against any power saving.
-/

namespace RHTower.Sieve

open Real ArithmeticFunction

noncomputable section

/-- An even integer in the support of `Λ` is a power of two. -/
theorem eq_two_pow_of_vonMangoldt_ne_zero {m : ℕ} (h : Λ m ≠ 0) (h2 : 2 ∣ m) :
    ∃ j : ℕ, 1 ≤ j ∧ m = 2 ^ j := by
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff m).1 (vonMangoldt_ne_zero_iff.1 h)
  have hdvd : (2 : ℕ) ∣ p ^ k := hpk ▸ h2
  have hp2 : p = 2 := by
    have h2p : (2 : ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2p).symm
  exact ⟨k, hk, by rw [← hpk, hp2]⟩

/-- **The parity correction.**  The even part of a von Mangoldt sum is at most `log N`. -/
theorem sum_vonMangoldt_even_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => 2 ∣ m), Λ m ≤ Real.log N := by
  classical
  set s : Finset ℕ := (Finset.Icc 1 N).filter (fun m => 2 ∣ m) with hs
  set t : Finset ℕ := s.filter (fun m => Λ m ≠ 0) with ht
  have hzero : ∑ m ∈ s, Λ m = ∑ m ∈ t, Λ m := by
    rw [ht, Finset.sum_filter_ne_zero]
  rw [hzero]
  have hsub : t ⊆ Finset.image (fun j : ℕ => 2 ^ j) (Finset.Icc 1 (Nat.log 2 N)) := by
    intro m hm
    rw [ht, Finset.mem_filter, hs, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨j, hj1, hj⟩ := eq_two_pow_of_vonMangoldt_ne_zero hm.2 hm.1.2
    refine Finset.mem_image.2 ⟨j, ?_, hj.symm⟩
    rw [Finset.mem_Icc]
    refine ⟨hj1, Nat.le_log_of_pow_le (by norm_num) ?_⟩
    rw [← hj]
    exact hm.1.1.2
  have hterm : ∀ m ∈ t, Λ m ≤ Real.log 2 := by
    intro m hm
    rw [ht, Finset.mem_filter, hs, Finset.mem_filter] at hm
    obtain ⟨j, hj1, hj⟩ := eq_two_pow_of_vonMangoldt_ne_zero hm.2 hm.1.2
    rw [hj, vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hcard : (t.card : ℝ) ≤ (Nat.log 2 N : ℝ) := by
    have h1 : t.card ≤ (Finset.image (fun j : ℕ => 2 ^ j) (Finset.Icc 1 (Nat.log 2 N))).card :=
      Finset.card_le_card hsub
    have h2 : (Finset.image (fun j : ℕ => 2 ^ j) (Finset.Icc 1 (Nat.log 2 N))).card
        ≤ (Finset.Icc 1 (Nat.log 2 N)).card := Finset.card_image_le
    have h3 : (Finset.Icc 1 (Nat.log 2 N)).card = Nat.log 2 N := by
      rw [Nat.card_Icc]
      omega
    have : t.card ≤ Nat.log 2 N := by omega
    exact_mod_cast this
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc ∑ m ∈ t, Λ m ≤ ∑ _m ∈ t, Real.log 2 := Finset.sum_le_sum hterm
    _ = (t.card : ℝ) * Real.log 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.log 2 N : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hcard hlog2.le
    _ ≤ Real.log N := by
        have hpow : (2 : ℕ) ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
        have hpowR : ((2 : ℝ)) ^ (Nat.log 2 N) ≤ (N : ℝ) := by exact_mod_cast hpow
        have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hle := Real.log_le_log (by positivity) hpowR
        rw [Real.log_pow] at hle
        linarith

end

end RHTower.Sieve
