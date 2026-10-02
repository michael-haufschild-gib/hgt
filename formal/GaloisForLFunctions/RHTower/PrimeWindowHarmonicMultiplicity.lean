import GaloisForLFunctions.RHTower.PrimeWindowMultiplicity
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import Mathlib.Data.Nat.Cast.Order.Field

open Finset Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower


/-- Each complete cofactor slice retains the original free-prime threshold. -/
theorem card_prime_window_slice_mul_log_le {N H k : ℕ}
    (hH : 1 ≤ H) (hN : H ^ 2 ≤ N) :
    (({p ∈ Nat.primesLE (N / k) | N / H < p}).card : ℝ) * Real.log N ≤
      2 * (N : ℝ) * Real.log 4 * (1 / (k : ℝ)) := by
  let P := {p ∈ Nat.primesLE (N / k) | N / H < p}
  have hN1 : 1 ≤ N := (by nlinarith : 1 ≤ H ^ 2).trans hN
  have hpLog (p : ℕ) (hp : p ∈ P) : Real.log N ≤ 2 * Real.log p := by
    have hmem := Finset.mem_filter.mp hp
    have hNHp : N < p * H := (Nat.div_lt_iff_lt_mul (by omega)).mp hmem.2
    have hHp : H < p := by nlinarith
    have hNp : N ≤ p ^ 2 := by nlinarith
    have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hNpR : (N : ℝ) ≤ (p : ℝ) ^ 2 := by exact_mod_cast hNp
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hNR hNpR
  have hsum : ∑ p ∈ P, Real.log p ≤ (N / k : ℕ) * Real.log 4 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (show P ⊆ Nat.primesLE (N / k) from Finset.filter_subset _ _) ?_)
      (Sieve.sum_log_primesLE_le (N / k))
    intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
  have hdiv : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc
    _ = ∑ _p ∈ P, Real.log N := by simp [P]
    _ ≤ ∑ p ∈ P, 2 * Real.log p := Finset.sum_le_sum hpLog
    _ = 2 * ∑ p ∈ P, Real.log p := by rw [Finset.mul_sum]
    _ ≤ 2 * (((N / k : ℕ) : ℝ) * Real.log 4) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ 2 * (((N : ℝ) / k) * Real.log 4) := by gcongr
    _ = _ := by ring

/-- Keeping the complete product cutoff in each cofactor slice replaces
linear cofactor cost by its harmonic mass. -/
theorem card_primeWindowSupported_mul_log_le_harmonic {S : Finset ℕ} {N H : ℕ}
    (hH : 1 ≤ H) (hN : H ^ 2 ≤ N) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    ((primeWindowSupported S N H).card : ℝ) * Real.log N ≤
      2 * (N : ℝ) * Real.log 4 * ∑ k ∈ Finset.Icc 1 H, 1 / (k : ℝ) := by
  classical
  let P : ℕ → Finset ℕ := fun k => {p ∈ Nat.primesLE (N / k) | N / H < p}
  have hsub : primeWindowSupported S N H ⊆
      (Finset.Icc 1 H).biUnion (fun k => (P k).image (fun p => p * k)) := by
    intro n hn
    obtain ⟨hnS, p, hp, k, hnk⟩ := Finset.mem_filter.mp hn
    have hnkpos : 0 < p * k := by simpa [hnk] using (hS n hnS).1
    have hk0 : 0 < k := by nlinarith
    have hpk : p * k ≤ N := by simpa [hnk] using (hS n hnS).2
    have hNHp : N < p * H := (Nat.div_lt_iff_lt_mul (by omega)).mp (mem_largePrimes.mp hp).2
    have hkH : k ≤ H := by nlinarith
    have hpSlice : p ∈ P k := by
      apply Finset.mem_filter.mpr
      refine ⟨Nat.mem_primesLE.mpr ⟨?_, (mem_largePrimes.mp hp).1.2⟩, (mem_largePrimes.mp hp).2⟩
      exact (Nat.le_div_iff_mul_le hk0).mpr hpk
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk0, hkH⟩,
      Finset.mem_image.mpr ⟨p, hpSlice, hnk.symm⟩⟩
  have hcard : (primeWindowSupported S N H).card ≤ ∑ k ∈ Finset.Icc 1 H, (P k).card := by
    calc
      _ ≤ ((Finset.Icc 1 H).biUnion (fun k => (P k).image (fun p => p * k))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ k ∈ Finset.Icc 1 H, ((P k).image (fun p => p * k)).card := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun k _ => Finset.card_image_le)
  have hcR : ((primeWindowSupported S N H).card : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 H, ((P k).card : ℝ) := by exact_mod_cast hcard
  have hN1 : 1 ≤ N := (by nlinarith : 1 ≤ H ^ 2).trans hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  calc
    _ ≤ (∑ k ∈ Finset.Icc 1 H, ((P k).card : ℝ)) * Real.log N :=
      mul_le_mul_of_nonneg_right hcR hlog
    _ = ∑ k ∈ Finset.Icc 1 H, ((P k).card : ℝ) * Real.log N := Finset.sum_mul _ _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 H, 2 * (N : ℝ) * Real.log 4 * (1 / (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact card_prime_window_slice_mul_log_le hH hN
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Explicit logarithmic cofactor occupancy, valid throughout the square-root seam. -/
theorem card_primeWindowSupported_mul_log_le_log {S : Finset ℕ} {N H : ℕ}
    (hH : 1 ≤ H) (hN : H ^ 2 ≤ N) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    ((primeWindowSupported S N H).card : ℝ) * Real.log N ≤
      2 * (N : ℝ) * Real.log 4 * (1 + Real.log H) := by
  apply (card_primeWindowSupported_mul_log_le_harmonic hH hN hS).trans
  exact mul_le_mul_of_nonneg_left (Sieve.sum_Icc_one_div_le_one_add_log H)
    (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity)

end RHTower
