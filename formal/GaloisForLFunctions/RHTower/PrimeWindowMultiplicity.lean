import GaloisForLFunctions.RHTower.MobiusFriableLargestPrimeDecomposition
import GaloisForLFunctions.RHTower.Sieve.Mertens
import Mathlib.Data.Finset.Prod

open Finset Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower


/-- Integers of a selected support carrying a prime in the literal free window. -/
def primeWindowSupported (S : Finset ℕ) (N H : ℕ) : Finset ℕ :=
  S.filter fun n => ∃ p ∈ largePrimes N (N / H), p ∣ n

/-- A cofactor window above `N/H` has only logarithmically many prime coordinates. -/
theorem card_largePrimes_mul_log_le {N H : ℕ} (hH : 1 ≤ H) (hN : H ^ 2 ≤ N) :
    ((largePrimes N (N / H)).card : ℝ) * Real.log N ≤
      2 * (N : ℝ) * Real.log 4 := by
  have hN1 : 1 ≤ N := (by nlinarith : 1 ≤ H ^ 2).trans hN
  have hlog (p : ℕ) (hp : p ∈ largePrimes N (N / H)) :
      Real.log N ≤ 2 * Real.log p := by
    have hmem := mem_largePrimes.mp hp
    have hNHp : N < p * H := (Nat.div_lt_iff_lt_mul (by omega)).mp hmem.2
    have hHp : H < p := by nlinarith
    have hNp : N ≤ p ^ 2 := by nlinarith
    have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hNpR : (N : ℝ) ≤ (p : ℝ) ^ 2 := by exact_mod_cast hNp
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hNR hNpR
  have hsub : largePrimes N (N / H) ⊆ Nat.primesLE N := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hsum : ∑ p ∈ largePrimes N (N / H), Real.log p ≤
      ∑ p ∈ Nat.primesLE N, Real.log p := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
  calc
    _ = ∑ _p ∈ largePrimes N (N / H), Real.log N := by simp
    _ ≤ ∑ p ∈ largePrimes N (N / H), 2 * Real.log p := Finset.sum_le_sum hlog
    _ = 2 * ∑ p ∈ largePrimes N (N / H), Real.log p := by rw [Finset.mul_sum]
    _ ≤ 2 * ((N : ℝ) * Real.log 4) :=
      mul_le_mul_of_nonneg_left (hsum.trans (Sieve.sum_log_primesLE_le N)) (by norm_num)
    _ = _ := by ring

/-- Every selected free-window integer comes from one prime and a cofactor below `H`.
The count keeps the entire selected support and does not require uniqueness. -/
theorem card_primeWindowSupported_le {S : Finset ℕ} {N H : ℕ} (hH : 1 ≤ H)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (primeWindowSupported S N H).card ≤ (largePrimes N (N / H)).card * H := by
  classical
  have hsub : primeWindowSupported S N H ⊆
      ((largePrimes N (N / H)) ×ˢ Finset.range H).image (fun z : ℕ × ℕ => z.1 * z.2) := by
    intro n hn
    obtain ⟨hnS, p, hp, k, hnk⟩ := Finset.mem_filter.mp hn
    have hNHp : N < p * H := (Nat.div_lt_iff_lt_mul (by omega)).mp (mem_largePrimes.mp hp).2
    have hpk : p * k ≤ N := by simpa [hnk] using (hS n hnS).2
    have hp0 := (mem_largePrimes.mp hp).1.2.pos
    have hk : k < H := by nlinarith
    exact Finset.mem_image.mpr ⟨(p, k), Finset.mem_product.mpr ⟨hp, Finset.mem_range.mpr hk⟩,
      hnk.symm⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  simpa only [Finset.card_product, Finset.card_range] using hcard

/-- Complete free-window occupancy obeys a uniform, explicit cofactor/logarithm budget. -/
theorem card_primeWindowSupported_mul_log_le {S : Finset ℕ} {N H : ℕ}
    (hH : 1 ≤ H) (hN : H ^ 2 ≤ N) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    ((primeWindowSupported S N H).card : ℝ) * Real.log N ≤
      2 * (H : ℝ) * N * Real.log 4 := by
  have hN1 : 1 ≤ N := (by nlinarith : 1 ≤ H ^ 2).trans hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hc : ((primeWindowSupported S N H).card : ℝ) ≤
      ((largePrimes N (N / H)).card : ℝ) * H := by
    exact_mod_cast card_primeWindowSupported_le hH hS
  calc
    _ ≤ (((largePrimes N (N / H)).card : ℝ) * H) * Real.log N :=
      mul_le_mul_of_nonneg_right hc hlog
    _ = (H : ℝ) * (((largePrimes N (N / H)).card : ℝ) * Real.log N) := by ring
    _ ≤ (H : ℝ) * (2 * (N : ℝ) * Real.log 4) :=
      mul_le_mul_of_nonneg_left (card_largePrimes_mul_log_le hH hN) (Nat.cast_nonneg H)
    _ = _ := by ring

/-- At fixed cofactor budget every free-window part occupies a vanishing
fraction of the height-scale integer support. -/
theorem eventually_card_primeWindowSupported_le (H : ℕ) (hH : 1 ≤ H)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ n ≤ N) →
      ((primeWindowSupported S N H).card : ℝ) ≤ ε * N := by
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (2 * (H : ℝ) * Real.log 4 / ε),
    eventually_ge_atTop (H ^ 2), eventually_ge_atTop (2 : ℕ)] with N hlog hN hN2
  intro S hS
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 2 * (H : ℝ) * Real.log 4 ≤ ε * Real.log N := by
    have hh := (div_le_iff₀ hε).mp hlog
    nlinarith only [hh]
  refine le_of_mul_le_mul_right ?_ hlogpos
  calc
    _ ≤ 2 * (H : ℝ) * N * Real.log 4 := card_primeWindowSupported_mul_log_le hH hN hS
    _ = (2 * (H : ℝ) * Real.log 4) * N := by ring
    _ ≤ (ε * Real.log N) * N := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg N)
    _ = _ := by ring

end RHTower
