import GaloisForLFunctions.RHTower.Sieve.GallagherAlmostDiagonal
import GaloisForLFunctions.RHTower.Sieve.PrimeInterval

/-!
# Primes in a multiplicative window

The count that the almost-diagonal mean value theorem leaves behind is

`#{m ∈ s : |log n - log m| < δ}`,

the number of indices of the support inside the multiplicative window `(n e^{-δ}, n e^{δ})`.  When the
support consists of primes this is a short-interval prime count, so the Selberg sieve bounds it by

`2·(n(e^δ - e^{-δ}) + 1)/log Y + selbergFibreError z Y + z`

for every admissible sieve level `Y ≤ z`.  The saving of one logarithm over the number of *integers* in
the window is the whole point: it is what turns the weight `Λ(n)²` of the classical mean value theorem
into `Λ(n)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- A multiplicative window of ratio `e^δ` around `n` consists of integers of one interval. -/
theorem logNeighbourCount_le_card_prime_Ioc (s : Finset ℕ) (hs : ∀ m ∈ s, m.Prime)
    {δ : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    logNeighbourCount s δ n
      ≤ #{m ∈ Finset.Ioc ⌊(n : ℝ) * Real.exp (-δ)⌋₊ ⌊(n : ℝ) * Real.exp δ⌋₊ | m.Prime} := by
  classical
  rw [logNeighbourCount]
  refine Finset.card_le_card ?_
  intro m hm
  rw [Finset.mem_filter] at hm
  obtain ⟨hms, hmlog⟩ := hm
  have hmp : m.Prime := hs m hms
  have hm2 : 2 ≤ m := hmp.two_le
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have hmpos : 0 < m := by omega
    exact_mod_cast hmpos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [abs_lt] at hmlog
  have hupper : (m : ℝ) < (n : ℝ) * Real.exp δ := by
    have h := Real.exp_lt_exp.2 (show Real.log (m : ℝ) - Real.log (n : ℝ) < δ by
      linarith [hmlog.1])
    rw [Real.exp_sub, Real.exp_log hmR, Real.exp_log hnR, div_lt_iff₀ hnR] at h
    linarith [h]
  have hlower : (n : ℝ) * Real.exp (-δ) < (m : ℝ) := by
    have h := Real.exp_lt_exp.2 hmlog.2
    rw [Real.exp_sub, Real.exp_log hnR, Real.exp_log hmR, div_lt_iff₀ hmR] at h
    have hprod : Real.exp δ * Real.exp (-δ) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith [h, Real.exp_pos (-δ), hprod]
  rw [Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨?_, ?_⟩, hmp⟩
  · rw [Nat.floor_lt (by positivity)]
    exact hlower
  · exact Nat.le_floor hupper.le

/-- The integer window is not longer than the real one, plus one. -/
theorem floor_sub_floor_le {x y : ℝ} (hy : 0 ≤ y) :
    ((⌊y⌋₊ : ℝ)) - (⌊x⌋₊ : ℝ) ≤ y - x + 1 := by
  have h1 : ((⌊y⌋₊ : ℝ)) ≤ y := Nat.floor_le hy
  have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

/-- **Primes in a multiplicative window.**  The Selberg-sieve short-interval count, transported to the
neighbour count of the almost-diagonal mean value theorem. -/
theorem logNeighbourCount_le_sieve (s : Finset ℕ) (hs : ∀ m ∈ s, m.Prime)
    {δ : ℝ} (hδ : 0 ≤ δ) {n : ℕ} (hn : 1 ≤ n) (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z)
    (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    (logNeighbourCount s δ n : ℝ)
      ≤ 2 * ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) / Real.log Y
        + selbergFibreError z Y + (z : ℝ) := by
  classical
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hexp : Real.exp (-δ) ≤ Real.exp δ := Real.exp_le_exp.2 (by linarith)
  have hab : ⌊(n : ℝ) * Real.exp (-δ)⌋₊ ≤ ⌊(n : ℝ) * Real.exp δ⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left hexp hnR)
  have hcard := card_prime_Ioc_le ⌊(n : ℝ) * Real.exp (-δ)⌋₊ ⌊(n : ℝ) * Real.exp δ⌋₊ z Y
    hab hY hYz hz hlog
  have hsub := logNeighbourCount_le_card_prime_Ioc s hs (δ := δ) hn
  have hsubR : (logNeighbourCount s δ n : ℝ)
      ≤ ((#{m ∈ Finset.Ioc ⌊(n : ℝ) * Real.exp (-δ)⌋₊ ⌊(n : ℝ) * Real.exp δ⌋₊ | m.Prime} : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have hlen : ((⌊(n : ℝ) * Real.exp δ⌋₊ : ℝ)) - ((⌊(n : ℝ) * Real.exp (-δ)⌋₊ : ℝ))
      ≤ (n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1 := by
    have h := floor_sub_floor_le (x := (n : ℝ) * Real.exp (-δ))
      (y := (n : ℝ) * Real.exp δ) (by positivity)
    calc ((⌊(n : ℝ) * Real.exp δ⌋₊ : ℝ)) - ((⌊(n : ℝ) * Real.exp (-δ)⌋₊ : ℝ))
        ≤ (n : ℝ) * Real.exp δ - (n : ℝ) * Real.exp (-δ) + 1 := h
      _ = (n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1 := by ring
  have hmain : 2 * (((⌊(n : ℝ) * Real.exp δ⌋₊ : ℝ)) - ((⌊(n : ℝ) * Real.exp (-δ)⌋₊ : ℝ)))
        / Real.log Y
      ≤ 2 * ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) / Real.log Y := by
    gcongr
  linarith [hsubR, hcard, hmain]


/-- **The prime-supported mean value theorem.**  The almost-diagonal mean value theorem with its
neighbour count discharged by the Selberg sieve: for coefficients supported on primes the frequency mean
square is bounded by the coefficients weighted by a *short-interval prime count*, which carries one
logarithm of saving over the number of integers in the window. -/
theorem integral_Icc_normSq_logPoly_le_prime_sieve (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ m ∈ s, m.Prime) {δ W : ℝ} (hδ : 0 < δ) (hWδ : 2 * Real.pi * δ * W ≤ 1)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ (5 / (4 * δ)) * ∑ n ∈ s,
          (2 * ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) / Real.log Y
            + selbergFibreError z Y + (z : ℝ)) * ‖a n‖ ^ (2 : ℕ) := by
  refine le_trans (integral_Icc_normSq_logPoly_le_count a s hδ hWδ) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) (by positivity)
  have hn1 : 1 ≤ n := (hs n hn).one_lt.le.trans' (by norm_num)
  exact mul_le_mul_of_nonneg_right
    (logNeighbourCount_le_sieve s hs hδ.le hn1 z Y hY hYz hz hlog) (by positivity)

end RHTower.Sieve

end
