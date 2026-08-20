import GaloisForLFunctions.RHTower.Sieve.ShortIntervalPrimeCount
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange
import GaloisForLFunctions.RHTower.Sieve.RamareBlockSplit

/-!
# A ladder step of a designated prime range holds all the primes of its interval

A ladder step `geomBlock (primesRange z₀ z) Q (1+η) j` is by definition the *designated* primes in
`(Q(1+η)^j, Q(1+η)^{j+1}]`.  When the ladder starts at `Q = z₀` and ends at `z = ⌊Q(1+η)^L⌋`, every
prime of that interval is designated: the lower endpoint is at least `z₀` because the ratio is at
least one, and the upper endpoint is at most `z` because a prime below `Q(1+η)^L` is an integer.

Combining with `Sieve/ShortIntervalPrimeCount` turns the prime number theorem with error term into a
lower bound for the size of every ladder step — which is exactly what the moment method needs and
what a purely relative threshold cannot do without.
-/

namespace RHTower.Sieve

open Filter Finset

noncomputable section

/-- **A ladder step of a full designated range holds every prime of its interval.** -/
theorem windowPrimes_subset_geomBlock {z₀ L j : ℕ} {R η : ℝ}
    (hR : R = (z₀ : ℝ)) (hη : 0 ≤ η) (hR0 : 0 < R) (hj : j + 1 ≤ L) :
    windowPrimes (R * (1 + η) ^ j) (R * (1 + η) ^ (j + 1))
      ⊆ geomBlock (primesRange z₀ ⌊R * (1 + η) ^ L⌋₊) R (1 + η) j := by
  classical
  intro p hp
  rw [mem_windowPrimes, Finset.mem_Ioc] at hp
  obtain ⟨⟨hlo, hhi⟩, hprime⟩ := hp
  have h1η : (1 : ℝ) ≤ 1 + η := by linarith
  have hpowj : (1 : ℝ) ≤ (1 + η) ^ j := one_le_pow₀ h1η
  have hlo' : R * (1 + η) ^ j < (p : ℝ) := by
    have := Nat.lt_floor_add_one (R * (1 + η) ^ j)
    have hcast : ((⌊R * (1 + η) ^ j⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
      have : (⌊R * (1 + η) ^ j⌋₊ : ℕ) + 1 ≤ p := hlo
      exact_mod_cast this
    linarith
  have hbase0 : (0 : ℝ) < R * (1 + η) ^ (j + 1) := by positivity
  have hhi' : (p : ℝ) ≤ R * (1 + η) ^ (j + 1) := by
    have hc : (p : ℝ) ≤ ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hhi
    exact hc.trans (Nat.floor_le hbase0.le)
  have hmono : (1 + η) ^ (j + 1) ≤ (1 + η) ^ L :=
    pow_le_pow_right₀ h1η hj
  have hpL : (p : ℝ) ≤ R * (1 + η) ^ L :=
    hhi'.trans (mul_le_mul_of_nonneg_left hmono hR0.le)
  rw [geomBlock, Finset.mem_filter]
  refine ⟨?_, hlo', hhi'⟩
  rw [mem_primesRange]
  refine ⟨hprime, ?_, Nat.le_floor hpL⟩
  have hz₀ : ((z₀ : ℕ) : ℝ) < (p : ℝ) := by
    rw [← hR]
    have : R ≤ R * (1 + η) ^ j := by nlinarith [hR0, hpowj]
    linarith
  exact_mod_cast hz₀

/-- **Every ladder step of a full designated range is large.** -/
theorem card_geomBlock_primesRange_ge {C c y₀ : ℝ}
    (hcount : ∀ y : ℝ, y₀ ≤ y → ∀ η : ℝ, 0 < η → η ≤ 1 →
      16 * C * Real.exp (-c * Real.sqrt (Real.log y)) + 24 * Real.log y / Real.sqrt y ≤ η →
      y * η / (4 * Real.log y) ≤ ((windowPrimes y (y * (1 + η))).card : ℝ))
    {z₀ L j : ℕ} {R η : ℝ} (hR : R = (z₀ : ℝ)) (hR0 : 0 < R) (hη : 0 < η) (hη1 : η ≤ 1)
    (hj : j + 1 ≤ L) (hy₀ : y₀ ≤ R * (1 + η) ^ j)
    (herr : 16 * C * Real.exp (-c * Real.sqrt (Real.log (R * (1 + η) ^ j)))
        + 24 * Real.log (R * (1 + η) ^ j) / Real.sqrt (R * (1 + η) ^ j) ≤ η) :
    R * (1 + η) ^ j * η / (4 * Real.log (R * (1 + η) ^ j))
      ≤ ((geomBlock (primesRange z₀ ⌊R * (1 + η) ^ L⌋₊) R (1 + η) j).card : ℝ) := by
  have hbase := hcount (R * (1 + η) ^ j) hy₀ η hη hη1 herr
  refine hbase.trans ?_
  have hsub : windowPrimes (R * (1 + η) ^ j) (R * (1 + η) ^ j * (1 + η))
      ⊆ geomBlock (primesRange z₀ ⌊R * (1 + η) ^ L⌋₊) R (1 + η) j := by
    have hid : R * (1 + η) ^ j * (1 + η) = R * (1 + η) ^ (j + 1) := by ring
    rw [hid]
    exact windowPrimes_subset_geomBlock hR hη.le hR0 hj
  exact_mod_cast Finset.card_le_card hsub

end

end RHTower.Sieve
