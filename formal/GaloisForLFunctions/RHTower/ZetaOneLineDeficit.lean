import GaloisForLFunctions.RHTower.ZetaEulerLogPrimeSum
import GaloisForLFunctions.RHTower.EulerTiltMeanEnergy

/-!
# The zeta one-line deficit is the prime clock energy

At the canonical shift `δ = 1/log x` the logarithmic modulus of zeta on the line `Re s = 1 + δ`
differs from the prime clock energy by one absolute constant, uniformly in the frequency:

```text
log log x - log |ζ(1 + 1/log x + iτ)| = ∑_{p ≤ x} (1 - cos(τ log p))/p + O(1).
```

The three corrections are the prime-power correction of the Euler logarithm, the abscissa shift on
the head `p ≤ x`, and the tail `p > x`, which is bounded because a prime beyond `x` carries a
logarithm at least `log x`.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Prime-indexed coefficient sequences -/

/-- The prime rpow coefficient, extended by zero. -/
def primeRpowCoeff (σ : ℝ) (n : ℕ) : ℝ := if n.Prime then (n : ℝ) ^ (-σ) else 0

/-- The prime rpow-logarithm coefficient, extended by zero. -/
def primeRpowLogCoeff (σ : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then (n : ℝ) ^ (-σ) * Real.log n else 0

theorem primeRpowCoeff_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ primeRpowCoeff σ n := by
  rw [primeRpowCoeff]
  split
  · positivity
  · exact le_rfl

theorem primeRpowLogCoeff_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ primeRpowLogCoeff σ n := by
  rw [primeRpowLogCoeff]
  split
  · rename_i hp
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.one_lt.le
    have hlog : 0 ≤ Real.log n := Real.log_nonneg h1
    positivity
  · exact le_rfl

theorem primeRpowCoeff_le_invRpow (σ : ℝ) (n : ℕ) :
    primeRpowCoeff σ n ≤ 1 / (n : ℝ) ^ σ := by
  rw [primeRpowCoeff]
  split
  · rename_i hp
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    rw [Real.rpow_neg hn0.le, one_div]
  · positivity

theorem primeRpowLogCoeff_le_logDiv (σ : ℝ) (n : ℕ) :
    primeRpowLogCoeff σ n ≤ Real.log n / (n : ℝ) ^ σ := by
  rw [primeRpowLogCoeff]
  split
  · rename_i hp
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    rw [Real.rpow_neg hn0.le]
    rw [div_eq_mul_inv]
    ring
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hlog : 0 ≤ Real.log n := Real.log_nonneg h1
      positivity

theorem summable_primeRpowCoeff {σ : ℝ} (hσ : 1 < σ) : Summable (primeRpowCoeff σ) :=
  Summable.of_nonneg_of_le (fun n => primeRpowCoeff_nonneg σ n)
    (fun n => primeRpowCoeff_le_invRpow σ n) (Real.summable_one_div_nat_rpow.mpr hσ)

theorem summable_primeRpowLogCoeff {σ : ℝ} (hσ : 1 < σ) : Summable (primeRpowLogCoeff σ) :=
  Summable.of_nonneg_of_le (fun n => primeRpowLogCoeff_nonneg σ n)
    (fun n => primeRpowLogCoeff_le_logDiv σ n) (Mertens.summable_log_div_rpow hσ)

/-! ## Finite prime sums -/

theorem sum_range_primeRpowLogCoeff (σ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), primeRpowLogCoeff σ n
      = ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-σ) * Real.log p := by
  rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => rfl

theorem sum_range_primeRpowCoeff (σ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), primeRpowCoeff σ n
      = ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-σ) := by
  rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => rfl

/-- The uniform bound for the full tilted prime logarithm sum. -/
def tiltedPrimeLogTotalConst : ℝ := tiltedPrimeLogSumConst + Real.log 2

theorem tiltedPrimeLogTotalConst_nonneg : 0 ≤ tiltedPrimeLogTotalConst := by
  have h1 : 0 ≤ tiltedPrimeLogSumConst := by
    rw [tiltedPrimeLogSumConst]
    have := thetaRelMass_nonneg
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [tiltedPrimeLogTotalConst]
  linarith

theorem sum_primesLE_rpowLog_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(1 + δ)) * Real.log p
      ≤ 1 / δ + tiltedPrimeLogTotalConst := by
  have hconst := tiltedPrimeLogTotalConst_nonneg
  rcases lt_or_ge N 2 with hN | hN
  · have hzero : ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(1 + δ)) * Real.log p = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hprime := Nat.prime_of_mem_primesLE hp
      have hple : p ≤ N := (Nat.mem_primesLE.mp hp).1
      omega_nat
    rw [hzero]
    positivity
  · have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
    have hexp : ∀ p : ℕ, (p : ℝ) ^ (-(1 + δ)) * Real.log p
        = (p : ℝ) ^ (-δ - 1) * Real.log p := by
      intro p
      congr 2
      ring
    have hsum : ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(1 + δ)) * Real.log p
        = tiltedPrimeLogSumLE δ (N : ℝ) := by
      rw [tiltedPrimeLogSumLE, hfloor]
      exact Finset.sum_congr rfl fun p _ => hexp p
    rw [hsum, tiltedPrimeLogSumLE_eq hNR]
    have hbound := abs_le.mp (abs_tiltedPrimeLogSum_sub_le hδ0 hδ1 hNR)
    have hrp : (2 : ℝ) ^ (-δ - 1) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show -δ - 1 ≤ 0 by linarith)
      rwa [Real.rpow_zero] at h
    have hrp0 : (0 : ℝ) < (2 : ℝ) ^ (-δ - 1) := Real.rpow_pos_of_pos (by norm_num) _
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hNrp : (0 : ℝ) < (N : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by linarith) _
    have hdiv : (1 - (N : ℝ) ^ (-δ)) / δ ≤ 1 / δ := by
      rw [div_le_div_iff_of_pos_right hδ0]
      linarith
    rw [tiltedPrimeLogTotalConst]
    nlinarith [hbound.2, hrp, hrp0, hlog2, hdiv]

theorem tsum_primeRpowLogCoeff_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∑' n : ℕ, primeRpowLogCoeff (1 + δ) n ≤ 1 / δ + tiltedPrimeLogTotalConst := by
  have hsummable : Summable (primeRpowLogCoeff (1 + δ)) :=
    summable_primeRpowLogCoeff (by linarith)
  refine tsum_le_of_sum_le hsummable fun s => ?_
  obtain ⟨k, hk⟩ := s.exists_nat_subset_range
  have hmono : ∑ n ∈ s, primeRpowLogCoeff (1 + δ) n
      ≤ ∑ n ∈ Finset.range k, primeRpowLogCoeff (1 + δ) n :=
    Finset.sum_le_sum_of_subset_of_nonneg hk fun n _ _ => primeRpowLogCoeff_nonneg _ n
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have hzero : ∑ n ∈ Finset.range 0, primeRpowLogCoeff (1 + δ) n = 0 := by simp
    have hconst := tiltedPrimeLogTotalConst_nonneg
    have hδinv : 0 < 1 / δ := by positivity
    linarith [hmono, hzero.le, hzero.ge]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
    rw [sum_range_primeRpowLogCoeff] at hmono
    exact le_trans hmono (sum_primesLE_rpowLog_le hδ0 hδ1 m)

end

end RHTower
