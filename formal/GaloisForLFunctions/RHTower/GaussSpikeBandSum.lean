import GaloisForLFunctions.RHTower.GaussShiftRatioWeight

/-!
# The spike band of the shifted diagonal has linear mass

The sampled ratio at the shifted frequency `l` is bounded by the square root of the harmonic
factor `K·n/|n+l|`.  Summed over the spike `2|n+l| < n` — a band of width `n` at height at most
`(K n/|n+l|)^{1/2}` — the total mass is linear in `n`, because a sub-unit power weight on a
punctured band of radius `n` has mass `O(n^{1/2})`.

This is the estimate that makes the spike harmless once the vector it is applied to has
coefficients of size `O(log n / n)` there.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ} {k : Fin m} {p : Nat.Primes}

/-- The sampled ratio is bounded by the square root of the largest harmonic factor. -/
theorem gaussShiftRatio_sq_le_global (hm : 2 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (l : ℤ) :
    gaussShiftRatio k p (I : ℤ) l ^ 2 ≤ 1 + (K * (I : ℝ)) ^ (1 / 2 : ℝ) := by
  have hnn : (0 : ℝ) ≤ (K * (I : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  rcases eq_or_ne ((I : ℤ) + l) 0 with h0 | h0
  · have hzero : gaussShiftRatio k p (I : ℤ) l = 0 := by
      rw [gaussShiftRatio, h0, gaussSampleValue_zero, norm_zero, zero_div]
    rw [hzero]
    nlinarith
  · have hbase := gaussShiftRatio_sq_le_sqrt hm k p hK hKb I l
    have hr1 : (1 : ℝ) ≤ ((((I : ℤ) + l).natAbs : ℕ) : ℝ) := by
      have h1 : 1 ≤ ((I : ℤ) + l).natAbs := by omega
      exact_mod_cast h1
    have hdiv : K * (I : ℝ) / ((((I : ℤ) + l).natAbs : ℕ) : ℝ) ≤ K * (I : ℝ) := by
      have hKI : (0 : ℝ) ≤ K * (I : ℝ) := by positivity
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hKI, hr1]
    have hmono := Real.rpow_le_rpow (by positivity) hdiv (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith

/-- **The spike band carries linear mass.** -/
theorem tsum_spike_gaussShiftRatio_sq_le (hm : 2 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) :
    ∑' l : ℤ, (if 2 * ((I : ℤ) + l).natAbs < I then
        ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2) else 0)
      ≤ ENNReal.ofReal ((2 + 4 * K ^ (1 / 2 : ℝ)) * (I : ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos I with hI0 | hIpos
  · subst hI0
    have hzero : ∀ l : ℤ, (if 2 * (((0 : ℕ) : ℤ) + l).natAbs < (0 : ℕ) then
        ENNReal.ofReal (gaussShiftRatio k p ((0 : ℕ) : ℤ) l ^ 2) else 0) = 0 := by
      intro l
      exact if_neg (by omega)
    rw [tsum_congr hzero, tsum_zero]
    exact _root_.zero_le
  set F : ℤ → ℝ≥0∞ := fun l => if 2 * ((I : ℤ) + l).natAbs < I then
    ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) l ^ 2) else 0 with hF
  have hre : ∑' l : ℤ, F l = ∑' r : ℤ, F (r - (I : ℤ)) :=
    (Equiv.tsum_eq (Equiv.subRight ((I : ℤ))) F).symm
  have hKsqrt : (0 : ℝ) ≤ K ^ (1 / 2 : ℝ) := Real.rpow_nonneg hK.le _
  have hIsqrt : (0 : ℝ) ≤ (I : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg I) _
  have hpoint : ∀ r : ℤ, F (r - (I : ℤ))
      ≤ (if 2 * r.natAbs < I then (1 : ℝ≥0∞) else 0)
        + (if 0 < r.natAbs ∧ r.natAbs < I then
            ENNReal.ofReal ((K * (I : ℝ)) ^ (1 / 2 : ℝ)) *
              ENNReal.ofReal (((r.natAbs : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) else 0) := by
    intro r
    have hidx : ((I : ℤ) + (r - (I : ℤ))) = r := by ring
    by_cases hsp : 2 * r.natAbs < I
    swap
    · have : F (r - (I : ℤ)) = 0 := by
        rw [hF]
        exact if_neg (by rw [hidx]; exact hsp)
      rw [this]
      exact _root_.zero_le
    have hFval : F (r - (I : ℤ))
        = ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) (r - (I : ℤ)) ^ 2) := by
      rw [hF]
      exact if_pos (by rw [hidx]; exact hsp)
    rcases eq_or_ne r 0 with hr0 | hr0
    · have hzero : gaussShiftRatio k p (I : ℤ) (r - (I : ℤ)) = 0 := by
        rw [gaussShiftRatio, show (I : ℤ) + (r - (I : ℤ)) = r from by ring, hr0,
          gaussSampleValue_zero, norm_zero, zero_div]
      have hz2 : ENNReal.ofReal ((0 : ℝ) ^ 2) = 0 := by norm_num
      rw [hFval, hzero, hz2]
      exact _root_.zero_le
    · have hrpos : 0 < r.natAbs := by omega
      have hrlt : r.natAbs < I := by omega
      have hbase := gaussShiftRatio_sq_le_sqrt hm k p hK hKb I (r - (I : ℤ))
      rw [hidx] at hbase
      have hr1 : (1 : ℝ) ≤ ((r.natAbs : ℕ) : ℝ) := by exact_mod_cast hrpos
      have hsplit : (K * (I : ℝ) / ((r.natAbs : ℕ) : ℝ)) ^ (1 / 2 : ℝ)
          = (K * (I : ℝ)) ^ (1 / 2 : ℝ) * ((r.natAbs : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by
        rw [Real.div_rpow (by positivity) (by linarith),
          Real.rpow_neg (by linarith), div_eq_mul_inv]
      rw [hsplit] at hbase
      rw [hFval]
      have hprodnn : (0 : ℝ) ≤ (K * (I : ℝ)) ^ (1 / 2 : ℝ) *
          ((r.natAbs : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
      calc ENNReal.ofReal (gaussShiftRatio k p (I : ℤ) (r - (I : ℤ)) ^ 2)
          ≤ ENNReal.ofReal (1 + (K * (I : ℝ)) ^ (1 / 2 : ℝ) *
              ((r.natAbs : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) := ENNReal.ofReal_le_ofReal hbase
        _ = ENNReal.ofReal 1 + ENNReal.ofReal ((K * (I : ℝ)) ^ (1 / 2 : ℝ) *
              ((r.natAbs : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) :=
              ENNReal.ofReal_add (by norm_num) hprodnn
        _ ≤ (if 2 * r.natAbs < I then (1 : ℝ≥0∞) else 0)
              + (if 0 < r.natAbs ∧ r.natAbs < I then
                  ENNReal.ofReal ((K * (I : ℝ)) ^ (1 / 2 : ℝ)) *
                    ENNReal.ofReal (((r.natAbs : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) else 0) := by
              rw [if_pos hsp, if_pos ⟨hrpos, hrlt⟩, ENNReal.ofReal_one,
                ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  refine le_trans (le_of_eq hre) (le_trans (ENNReal.tsum_le_tsum hpoint) ?_)
  rw [ENNReal.tsum_add]
  have hband : ∑' r : ℤ, (if 2 * r.natAbs < I then (1 : ℝ≥0∞) else 0) ≤ 2 * (I : ℝ≥0∞) := by
    refine le_trans (ENNReal.tsum_le_tsum fun r => ?_) (tsum_int_band_one_le I)
    by_cases h : 2 * r.natAbs < I
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h]
      exact _root_.zero_le
  have hpow : ∑' r : ℤ, (if 0 < r.natAbs ∧ r.natAbs < I then
        ENNReal.ofReal ((K * (I : ℝ)) ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal (((r.natAbs : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) else 0)
      ≤ ENNReal.ofReal ((K * (I : ℝ)) ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal (4 * (I : ℝ) ^ (1 / 2 : ℝ)) := by
    have hmove : ∀ r : ℤ, (if 0 < r.natAbs ∧ r.natAbs < I then
        ENNReal.ofReal ((K * (I : ℝ)) ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal (((r.natAbs : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) else 0)
        = ENNReal.ofReal ((K * (I : ℝ)) ^ (1 / 2 : ℝ)) *
          (if 0 < r.natAbs ∧ r.natAbs < I then
            ENNReal.ofReal (((r.natAbs : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) else 0) := by
      intro r
      by_cases h : 0 < r.natAbs ∧ r.natAbs < I
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [tsum_congr hmove, ENNReal.tsum_mul_left]
    refine mul_le_mul_right ?_ _
    have hbase := tsum_int_punctured_band_rpow_le (t := 1 / 2) (by norm_num) (by norm_num) I
    refine hbase.trans (le_of_eq ?_)
    congr 1
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num]
    ring
  refine le_trans (add_le_add hband hpow) ?_
  have hmulI : (K * (I : ℝ)) ^ (1 / 2 : ℝ) * (4 * (I : ℝ) ^ (1 / 2 : ℝ))
      = 4 * K ^ (1 / 2 : ℝ) * (I : ℝ) := by
    have hIpos' : (0 : ℝ) < (I : ℝ) := by exact_mod_cast hIpos
    rw [Real.mul_rpow hK.le (le_of_lt hIpos')]
    have hsq : (I : ℝ) ^ (1 / 2 : ℝ) * (I : ℝ) ^ (1 / 2 : ℝ) = (I : ℝ) := by
      rw [← Real.rpow_add hIpos']
      norm_num
    calc K ^ (1 / 2 : ℝ) * (I : ℝ) ^ (1 / 2 : ℝ) * (4 * (I : ℝ) ^ (1 / 2 : ℝ))
        = 4 * K ^ (1 / 2 : ℝ) * ((I : ℝ) ^ (1 / 2 : ℝ) * (I : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = 4 * K ^ (1 / 2 : ℝ) * (I : ℝ) := by rw [hsq]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), hmulI,
    show (2 : ℝ≥0∞) * (I : ℝ≥0∞) = ENNReal.ofReal (2 * (I : ℝ)) from by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
      norm_num,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

end

end RHTower
