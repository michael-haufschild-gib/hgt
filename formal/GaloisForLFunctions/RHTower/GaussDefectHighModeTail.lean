import GaloisForLFunctions.RHTower.GaussSpikeBandSum

/-!
# The high-mode tail of the lattice defect

For an amplitude with harmonic decay the defect mass carried by the frequencies outside a band of
radius `J` is controlled by two effects: the quadratic tail of the amplitude, and the harmonic
spike of the lattice ratio.  The spike sits at `|n+j| < n/2`, where the amplitude weight is already
of size `1/n²`, so the spike contributes only `O(log n / n)`.

The resulting bound `O(1/J) + O(log n / n)` is what makes the truncation error of the defect small
at the scale `J ≍ n`.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions

open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

/-- **The high-mode defect tail.**  Outside a band of radius `J` the harmonically decaying
amplitude carries defect mass `O(1/J) + O(log n / n)`. -/
theorem tsum_defect_highMode_le (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (A : ℝ) (I J : ℕ) :
    ∑' j : ℤ, (if J < j.natAbs then
        ENNReal.ofReal ((A / (1 + (j.natAbs : ℝ))) ^ 2 *
          ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2) else 0)
      ≤ ENNReal.ofReal (16 * A ^ 2 * (1 + K) / (1 + (J : ℝ))
          + 16 * K * A ^ 2 * (1 + Real.log (I : ℝ)) / (I : ℝ)) := by
  classical
  set T1 : ℤ → ℝ≥0∞ := fun j =>
    if J < j.natAbs then ENNReal.ofReal (4 * A ^ 2 * (1 / (1 + (j.natAbs : ℝ)) ^ 2)) else 0 with hT1
  set T2 : ℤ → ℝ≥0∞ := fun j =>
    if J < j.natAbs then
      ENNReal.ofReal (4 * K * A ^ 2 * (1 / (1 + (j.natAbs : ℝ)) ^ 2)) else 0 with hT2
  set T3 : ℤ → ℝ≥0∞ := fun j =>
    if 2 * ((I : ℤ) + j).natAbs < I then
      ENNReal.ofReal (8 * K * A ^ 2 / ((I : ℝ) * ((((I : ℤ) + j).natAbs : ℕ) : ℝ))) else 0 with hT3
  have hpoint : ∀ j : ℤ, (if J < j.natAbs then
      ENNReal.ofReal ((A / (1 + (j.natAbs : ℝ))) ^ 2 *
        ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2) else 0)
      ≤ T1 j + T2 j + T3 j := by
    intro j
    by_cases hj : J < j.natAbs
    swap
    · rw [if_neg hj]
      exact _root_.zero_le
    rw [if_pos hj]
    have hdef := norm_gaussSampleRatioDefect_sq_le hm k p hKb I j
    have hamp : (0 : ℝ) ≤ (A / (1 + (j.natAbs : ℝ))) ^ 2 := by positivity
    have hden : (0 : ℝ) < (1 + (j.natAbs : ℝ)) ^ 2 := by positivity
    by_cases hreg : I ≤ 2 * ((I : ℤ) + j).natAbs
    · -- away from the spike the harmonic factor is bounded
      have hquot : 2 * K * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℕ) : ℝ) ≤ 4 * K := by
        rcases Nat.eq_zero_or_pos ((I : ℤ) + j).natAbs with h0 | hpos
        · rw [h0]
          simp only [Nat.cast_zero, div_zero]
          positivity
        · have hposR : (0 : ℝ) < ((((I : ℤ) + j).natAbs : ℕ) : ℝ) := by exact_mod_cast hpos
          have hI : (I : ℝ) ≤ 2 * ((((I : ℤ) + j).natAbs : ℕ) : ℝ) := by exact_mod_cast hreg
          rw [div_le_iff₀ hposR]
          nlinarith [hK.le]
      have hstep : (A / (1 + (j.natAbs : ℝ))) ^ 2 *
          ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2
          ≤ 4 * A ^ 2 * (1 / (1 + (j.natAbs : ℝ)) ^ 2)
            + 4 * K * A ^ 2 * (1 / (1 + (j.natAbs : ℝ)) ^ 2) := by
        have hb : ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 ≤ 4 + 4 * K := by
          linarith [hdef, hquot]
        have hmul := mul_le_mul_of_nonneg_left hb hamp
        refine hmul.trans (le_of_eq ?_)
        rw [div_pow]
        field_simp
      calc ENNReal.ofReal ((A / (1 + (j.natAbs : ℝ))) ^ 2 *
            ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2)
          ≤ ENNReal.ofReal (4 * A ^ 2 * (1 / (1 + (j.natAbs : ℝ)) ^ 2)
              + 4 * K * A ^ 2 * (1 / (1 + (j.natAbs : ℝ)) ^ 2)) :=
            ENNReal.ofReal_le_ofReal hstep
        _ = T1 j + T2 j := by
            rw [hT1, hT2]
            simp only [if_pos hj]
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ T1 j + T2 j + T3 j := le_add_right le_rfl
    · -- on the spike the amplitude weight is already of size `1/I²`
      have hspike : 2 * ((I : ℤ) + j).natAbs < I := by omega
      have hIpos : 0 < I := by omega
      have hjbig : I < 2 * (1 + j.natAbs) := by omega
      have hjbigR : (I : ℝ) < 2 * (1 + (j.natAbs : ℝ)) := by exact_mod_cast hjbig
      have hstep : (A / (1 + (j.natAbs : ℝ))) ^ 2 *
          ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2
          ≤ 4 * A ^ 2 * (1 / (1 + (j.natAbs : ℝ)) ^ 2)
            + 8 * K * A ^ 2 / ((I : ℝ) * ((((I : ℤ) + j).natAbs : ℕ) : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left hdef hamp
        refine hmul.trans ?_
        rcases Nat.eq_zero_or_pos ((I : ℤ) + j).natAbs with h0 | hpos
        · rw [h0]
          refine le_of_eq ?_
          simp only [Nat.cast_zero, div_zero, mul_zero, add_zero]
          rw [div_pow]
          field_simp
          try ring
        · have hposR : (0 : ℝ) < ((((I : ℤ) + j).natAbs : ℕ) : ℝ) := by exact_mod_cast hpos
          have hIR : (0 : ℝ) < (I : ℝ) := by exact_mod_cast hIpos
          have hkey : (A / (1 + (j.natAbs : ℝ))) ^ 2 *
              (2 * K * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℕ) : ℝ))
              ≤ 8 * K * A ^ 2 / ((I : ℝ) * ((((I : ℤ) + j).natAbs : ℕ) : ℝ)) := by
            rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
            have hsq : (I : ℝ) ^ 2 ≤ 4 * (1 + (j.natAbs : ℝ)) ^ 2 := by nlinarith
            have hc : (0 : ℝ) ≤ 2 * K * A ^ 2 * ((((I : ℤ) + j).natAbs : ℕ) : ℝ) := by
              positivity
            nlinarith [hsq, hc]
          have hfirst : (A / (1 + (j.natAbs : ℝ))) ^ 2 * 4
              = 4 * A ^ 2 * (1 / (1 + (j.natAbs : ℝ)) ^ 2) := by
            rw [div_pow]
            field_simp
          calc (A / (1 + (j.natAbs : ℝ))) ^ 2 *
                (4 + 2 * K * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℕ) : ℝ))
              = (A / (1 + (j.natAbs : ℝ))) ^ 2 * 4
                + (A / (1 + (j.natAbs : ℝ))) ^ 2 *
                  (2 * K * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℕ) : ℝ)) := by ring
            _ ≤ 4 * A ^ 2 * (1 / (1 + (j.natAbs : ℝ)) ^ 2)
                + 8 * K * A ^ 2 / ((I : ℝ) * ((((I : ℤ) + j).natAbs : ℕ) : ℝ)) := by
                rw [hfirst]
                linarith [hkey]
      calc ENNReal.ofReal ((A / (1 + (j.natAbs : ℝ))) ^ 2 *
            ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2)
          ≤ ENNReal.ofReal (4 * A ^ 2 * (1 / (1 + (j.natAbs : ℝ)) ^ 2)
              + 8 * K * A ^ 2 / ((I : ℝ) * ((((I : ℤ) + j).natAbs : ℕ) : ℝ))) :=
            ENNReal.ofReal_le_ofReal hstep
        _ = T1 j + T3 j := by
            rw [hT1, hT3]
            simp only [if_pos hj, if_pos hspike]
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ T1 j + T2 j + T3 j := by
            rw [add_assoc, add_comm (T2 j) (T3 j), ← add_assoc]
            exact le_add_right le_rfl
  refine le_trans (ENNReal.tsum_le_tsum hpoint) ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_add]
  -- the three bands
  have hb1 : ∑' j : ℤ, T1 j ≤ ENNReal.ofReal (4 * A ^ 2) * ENNReal.ofReal (4 / (1 + (J : ℝ))) := by
    have hmove : ∀ j : ℤ, T1 j = ENNReal.ofReal (4 * A ^ 2) *
        (if J < j.natAbs then ENNReal.ofReal (1 / (1 + (j.natAbs : ℝ)) ^ 2) else 0) := by
      intro j
      simp only [hT1]
      by_cases h : J < j.natAbs
      · rw [if_pos h, if_pos h, ← ENNReal.ofReal_mul (by positivity)]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [tsum_congr hmove, ENNReal.tsum_mul_left]
    exact mul_le_mul_right (tsum_int_tail_inv_one_add_sq_le J) _
  have hb2 : ∑' j : ℤ, T2 j
      ≤ ENNReal.ofReal (4 * K * A ^ 2) * ENNReal.ofReal (4 / (1 + (J : ℝ))) := by
    have hmove : ∀ j : ℤ, T2 j = ENNReal.ofReal (4 * K * A ^ 2) *
        (if J < j.natAbs then ENNReal.ofReal (1 / (1 + (j.natAbs : ℝ)) ^ 2) else 0) := by
      intro j
      simp only [hT2]
      by_cases h : J < j.natAbs
      · rw [if_pos h, if_pos h, ← ENNReal.ofReal_mul (by positivity)]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [tsum_congr hmove, ENNReal.tsum_mul_left]
    exact mul_le_mul_right (tsum_int_tail_inv_one_add_sq_le J) _
  have hb3 : ∑' j : ℤ, T3 j
      ≤ ENNReal.ofReal (8 * K * A ^ 2 / (I : ℝ)) *
        ENNReal.ofReal (2 * (1 + Real.log (I : ℝ))) := by
    have hre : ∑' j : ℤ, T3 j = ∑' r : ℤ, T3 (r - (I : ℤ)) :=
      (Equiv.tsum_eq (Equiv.subRight ((I : ℤ))) T3).symm
    rw [hre]
    have hmove : ∀ r : ℤ, T3 (r - (I : ℤ)) ≤ ENNReal.ofReal (8 * K * A ^ 2 / (I : ℝ)) *
        (if 0 < r.natAbs ∧ r.natAbs < I then
          ENNReal.ofReal (1 / ((r.natAbs : ℕ) : ℝ)) else 0) := by
      intro r
      have hidx : ((I : ℤ) + (r - (I : ℤ))) = r := by ring
      simp only [hT3, hidx]
      by_cases hsp : 2 * r.natAbs < I
      swap
      · rw [if_neg hsp]
        exact _root_.zero_le
      rw [if_pos hsp]
      rcases eq_or_ne r 0 with hr0 | hr0
      · rw [hr0]
        simp
      · have hrpos : 0 < r.natAbs := by omega
        have hrlt : r.natAbs < I := by omega
        rw [if_pos ⟨hrpos, hrlt⟩, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [div_mul_eq_mul_div, mul_one_div, div_div]
        ring
    refine le_trans (ENNReal.tsum_le_tsum hmove) ?_
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul_right (tsum_int_punctured_band_inv_le I) _
  refine le_trans (add_le_add (add_le_add hb1 hb2) hb3) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hJ : (0 : ℝ) < 1 + (J : ℝ) := by positivity
  rcases Nat.eq_zero_or_pos I with hI0 | hIpos
  · subst hI0
    simp only [Nat.cast_zero, div_zero]
    have h1 : 4 * A ^ 2 * (4 / (1 + (J : ℝ))) + 4 * K * A ^ 2 * (4 / (1 + (J : ℝ)))
        = 16 * A ^ 2 * (1 + K) / (1 + (J : ℝ)) := by
      field_simp
      ring
    rw [h1]
    simp
  · have hIR : (0 : ℝ) < (I : ℝ) := by exact_mod_cast hIpos
    have h1 : 4 * A ^ 2 * (4 / (1 + (J : ℝ))) + 4 * K * A ^ 2 * (4 / (1 + (J : ℝ)))
        = 16 * A ^ 2 * (1 + K) / (1 + (J : ℝ)) := by
      field_simp
      ring
    have h2 : 8 * K * A ^ 2 / (I : ℝ) * (2 * (1 + Real.log (I : ℝ)))
        = 16 * K * A ^ 2 * (1 + Real.log (I : ℝ)) / (I : ℝ) := by
      field_simp
      ring
    rw [h1, h2]

end

end RHTower
