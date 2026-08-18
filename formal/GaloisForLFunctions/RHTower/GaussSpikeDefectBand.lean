import GaloisForLFunctions.RHTower.GaussSpikeMass
import GaloisForLFunctions.RHTower.GaussShiftRatioWeight
import GaloisForLFunctions.RHTower.GaussRatioWeightedDefect
import GaloisForLFunctions.HTGeometry.IntegerPowerSeriesBounds

/-!
# The spike of the two-piece class is annihilated by the moving-translation defect

The two-piece amplitude class carries, besides its uniform harmonic part, a spike of height `B`
and exponent `c` at the moving frequency `-n`.  Multiplied by the moving-translation defect and
summed, that spike contributes

`B² n^(2c) (2 + 2 (K n)^(1/m)) · ∑_r (1 + |r|)^(-2c)`,

so when the spike height decays like `n^(-θ)` the whole contribution is `O(n^(2c + 1/m - 2θ))`.
The exponent `1/m` — and not the cruder `1/2` — is what makes the arithmetic close: the class the
`m`-fold iteration produces has `c` just below `1 - 1/(2m)`, and `2c + 1/m < 2θ` still holds with
`θ` just below one.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ} {k : Fin m} {p : Nat.Primes}

/-! ## The defect is bounded by the sampled ratio -/

/-- The moving-translation defect is at most the sampled ratio plus one. -/
theorem norm_gaussSampleRatioDefect_le_shiftRatio (k : Fin m) (p : Nat.Primes) (i j : ℤ) :
    ‖gaussSampleRatioDefect k p j i‖ ≤ gaussShiftRatio k p i j + 1 := by
  have h := norm_sub_le (gaussSampleValue k p (i + j) / gaussSampleValue k p i)
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
      ((gaussSamplePhase m p i : ℝ) : ℂ)))
  rw [← gaussSampleRatioDefect, norm_div, norm_gaussSampleRotation (m := m) p j i] at h
  rw [gaussShiftRatio]
  exact h

/-! ## The sharp power of the sampled ratio -/

/-- **The sampled ratio at the sharp exponent.**  Taking the `m`-th root of the uniform bound on
the `2m`-th power gives the square of the ratio directly; no case split and no loss. -/
theorem gaussShiftRatio_sq_le_rpow (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ}
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (l : ℤ) :
    gaussShiftRatio k p (I : ℤ) l ^ 2
      ≤ (K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ)) ^ ((1 : ℝ) / m) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set R : ℝ := gaussShiftRatio k p (I : ℤ) l with hR
  have hR0 : 0 ≤ R := gaussShiftRatio_nonneg k p (I : ℤ) l
  have hbase : R ^ (2 * m) ≤ K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) :=
    norm_gaussSampleRatio_pow_le hm k p hKb I l
  have hid : (R ^ (2 * m)) ^ ((1 : ℝ) / m) = R ^ 2 := by
    rw [← Real.rpow_natCast R (2 * m), ← Real.rpow_mul hR0]
    push_cast
    rw [show (2 : ℝ) * (m : ℝ) * ((1 : ℝ) / (m : ℝ)) = 2 from by field_simp]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  calc R ^ 2 = (R ^ (2 * m)) ^ ((1 : ℝ) / m) := hid.symm
    _ ≤ (K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ)) ^ ((1 : ℝ) / m) :=
        Real.rpow_le_rpow (pow_nonneg hR0 _) hbase (by positivity)

/-- **The squared defect at the sharp exponent.** -/
theorem norm_gaussSampleRatioDefect_sq_le_rpow (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ}
    (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (l : ℤ) :
    ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2 ≤ 2 + 2 * (K * (I : ℝ)) ^ ((1 : ℝ) / m) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp : (0 : ℝ) < (1 : ℝ) / m := by positivity
  set R : ℝ := gaussShiftRatio k p (I : ℤ) l with hR
  have hR0 : 0 ≤ R := gaussShiftRatio_nonneg k p (I : ℤ) l
  have hD : ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ≤ R + 1 :=
    norm_gaussSampleRatioDefect_le_shiftRatio k p (I : ℤ) l
  have hD0 : (0 : ℝ) ≤ ‖gaussSampleRatioDefect k p l (I : ℤ)‖ := norm_nonneg _
  have hRsq : R ^ 2 ≤ (K * (I : ℝ)) ^ ((1 : ℝ) / m) := by
    refine le_trans (gaussShiftRatio_sq_le_rpow hm k p hKb I l) ?_
    rcases Nat.eq_zero_or_pos ((I : ℤ) + l).natAbs with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, div_zero]
      rw [Real.zero_rpow (ne_of_gt hexp)]
      positivity
    · have hposR : (1 : ℝ) ≤ ((((I : ℤ) + l).natAbs : ℕ) : ℝ) := by exact_mod_cast hpos
      have hKI : (0 : ℝ) ≤ K * (I : ℝ) := by positivity
      have hdiv : K * (I : ℝ) / ((((I : ℤ) + l).natAbs : ℕ) : ℝ) ≤ K * (I : ℝ) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      exact Real.rpow_le_rpow (by positivity) hdiv hexp.le
  nlinarith [sq_nonneg (R - 1), hD, hD0, hR0]

/-! ## The band sum -/

/-- **The spike contribution to the moving-translation defect.** -/
theorem tsum_spikeProfile_sq_mul_defect_sq_le (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {B c : ℝ} (hB : 0 ≤ B) (hc : 1 < 2 * c) (I : ℕ) :
    ∑' l : ℤ, ENNReal.ofReal
        (spikeProfile B c I l ^ 2 * ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2)
      ≤ ENNReal.ofReal (B ^ 2 * (I : ℝ) ^ (2 * c) * (2 + 2 * (K * (I : ℝ)) ^ ((1 : ℝ) / m)) *
          (∑' r : ℤ, intPowWeight (2 * c) r).toReal) := by
  classical
  have hc0 : (0 : ℝ) < c := by linarith
  set M : ℝ := B ^ 2 * (I : ℝ) ^ (2 * c) * (2 + 2 * (K * (I : ℝ)) ^ ((1 : ℝ) / m)) with hM
  have hM0 : 0 ≤ M := by
    have : (0 : ℝ) ≤ (K * (I : ℝ)) ^ ((1 : ℝ) / m) := Real.rpow_nonneg (by positivity) _
    rw [hM]
    positivity
  -- pointwise domination by the shifted power weight
  have hpoint : ∀ l : ℤ,
      ENNReal.ofReal (spikeProfile B c I l ^ 2 * ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2)
        ≤ ENNReal.ofReal M * intPowWeight (2 * c) ((I : ℤ) + l) := by
    intro l
    have hnat : |(((I : ℤ) + l : ℤ) : ℝ)| = ((((I : ℤ) + l).natAbs : ℕ) : ℝ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have hden : (0 : ℝ) < 1 + ((((I : ℤ) + l).natAbs : ℕ) : ℝ) := by positivity
    have hweight : intPowWeight (2 * c) ((I : ℤ) + l)
        = ENNReal.ofReal (1 / (1 + ((((I : ℤ) + l).natAbs : ℕ) : ℝ)) ^ (2 * c)) := by
      rw [intPowWeight, hnat]
    have hDsq := norm_gaussSampleRatioDefect_sq_le_rpow hm k p hK hKb I l
    have hspike : spikeProfile B c I l ^ 2
        ≤ B ^ 2 * (I : ℝ) ^ (2 * c) / (1 + ((((I : ℤ) + l).natAbs : ℕ) : ℝ)) ^ (2 * c) := by
      rw [spikeProfile]
      split_ifs with hband
      · rw [mul_pow, ← Real.rpow_natCast (((I : ℝ) / (1 + ((((I : ℤ) + l).natAbs : ℕ) : ℝ))) ^ c) 2,
          ← Real.rpow_mul (by positivity)]
        rw [show c * ((2 : ℕ) : ℝ) = 2 * c from by push_cast; ring]
        rw [Real.div_rpow (by positivity) hden.le]
        rw [mul_div_assoc]
      · have : (0 : ℝ) ≤ B ^ 2 * (I : ℝ) ^ (2 * c) /
            (1 + ((((I : ℤ) + l).natAbs : ℕ) : ℝ)) ^ (2 * c) := by positivity
        simpa using this
    have hprod : spikeProfile B c I l ^ 2 * ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2
        ≤ M * (1 / (1 + ((((I : ℤ) + l).natAbs : ℕ) : ℝ)) ^ (2 * c)) := by
      have h1 : (0 : ℝ) ≤ spikeProfile B c I l ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2 := by positivity
      have hpow0 : (0 : ℝ) < (1 + ((((I : ℤ) + l).natAbs : ℕ) : ℝ)) ^ (2 * c) := by positivity
      have hcalc := mul_le_mul hspike hDsq h2 (by positivity)
      refine le_trans hcalc (le_of_eq ?_)
      rw [hM]
      field_simp
    rw [hweight, ← ENNReal.ofReal_mul hM0]
    exact ENNReal.ofReal_le_ofReal hprod
  refine le_trans (ENNReal.tsum_le_tsum hpoint) ?_
  rw [ENNReal.tsum_mul_left]
  have hshift : ∑' l : ℤ, intPowWeight (2 * c) ((I : ℤ) + l)
      = ∑' r : ℤ, intPowWeight (2 * c) r :=
    Equiv.tsum_eq (Equiv.addLeft ((I : ℤ))) (intPowWeight (2 * c))
  rw [hshift]
  have hfin : (∑' r : ℤ, intPowWeight (2 * c) r) ≠ ⊤ := tsum_intPowWeight_ne_top hc
  rw [ENNReal.ofReal_mul hM0, ENNReal.ofReal_toReal hfin]

end

end RHTower
