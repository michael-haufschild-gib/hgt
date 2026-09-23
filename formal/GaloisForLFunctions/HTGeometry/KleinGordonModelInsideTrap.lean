import GaloisForLFunctions.HTGeometry.KleinGordonBandFrequencySpread

/-!
# The model sits inside the trapping band

The explicit excursion of a diagonal clock is at most `c² + b ≤ 1 + 2b`, and the general trapping band
of the card is `(1+b)/(1−b)`. The first is smaller than the second, by exactly `2b²/(1−b)`, so the
model respects the general law — and the two agree to first order in the strength of the potential.

Deriving the general bound from the explicit formula is a check on both.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section InsideTrap

variable {b c : ℝ}

/-- **The explicit excursion factor lies inside the trapping band.** -/
theorem excursion_le_trap_band (hb0 : 0 ≤ b) (hb1 : b < 1) (hcb : c ^ (2 : ℕ) ≤ 1 + b) :
    c ^ (2 : ℕ) + b ≤ (1 + b) / (1 - b) := by
  have hpos : (0 : ℝ) < 1 - b := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [sq_nonneg b]

/-- The gap between the two is second order in the strength of the potential. -/
theorem trap_band_sub_excursion (hb1 : b < 1) :
    (1 + b) / (1 - b) - (1 + 2 * b) = 2 * b ^ (2 : ℕ) / (1 - b) := by
  have hne : (1 : ℝ) - b ≠ 0 := by
    intro h
    exact absurd (by linarith : b = 1) (ne_of_lt hb1)
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- **The explicit energy of the model obeys the general trapping bound.** -/
theorem kgFieldEnergyT_kgTunedPot_real_le_trap (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t‖ ^ (2 : ℕ)
      ≤ (1 + b) / (1 - b) * ‖kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) := by
  obtain ⟨hspreadLow, hspreadHigh⟩ :=
    kgFieldEnergyT_kgTunedPot_real_spread (E := E) hb0 hc1 x
  obtain ⟨_, hupper⟩ :=
    kgFieldEnergyT_kgTunedPot_real_between hb0 hb1 hc0 hc1 hcb x t
  have hband := excursion_le_trap_band (c := c) hb0 hb1 hcb
  have hcb0 : (0 : ℝ) ≤ c ^ (2 : ℕ) + b := by nlinarith
  have hA0 : (0 : ℝ) ≤ ‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) := sq_nonneg _
  have hmax : max (‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
      (c ^ (2 : ℕ) * ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
      ≤ (c ^ (2 : ℕ) + b) * ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) := by
    refine max_le hspreadHigh ?_
    nlinarith [sq_nonneg ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖]
  have hstep : (c ^ (2 : ℕ) + b) * ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)
      ≤ (c ^ (2 : ℕ) + b) * ‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hspreadLow hcb0
  have hfinal : (c ^ (2 : ℕ) + b) * ‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)
      ≤ (1 + b) / (1 - b) * ‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_right hband hA0
  linarith

end InsideTrap

end GaloisForLFunctions.HTGeometry
