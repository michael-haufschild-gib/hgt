import GaloisForLFunctions.HTGeometry.KleinGordonModelInsideTrap

/-!
# The lower half of the trap, from the model

The explicit energy of a diagonal clock is bounded below by the projection norm, which the frequency
spread bounds below by `E(0)/(c² + b)`. Since `c² + b ≤ (1+b)/(1−b)`, the model reproduces the lower
half of the trapping law as well:

`E(0)·(1−b)/(1+b) ≤ E(t) ≤ E(0)·(1+b)/(1−b)`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TrapLower

variable {b c : ℝ}

/-- The trapping comparison in cleared form. -/
theorem excursion_mul_le (hb0 : 0 ≤ b) (hcb : c ^ (2 : ℕ) ≤ 1 + b) :
    (c ^ (2 : ℕ) + b) * (1 - b) ≤ 1 + b := by
  nlinarith [sq_nonneg b]

set_option maxHeartbeats 1000000 in
/-- **The explicit energy of the model obeys the lower trapping bound.** -/
theorem kgFieldEnergyT_kgTunedPot_real_ge_trap (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    (1 - b) / (1 + b) * ‖kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)
      ≤ ‖kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t‖ ^ (2 : ℕ) := by
  have hbpos : (0 : ℝ) < 1 + b := by linarith
  have hbneg : (0 : ℝ) < 1 - b := by linarith
  obtain ⟨hspreadLow, hspreadHigh⟩ :=
    kgFieldEnergyT_kgTunedPot_real_spread (E := E) hb0 hc1 x
  obtain ⟨hlower, _⟩ :=
    kgFieldEnergyT_kgTunedPot_real_between hb0 hb1 hc0 hc1 hcb x t
  have hP20 : (0 : ℝ) ≤ ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) := sq_nonneg _
  have hmin : ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)
      ≤ min (‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
        (c ^ (2 : ℕ) * ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)) := by
    refine le_min hspreadLow ?_
    nlinarith [hP20]
  have hcleared := excursion_mul_le (c := c) hb0 hcb
  have hstep : (1 - b) / (1 + b) * ‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)
      ≤ ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hbpos]
    nlinarith [hspreadHigh, hcleared, hP20, hbneg]
  linarith

end TrapLower

end GaloisForLFunctions.HTGeometry
