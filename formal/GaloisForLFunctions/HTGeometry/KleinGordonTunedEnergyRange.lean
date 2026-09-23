import GaloisForLFunctions.HTGeometry.KleinGordonTunedRealDatum

/-!
# The exact range of the oscillating energy

The energy of the tuned clock started from a real datum is a convex combination of its two extreme
values, with weights `cos²(ct)` and `sin²(ct)`. So it never leaves the interval between them, and it
reaches both ends: the gradient value at `t = 0`, the velocity value a quarter period later.

`E(0) = ‖⟨D⟩_R x‖²`,   `E(π/2c) = c²‖P_R x‖²`,   `min ≤ E(t) ≤ max`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section EnergyRange

variable {b c : ℝ}

set_option maxHeartbeats 1000000 in
/-- **At time zero the energy is carried entirely by the gradient.** -/
theorem kgFieldEnergyT_kgTunedPot_real_zero (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 0‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 0‖ ^ (2 : ℕ)
      = ‖kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) := by
  rw [kgFieldEnergyT_kgTunedPot_real hb0 hb1 hc0 hc1 hcb x 0]
  simp

set_option maxHeartbeats 1000000 in
/-- **A quarter period later it is carried entirely by the velocity.** -/
theorem kgFieldEnergyT_kgTunedPot_real_quarter (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 (Real.pi / (2 * c))‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 (Real.pi / (2 * c))‖ ^ (2 : ℕ)
      = c ^ (2 : ℕ) * ‖kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) := by
  have harg : Real.pi / (2 * c) * c = Real.pi / 2 := by
    field_simp
  rw [kgFieldEnergyT_kgTunedPot_real hb0 hb1 hc0 hc1 hcb x (Real.pi / (2 * c)), harg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

set_option maxHeartbeats 1000000 in
/-- **The energy never leaves the interval between its two extreme values.** -/
theorem kgFieldEnergyT_kgTunedPot_real_between (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    min (‖kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
        (c ^ (2 : ℕ) * ‖kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
        ≤ ‖kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
              (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
              (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
              (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
            (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t‖ ^ (2 : ℕ)
          + ‖kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
              (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
              (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
              (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
            (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t‖ ^ (2 : ℕ)
      ∧ ‖kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
              (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
              (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
              (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
            (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t‖ ^ (2 : ℕ)
          + ‖kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
              (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
              (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
              (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
            (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x) 0 t‖ ^ (2 : ℕ)
        ≤ max (‖kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
            (c ^ (2 : ℕ) * ‖kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)) := by
  have hpyth : Real.cos (t * c) ^ (2 : ℕ) + Real.sin (t * c) ^ (2 : ℕ) = 1 :=
    Real.cos_sq_add_sin_sq _
  have hcos0 : (0 : ℝ) ≤ Real.cos (t * c) ^ (2 : ℕ) := sq_nonneg _
  have hsin0 : (0 : ℝ) ≤ Real.sin (t * c) ^ (2 : ℕ) := sq_nonneg _
  have hcsq : (c * Real.sin (t * c)) ^ (2 : ℕ)
      = c ^ (2 : ℕ) * Real.sin (t * c) ^ (2 : ℕ) := by ring
  rw [kgFieldEnergyT_kgTunedPot_real hb0 hb1 hc0 hc1 hcb x t, hcsq]
  constructor
  · have h1 := min_le_left (‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
      (c ^ (2 : ℕ) * ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
    have h2 := min_le_right (‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
      (c ^ (2 : ℕ) * ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
    nlinarith [hcos0, hsin0, hpyth]
  · have h1 := le_max_left (‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
      (c ^ (2 : ℕ) * ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
    have h2 := le_max_right (‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
      (c ^ (2 : ℕ) * ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ))
    nlinarith [hcos0, hsin0, hpyth]

end EnergyRange

end GaloisForLFunctions.HTGeometry
