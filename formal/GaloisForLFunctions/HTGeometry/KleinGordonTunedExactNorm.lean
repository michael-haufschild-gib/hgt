import GaloisForLFunctions.HTGeometry.KleinGordonTunedFlatEnvelope

/-!
# The tuned eigen-clock conserves its energy at every instant

The general theory gives an eigen-clock a flat envelope — two positive constants between which its
state norm is confined — and exact conservation at multiples of a period. The tuned clock started from
the complex datum does better: its state is multiplied by a unit-modulus phase, so its norm is
constant and its energy is conserved at **every** instant, not only stroboscopically.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section ExactNorm

variable {b c : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The state norm of the tuned eigen-clock is constant in time.** -/
theorem norm_kgFieldStateT_kgTunedPot_circle (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldStateT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
          (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
        (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
        (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x)) t‖
      = ‖kgPair E (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x,
          kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x))‖ := by
  rw [kgFieldStateT_kgTunedPot_circle hb0 hb1 hc0 hc1 hcb x t, norm_smul,
    norm_kgTunedPhase, one_mul]

set_option maxHeartbeats 1000000 in
/-- **The tuned eigen-clock conserves its energy at every instant.** -/
theorem kgFieldEnergyT_kgTunedPot_circle (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
          (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x)) t‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (kgBandOpT (fun _ : ℝ => fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
            (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
          (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x)) t‖ ^ (2 : ℕ)
      = ‖kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)
        + ‖kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x)‖ ^ (2 : ℕ) := by
  rw [kgFieldEnergyT_eq_norm_sq, norm_kgFieldStateT_kgTunedPot_circle hb0 hb1 hc0 hc1 hcb x t,
    norm_kgPair_sq]

end ExactNorm

end GaloisForLFunctions.HTGeometry
