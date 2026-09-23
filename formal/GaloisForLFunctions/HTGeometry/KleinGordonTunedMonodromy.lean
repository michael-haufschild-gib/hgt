import GaloisForLFunctions.HTGeometry.KleinGordonTunedVelocity

/-!
# The monodromy of the tuned clock

At the period `2π/c` both the field and the velocity of the tuned clock return to their initial
values, so the monodromy at that period fixes every state carried by the band:

`M v = 1 · v`.

Each admissible rate `c` therefore contributes its own periodic clock, and the Floquet eigen-class is
inhabited at every period in `[2π/√(1+b), 2π]`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TunedMonodromy

variable {b c : ℝ}

set_option maxHeartbeats 1000000 in
/-- The velocity of the tuned clock returns after one period. -/
theorem kgShiftedVel_kgTunedPot_period (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x y : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedVel (measurable_kgTunedPot (E := E) b c) hb0 hb1
        (abs_kgTunedPot_le hb0 hc1 hcb) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x y (2 * Real.pi / c)
      = kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) y := by
  have harg : 2 * Real.pi / c * c = 2 * Real.pi := by
    field_simp
  rw [kgShiftedVel_kgTunedPot hb0 hb1 hc0 hc1 hcb, harg, Real.cos_two_pi, Real.sin_two_pi]
  simp

set_option maxHeartbeats 1000000 in
/-- **The state of the tuned clock returns after one period.** -/
theorem kgFieldStateT_kgTunedPot_period (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x y : Lp ℂ 2 (volume : Measure E)) :
    kgFieldStateT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
          (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
        (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
        (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) y) (2 * Real.pi / c)
      = kgPair E (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x,
          kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) y) := by
  have hWb : ∀ r : ℝ, ‖(fun _ : ℝ => fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
      (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))) r‖ ≤ b :=
    fun _ => norm_fourierMulCLM_le _ _ _
  have hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ =>
      (fun _ : ℝ => fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))) r z := fun _ => continuous_const
  have hBandb := norm_kgBandOpT_le hb0 hWb (Real.sqrt (c ^ (2 : ℕ) - 1 + b))
  have hBands := continuous_kgBandOpT_apply hWs (Real.sqrt (c ^ (2 : ℕ) - 1 + b))
  have hmild := kgFieldMildT_eq_kgShiftedField (measurable_kgTunedPot (E := E) b c) hb0 hb1
    (abs_kgTunedPot_le hb0 hc1 hcb) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x y (2 * Real.pi / c)
  rw [kgShiftedField_kgTunedPot_period hc0 hc1] at hmild
  have hgradinv := kgFreqInvOp_kgFieldGradT hb0 hBandb hBands
    (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
    (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) y) (2 * Real.pi / c)
  have hgrad : kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
        (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
      (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
      (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) y) (2 * Real.pi / c)
      = kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x := by
    refine kgFreqInvOp_injective ?_
    rw [hgradinv, hmild, kgFreqInvOp_kgFreqLowOp]
  have hvel := kgFieldVelT_eq_kgShiftedVel (measurable_kgTunedPot (E := E) b c) hb0 hb1
    (abs_kgTunedPot_le hb0 hc1 hcb) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x y (2 * Real.pi / c)
  rw [kgShiftedVel_kgTunedPot_period hb0 hb1 hc0 hc1 hcb] at hvel
  rw [kgFieldStateT, hgrad, hvel]

set_option maxHeartbeats 1000000 in
/-- **The tuned clock is a Floquet eigen-solution with multiplier one at its own period.** -/
theorem kgMonodromy_kgTunedPot_eigen (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b)
    (hWb : ∀ r : ℝ, ‖kgBandOpT (fun _ : ℝ => fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
        (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ =>
      kgBandOpT (fun _ : ℝ => fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
        (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) r z)
    (x y : Lp ℂ 2 (volume : Measure E)) :
    kgMonodromy (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
          (Real.sqrt (c ^ (2 : ℕ) - 1 + b))) b hb0 hWb hWs (2 * Real.pi / c)
        (kgPair E (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x,
          kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) y))
      = (1 : ℂ) • kgPair E (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x,
          kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) y) := by
  rw [kgMonodromy_apply, kgPeriodMap_apply, one_smul]
  simp only [kgPair_fst, kgPair_snd]
  exact kgFieldStateT_kgTunedPot_period hb0 hb1 hc0 hc1 hcb x y

end TunedMonodromy

end GaloisForLFunctions.HTGeometry
