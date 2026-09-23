import GaloisForLFunctions.HTGeometry.KleinGordonTunedCircleData

/-!
# Every point of the unit circle is an attained multiplier

Started from the complex datum `(Px, −icPx)` the tuned clock multiplies its whole state by the phase
`e^{−ict}`. At an arbitrary period `T` this says the monodromy has the eigenvector

`M v = e^{−icT} · v`,   `‖e^{−icT}‖ = 1`.

Statement 440 forces every attained multiplier of a weak static real potential onto the unit circle;
this shows the constraint is exactly sharp, since `cT` runs over all of `ℝ`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section CircleMultiplier

variable {b c : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The state of the tuned clock started from the complex datum rotates by a phase.** -/
theorem kgFieldStateT_kgTunedPot_circle (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
    (hc1 : 1 ≤ c ^ (2 : ℕ)) (hcb : c ^ (2 : ℕ) ≤ 1 + b) (x : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    kgFieldStateT (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
          (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
        (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
        (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x)) T
      = kgTunedPhase c T • kgPair E (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x,
          kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x)) := by
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
  have hsmulP : kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b))
        ((-(Complex.I * (c : ℂ))) • x)
      = (-(Complex.I * (c : ℂ))) • kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x := map_smul _ _ _
  -- the field
  have hmild := kgFieldMildT_eq_kgShiftedField (measurable_kgTunedPot (E := E) b c) hb0 hb1
    (abs_kgTunedPot_le hb0 hc1 hcb) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x
    ((-(Complex.I * (c : ℂ))) • x) T
  rw [kgShiftedField_kgTunedPot_circle hc0 hc1] at hmild
  have hgradinv := kgFreqInvOp_kgFieldGradT hb0 hBandb hBands
    (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
    (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x)) T
  have hgrad : kgFieldGradT (kgBandOpT (fun _ : ℝ => fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
        (Real.sqrt (c ^ (2 : ℕ) - 1 + b)))
      (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x)
      (kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x)) T
      = kgTunedPhase c T • kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x := by
    refine kgFreqInvOp_injective ?_
    rw [hgradinv, hmild, map_smul, kgFreqInvOp_kgFreqLowOp]
  -- the velocity
  have hvel := kgFieldVelT_eq_kgShiftedVel (measurable_kgTunedPot (E := E) b c) hb0 hb1
    (abs_kgTunedPot_le hb0 hc1 hcb) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x
    ((-(Complex.I * (c : ℂ))) • x) T
  rw [kgShiftedVel_kgTunedPot_circle hb0 hb1 hc0 hc1 hcb, ← hsmulP] at hvel
  rw [kgFieldStateT, hgrad, hvel]
  exact map_smul (kgPair E) (kgTunedPhase c T)
    (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x,
      kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x))

set_option maxHeartbeats 1000000 in
/-- **Every point of the unit circle is an attained Floquet multiplier.** -/
theorem kgMonodromy_kgTunedPot_circle_eigen (hb0 : 0 ≤ b) (hb1 : b < 1) (hc0 : 0 < c)
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
    (x : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    kgMonodromy (kgBandOpT (fun _ : ℝ => fourierMulCLM
          (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
          (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
          (Real.sqrt (c ^ (2 : ℕ) - 1 + b))) b hb0 hWb hWs T
        (kgPair E (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x,
          kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x)))
      = kgTunedPhase c T • kgPair E (kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x,
          kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) ((-(Complex.I * (c : ℂ))) • x))
      ∧ ‖kgTunedPhase c T‖ = 1 := by
  refine ⟨?_, norm_kgTunedPhase c T⟩
  rw [kgMonodromy_apply, kgPeriodMap_apply]
  simp only [kgPair_fst, kgPair_snd]
  exact kgFieldStateT_kgTunedPot_circle hb0 hb1 hc0 hc1 hcb x T

end CircleMultiplier

end GaloisForLFunctions.HTGeometry
