import GaloisForLFunctions.HTGeometry.KleinGordonTunedUnitModulus

/-!
# The flat envelope, checked against the tuned clock

The general theory shows that an eigen-clock in a weak static real potential has a *flat* two-sided
envelope: its state norm is confined between two positive constants for all time, because the Floquet
exponent vanishes when the multiplier lies on the unit circle.

The tuned clock exhibits this directly — its state is multiplied by a phase, so its norm is constant.
Applying the general theorem to it produces the envelope from the spectral side.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TunedEnvelope

variable {b c : ℝ}

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The phase of the tuned clock is an exponential with imaginary exponent. -/
theorem kgTunedPhase_eq_exp (c t : ℝ) :
    kgTunedPhase c t = Complex.exp ((-(Complex.I * (c : ℂ))) * (t : ℂ)) := by
  rw [show (-(Complex.I * (c : ℂ))) * (t : ℂ) = ((-(t * c) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_mul_I, kgTunedPhase, Complex.ofReal_cos, Complex.ofReal_sin]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

set_option maxHeartbeats 1000000 in
/-- **The flat envelope applied to the tuned clock.** -/
theorem exists_tuned_clock_flat_envelope [Nontrivial E] (hbpos : 0 < b) (hb1 : b < 1)
    (hc0 : 0 < c) (hc1 : 1 ≤ c ^ 2) (hcb : c ^ 2 ≤ 1 + b) {T : ℝ} (hT : 0 < T) :
    ∃ z : Lp ℂ 2 (volume : Measure E), ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧ ∀ t : ℝ,
      m ≤ ‖kgFieldStateT (fun _ : ℝ => kgBandOp (fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hbpos.le
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hbpos.le hc1 hcb)))
            (Real.sqrt (c ^ 2 - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ 2 - 1 + b)) z)
          (kgLowPassOp (Real.sqrt (c ^ 2 - 1 + b)) ((-(Complex.I * (c : ℂ))) • z)) t‖
        ∧ ‖kgFieldStateT (fun _ : ℝ => kgBandOp (fourierMulCLM
            (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hbpos.le
            (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hbpos.le hc1 hcb)))
            (Real.sqrt (c ^ 2 - 1 + b)))
          (kgFreqLowOp (Real.sqrt (c ^ 2 - 1 + b)) z)
          (kgLowPassOp (Real.sqrt (c ^ 2 - 1 + b)) ((-(Complex.I * (c : ℂ))) • z)) t‖ ≤ M := by
  have hb0 : (0 : ℝ) ≤ b := hbpos.le
  have hRpos : 0 < Real.sqrt (c ^ 2 - 1 + b) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨z, hzne, hzfix⟩ := exists_ne_zero_kgLowPassOp_fixed (E := E) hRpos
  have hne : kgPair E (kgFreqLowOp (Real.sqrt (c ^ 2 - 1 + b)) z,
      kgLowPassOp (Real.sqrt (c ^ 2 - 1 + b)) ((-(Complex.I * (c : ℂ))) • z)) ≠ 0 :=
    kgPair_ne_zero_of_fst (kgFreqLowOp_ne_zero_of_fixed hzne hzfix)
  refine ⟨z, ?_⟩
  have hMp : ‖fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
      (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb))‖ ≤ b :=
    norm_fourierMulCLM_le _ _ _
  have hW : ‖kgBandOp (fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
      (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
      (Real.sqrt (c ^ 2 - 1 + b))‖ ≤ b := norm_kgBandOp_le hb0 hMp _
  have hsa : ∀ u v : Lp ℂ 2 (volume : Measure E),
      (inner ℂ (kgBandOp (fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
        (Real.sqrt (c ^ 2 - 1 + b)) u) v : ℂ)
      = inner ℂ u (kgBandOp (fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
        (Real.sqrt (c ^ 2 - 1 + b)) v) :=
    kgBandOp_inner (fourierMulCLM_inner _ _ _
      (starRingEnd_kgRealPotSymbol (kgTunedPot b c))) _
  have hWb : ∀ r : ℝ, ‖(fun _ : ℝ => kgBandOp (fourierMulCLM (E := E)
      (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
      (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
      (Real.sqrt (c ^ 2 - 1 + b))) r‖ ≤ b := fun _ => hW
  have hWs : ∀ u : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ =>
      (fun _ : ℝ => kgBandOp (fourierMulCLM
        (measurable_kgRealPotSymbol (measurable_kgTunedPot (E := E) b c)) hb0
        (norm_kgRealPotSymbol_le (abs_kgTunedPot_le hb0 hc1 hcb)))
        (Real.sqrt (c ^ 2 - 1 + b))) r u := fun _ => continuous_const
  obtain ⟨heig, _⟩ :=
    kgMonodromy_kgTunedPot_circle_eigen (E := E) hb0 hb1 hc0 hc1 hcb hWb hWs z T
  exact exists_flat_envelope_of_small_potential hb0 hb1 hW hsa hWb hWs hT
    (kgTunedPhase_eq_exp c T).symm
    (kgFreqLowOp (Real.sqrt (c ^ 2 - 1 + b)) z)
    (kgLowPassOp (Real.sqrt (c ^ 2 - 1 + b)) ((-(Complex.I * (c : ℂ))) • z)) hne heig

end TunedEnvelope

end GaloisForLFunctions.HTGeometry
