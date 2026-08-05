import GaloisForLFunctions.HTGeometry.KleinGordonBandResolved

/-!
# No cascade on a finite window, for a moving background

For a moving frequency-diagonal background the high-frequency energy is charged to its own initial
value, but with the exponential factor of the card's inequality rather than a fixed constant. On a
finite window of time that factor is bounded, so the conclusion of the static case survives in
window-limited form:

for every `ε` and every window `[-T, T]` there is a cutoff above which the clock carries less than `ε`
of energy throughout the window.

The dependence is honest: the cutoff grows with the window, because a moving background really can
pump energy upward. What it cannot do is move energy across a band boundary — the growth is always
charged to the energy already present in that band.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section WindowCascade

variable {b : ℝ} {w : ℝ → E → ℂ}

set_option maxHeartbeats 1000000 in
/-- The high-frequency energy of a moving diagonal background is charged to its own initial value. -/
theorem kgFieldEnergyT_high_le (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (R : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ 2
        + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ 2
      ≤ (‖g - kgLowPassOp R g‖ ^ 2 + ‖h - kgLowPassOp R h‖ ^ 2)
          * Real.exp (2 * (b * |t|)) :=
  kgFieldEnergyT_le hb0 (fun _ => norm_fourierMulCLM_le _ _ _) hWs
    (g - kgLowPassOp R g) (h - kgLowPassOp R h) t

set_option maxHeartbeats 1000000 in
/-- **No cascade on a finite window.** For every `ε` and every window `[-T, T]` there is a cutoff
above which the clock carries less than `ε` of energy throughout the window. -/
theorem exists_cutoff_high_energy_small_window (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (g h : Lp ℂ 2 (volume : Measure E)) {ε : ℝ} (hε : 0 < ε) {T : ℝ} :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ t : ℝ, |t| ≤ T →
      ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ 2
        + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ 2 ≤ ε := by
  have hexp : (0 : ℝ) < Real.exp (2 * (b * T)) := Real.exp_pos _
  have hquot : (0 : ℝ) < ε / Real.exp (2 * (b * T)) := div_pos hε hexp
  have hg := tendsto_norm_sub_kgLowPassOp g
  have hh := tendsto_norm_sub_kgLowPassOp h
  have hsum : Tendsto (fun R : ℝ =>
      ‖g - kgLowPassOp R g‖ ^ 2 + ‖h - kgLowPassOp R h‖ ^ 2) atTop (𝓝 0) := by
    have hpow := (hg.pow 2).add (hh.pow 2)
    simpa using hpow
  have hev : ∀ᶠ R : ℝ in atTop,
      ‖g - kgLowPassOp R g‖ ^ 2 + ‖h - kgLowPassOp R h‖ ^ 2
        < ε / Real.exp (2 * (b * T)) := hsum.eventually_lt_const hquot
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hev
  refine ⟨R₀, fun R hR t ht => ?_⟩
  have hs0 : (0 : ℝ) ≤ ‖g - kgLowPassOp R g‖ ^ 2 + ‖h - kgLowPassOp R h‖ ^ 2 := by positivity
  have hmono : Real.exp (2 * (b * |t|)) ≤ Real.exp (2 * (b * T)) := by
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left ht hb0
    linarith
  have hbound := kgFieldEnergyT_high_le hw hb0 hwb hWs R g h t
  have hstep : (‖g - kgLowPassOp R g‖ ^ 2 + ‖h - kgLowPassOp R h‖ ^ 2)
      * Real.exp (2 * (b * |t|))
      ≤ (ε / Real.exp (2 * (b * T))) * Real.exp (2 * (b * T)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hmono hs0) ?_
    exact mul_le_mul_of_nonneg_right (hR₀ R hR).le hexp.le
  have hcancel : (ε / Real.exp (2 * (b * T))) * Real.exp (2 * (b * T)) = ε :=
    div_mul_cancel₀ _ hexp.ne'
  linarith

set_option maxHeartbeats 1000000 in
/-- **On any finite window, all but `ε` of a clock's energy stays below a fixed frequency**, even
when the background moves. -/
theorem kgFieldEnergyT_no_uv_cascade_window (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (g h : Lp ℂ 2 (volume : Measure E)) {ε : ℝ} (hε : 0 < ε) {T : ℝ} :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ t : ℝ, |t| ≤ T →
      ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t‖ ^ 2
            + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t‖ ^ 2
          = (‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
                  (kgLowPassOp R g) (kgLowPassOp R h) t‖ ^ 2
              + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
                  (kgLowPassOp R g) (kgLowPassOp R h) t‖ ^ 2)
            + (‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
                  (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ 2
              + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
                  (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ 2)
        ∧ ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ 2
            + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ 2 ≤ ε := by
  obtain ⟨R₀, hR₀⟩ :=
    exists_cutoff_high_energy_small_window hw hb0 hwb hWs g h hε
  exact ⟨R₀, fun R hR t ht =>
    ⟨kgFieldEnergyT_band_split hw hb0 hwb hWs R g h t, hR₀ R hR t ht⟩⟩

end WindowCascade

end GaloisForLFunctions.HTGeometry
