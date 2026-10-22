import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHasseHilbertAdmission

/-! # Continuity in the original Meyer source topology

The full Hasse Hilbert map is controlled by finitely many of the original
weighted derivative gauges. Its continuity therefore descends through the
literal Poisson quotient; no weaker coordinate topology is substituted.
-/

noncomputable section
open Complex Filter MeasureTheory Set Topology

namespace RHTower
open scoped DeningerMeyerNaturalTopology

private def hasseMassGauge (g : DeningerMeyerStrongLogTarget) : ℝ :=
  ‖deningerMeyerStrongLogGaugeLinear 0 3 g‖ +
    ‖deningerMeyerStrongLogGaugeLinear 0 (-3) g‖

private theorem hasseMassGauge_nonneg (g : DeningerMeyerStrongLogTarget) :
    0 ≤ hasseMassGauge g := add_nonneg (norm_nonneg _) (norm_nonneg _)

private theorem continuous_hasseMassGauge : Continuous hasseMassGauge :=
  (continuous_deningerMeyerStrongLogGaugeLinear 0 3).norm.add
    (continuous_deningerMeyerStrongLogGaugeLinear 0 (-3)).norm

private theorem hasseMassGauge_zero : hasseMassGauge 0 = 0 := by
  simp only [hasseMassGauge, map_zero, norm_zero, add_zero]

private theorem hasse_mass_pointwise (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    Real.exp (2 * |t|) * ‖g.val t‖ ≤ hasseMassGauge g * Real.exp (-|t|) := by
  have hg (k : ℤ) : Real.exp ((k : ℝ)*t) * ‖g.val t‖ ≤
      ‖deningerMeyerStrongLogGaugeLinear 0 k g‖ := by
    have h := (deningerMeyerStrongLogGauge 0 k g).norm_coe_le_norm t
    rw [deningerMeyerStrongLogGauge_apply, iteratedDeriv_zero, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) (k : ℝ)), ← Real.exp_mul] at h
    simpa only [mul_comm t, deningerMeyerStrongLogGaugeLinear_apply] using h
  by_cases ht : 0 ≤ t
  · have hb : Real.exp (3*t) * ‖g.val t‖ ≤ hasseMassGauge g :=
      (hg 3).trans (le_add_of_nonneg_right (norm_nonneg _))
    calc
      _ = Real.exp (-|t|) * (Real.exp (3*t) * ‖g.val t‖) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        rw [abs_of_nonneg ht]
        ring
      _ ≤ Real.exp (-|t|) * hasseMassGauge g :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  · have hb : Real.exp (-3*t) * ‖g.val t‖ ≤ hasseMassGauge g := by
      simpa only [Int.cast_neg, Int.cast_ofNat, hasseMassGauge] using
        (hg (-3)).trans
          (le_add_of_nonneg_left (norm_nonneg (deningerMeyerStrongLogGaugeLinear 0 3 g)))
    calc
      _ = Real.exp (-|t|) * (Real.exp (-3*t) * ‖g.val t‖) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        rw [abs_of_neg (lt_of_not_ge ht)]
        ring
      _ ≤ Real.exp (-|t|) * hasseMassGauge g :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := mul_comm _ _

private def hasseKernelMass : ℝ := ∫ t : ℝ, Real.exp (-|t|)

private theorem hasseKernelMass_nonneg : 0 ≤ hasseKernelMass :=
  integral_nonneg fun _ => (Real.exp_pos _).le

private theorem hasse_mass_le_gauge (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHasseSourceMass g ≤ hasseKernelMass * hasseMassGauge g := by
  have hi : Integrable (fun t : ℝ => Real.exp (-|t|)) := by
    simpa using integrable_abs_pow_mul_exp_neg_mul_abs 0 (by norm_num : (0 : ℝ) < 1)
  have hb := integral_mono (integrable_deningerMeyerHasseSourceMass g)
    (hi.const_mul (hasseMassGauge g)) (hasse_mass_pointwise g)
  calc
    _ ≤ ∫ t : ℝ, hasseMassGauge g * Real.exp (-|t|) := hb
    _ = _ := by rw [integral_const_mul]; exact mul_comm _ _

theorem tendsto_deningerMeyerHasseSourceCost_zero :
    Tendsto deningerMeyerHasseSourceCost
      (𝓝 (0 : DeningerMeyerStrongLogTarget)) (𝓝 0) := by
  have hbound (g : DeningerMeyerStrongLogTarget) :
      deningerMeyerHasseSourceCost g ≤
        hasseKernelMass * (2 * hasseMassGauge g +
          hasseMassGauge (deningerMeyerStrongLogGenerator g)) := by
    have h0 := hasse_mass_le_gauge g
    have h1 := hasse_mass_le_gauge (deningerMeyerStrongLogGenerator g)
    dsimp [deningerMeyerHasseSourceCost]
    nlinarith
  have hc : Continuous (fun g : DeningerMeyerStrongLogTarget =>
      hasseKernelMass * (2 * hasseMassGauge g +
        hasseMassGauge (deningerMeyerStrongLogGenerator g))) :=
    continuous_const.mul ((continuous_const.mul continuous_hasseMassGauge).add
      (continuous_hasseMassGauge.comp deningerMeyerStrongLogGenerator_continuous))
  have ht : Tendsto (fun g : DeningerMeyerStrongLogTarget =>
      hasseKernelMass * (2 * hasseMassGauge g +
        hasseMassGauge (deningerMeyerStrongLogGenerator g))) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero, hasseMassGauge_zero, mul_zero, add_zero] using
      hc.continuousAt.tendsto (x := 0)
  exact squeeze_zero deningerMeyerHasseSourceCost_nonneg hbound ht

/-- Continuity of full-jet admission on the original source quotient. -/
theorem deningerMeyerHasseHilbertLM_continuous : Continuous deningerMeyerHasseHilbertLM := by
  apply (LinearMap.range deningerMeyerStrongLogSumLM).isQuotientMap_mkQ.continuous_iff.mpr
  let L := deningerMeyerHasseHilbertLM.comp
    (LinearMap.range deningerMeyerStrongLogSumLM).mkQ
  change Continuous L
  apply continuous_of_tendsto_nhds_zero L
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  obtain ⟨C, hC, hbound⟩ := deningerMeyerHasseHilbertLM_exists_source_bound
  have ht : Tendsto (fun g : DeningerMeyerStrongLogTarget => C * deningerMeyerHasseSourceCost g)
      (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_deningerMeyerHasseSourceCost_zero
  exact squeeze_zero (fun g => norm_nonneg (L g)) hbound ht

def deningerMeyerHasseHilbertCLM :
    DeningerMeyerStrongLogCohomology →L[ℂ] DeningerArithmeticJetHilbert :=
  ⟨deningerMeyerHasseHilbertLM, deningerMeyerHasseHilbertLM_continuous⟩

@[simp] theorem deningerMeyerHasseHilbertCLM_apply
    (u : DeningerMeyerStrongLogCohomology) (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHasseHilbertCLM u q = deningerMeyerHasseJet u q := rfl

end RHTower
