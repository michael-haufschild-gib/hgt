import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy

/-!
# Fixed-fibre translation obstruction for the theta source metric
-/

open Filter Topology

namespace RHTower

noncomputable section

namespace HedenmalmThetaSource

theorem tendsto_thetaShiftEnvelopeDecay {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun x : ℝ => Real.exp (-(Real.pi * Real.exp (2 * x)) * a))
      atTop (𝓝 0) := by
  have hlinear : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
  have hexp : Tendsto (fun x : ℝ => Real.exp (2 * x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlinear
  have hscale : Tendsto (fun x : ℝ => (Real.pi * a) * Real.exp (2 * x)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (mul_pos Real.pi_pos ha) hexp
  have hzero := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  convert hzero using 1
  funext x
  congr 1
  ring

/-- **Doubly exponential fixed-fibre translation wall.** For every positive shift, the ratio of
the theta source metric before and after the shift tends to infinity. -/
theorem tendsto_thetaSource_div_shift_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => thetaSource.k x / thetaSource.k (x + a)) atTop atTop := by
  have hdecay := tendsto_thetaShiftEnvelopeDecay ha
  refine Filter.tendsto_atTop.mpr ?_
  intro C
  let D : ℝ := |C| + 1
  have hD : 0 < D := by dsimp [D]; linarith [abs_nonneg C]
  have hDU : 0 < D * thetaEnvelopeUpper := mul_pos hD thetaEnvelopeUpper_pos
  have hthreshold : 0 < thetaEnvelopeLower / (D * thetaEnvelopeUpper) :=
    div_pos thetaEnvelopeLower_pos hDU
  have hsmall := hdecay.eventually (eventually_lt_nhds hthreshold)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with x hx hsmallx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hupper := thetaCuspFullSource_le_shift (x := x) (y := x + a) hx (by linarith)
  have hlower := thetaCuspFullSource_ge_envelope hxpos
  have hkshift : 0 < thetaSource.k (x + a) := thetaSource.pos_k _
  apply (le_div_iff₀ hkshift).2
  have hCD : C ≤ D := by
    dsimp [D]
    linarith [le_abs_self C]
  exact (calc
      C * thetaSource.k (x + a) ≤ D * thetaSource.k (x + a) :=
        mul_le_mul_of_nonneg_right hCD hkshift.le
      _ ≤ D * ((thetaEnvelopeUpper * thetaEnvelope x) *
          Real.exp (-(Real.pi * Real.exp (2 * x)) * a)) := by
        gcongr
        simpa only [thetaSource_k, add_sub_cancel_left] using hupper
      _ < thetaEnvelopeLower * thetaEnvelope x := by
        have hs : D * thetaEnvelopeUpper *
            Real.exp (-(Real.pi * Real.exp (2 * x)) * a) < thetaEnvelopeLower := by
          simpa only [mul_comm, mul_left_comm, mul_assoc] using
            (lt_div_iff₀ hDU).mp hsmallx
        have henv := thetaEnvelope_pos x
        nlinarith
      _ ≤ thetaSource.k x := by simpa only [thetaSource_k] using hlower).le

/-- Reflection gives the same blow-up for the opposite fixed-fibre shift. -/
theorem tendsto_thetaSource_div_negShift_atBot {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => thetaSource.k x / thetaSource.k (x - a)) atBot atTop := by
  have h := (tendsto_thetaSource_div_shift_atTop ha).comp tendsto_neg_atBot_atTop
  convert h using 1
  funext x
  simp only [Function.comp_apply]
  rw [← thetaSource_even x, ← thetaSource_even (x - a)]
  congr 2
  ring

/-- No fixed Hilbert-fibre metric comparison can bound a positive source translation. -/
theorem no_thetaSource_shift_metric_bound {a : ℝ} (ha : 0 < a) :
    ¬ ∃ C : ℝ, ∀ x : ℝ, thetaSource.k x ≤ C * thetaSource.k (x + a) := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx⟩ :=
    (Filter.tendsto_atTop.mp (tendsto_thetaSource_div_shift_atTop ha) (C + 1)).exists
  have hk : 0 < thetaSource.k (x + a) := thetaSource.pos_k _
  have hupper : thetaSource.k x / thetaSource.k (x + a) ≤ C :=
    (div_le_iff₀ hk).2 (hC x)
  linarith

/-- Reflection rules out the opposite fixed Hilbert-fibre translation as well. -/
theorem no_thetaSource_negShift_metric_bound {a : ℝ} (ha : 0 < a) :
    ¬ ∃ C : ℝ, ∀ x : ℝ, thetaSource.k x ≤ C * thetaSource.k (x - a) := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx⟩ :=
    (Filter.tendsto_atTop.mp (tendsto_thetaSource_div_negShift_atBot ha) (C + 1)).exists
  have hk : 0 < thetaSource.k (x - a) := thetaSource.pos_k _
  have hupper : thetaSource.k x / thetaSource.k (x - a) ≤ C :=
    (div_le_iff₀ hk).2 (hC x)
  linarith

end HedenmalmThetaSource

end

end RHTower

