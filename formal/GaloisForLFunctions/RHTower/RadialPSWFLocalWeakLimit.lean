import GaloisForLFunctions.RHTower.RadialPSWFMassRetention

/-!
# Compact-interval weak averaging for the radial PSWF phase

This module proves the oscillatory part of the radial leakage weak law on every compact exterior
interval.  For any `C¹` weight, any turning-parameter family in `[0,1]`, and any bandwidth tending
to infinity, the exact Liouville phase (with an arbitrary constant phase shift) makes `cos²` average
to `1/2`.  The error is the explicit amplitude-variation budget divided by bandwidth.  Endpoint
and far-tail tightness and transfer from the actual PSWF solution remain separate analytic inputs.
-/

open Filter MeasureTheory Set

namespace RHTower

noncomputable section

theorem abs_integral_weight_mul_cos_sq_radialPhase_add_sub_half_le
    {a b c sigma theta : ℝ} (hab : a ≤ b) (ha : 1 < a) (hc : 0 < c)
    (hs0 : 0 ≤ sigma) (hs1 : sigma ≤ 1)
    {w w' : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw'c : ContinuousOn w' (Icc a b)) :
    |(∫ t in a..b, w t * Real.cos (c * radialPSWFExteriorPhase sigma t + theta) ^ (2 : ℕ))
        - (1 / 2) * ∫ t in a..b, w t|
      ≤ (|w b| + |w a| + ∫ t in a..b, |w' t|) / c := by
  have hsigma : sigma ^ (2 : ℕ) ≤ 1 := by nlinarith
  refine abs_integral_weight_mul_cos_sq_sub_half_le'
    (φ := fun t => c * radialPSWFExteriorPhase sigma t + theta)
    (φ' := fun t => c * radialPSWFExteriorSpeed sigma t)
    (φ'' := fun t => c * radialPSWFSpeedDeriv sigma t)
    hab hc hw hw'c
    (fun x hx => ((hasDerivAt_radialPSWFExteriorPhase sigma (ha.trans_le hx.1)).const_mul c).add_const theta)
    (fun x hx => (hasDerivAt_radialPSWFExteriorSpeed hsigma (ha.trans_le hx.1)).const_mul c)
    (continuousOn_const.mul (continuousOn_radialPSWFSpeedDeriv hsigma ha)) ?_ ?_
  · intro x hx
    have hneg := radialPSWFExteriorSpeed_deriv_nonpos hsigma (ha.trans_le hx.1)
    have : radialPSWFSpeedDeriv sigma x ≤ 0 := hneg
    nlinarith
  · intro x hx
    have hone := one_le_radialPSWFExteriorSpeed hs0 hs1 (ha.trans_le hx.1)
    rw [abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ c * radialPSWFExteriorSpeed sigma x)]
    nlinarith

theorem tendsto_integral_weight_mul_cos_sq_radialPhase_add
    {ι : Type*} {l : Filter ι} {c sigma : ι → ℝ} {theta a b : ℝ}
    (hc : Tendsto c l atTop) (hs0 : ∀ᶠ i in l, 0 ≤ sigma i)
    (hs1 : ∀ᶠ i in l, sigma i ≤ 1)
    (hab : a ≤ b) (ha : 1 < a) {w w' : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x)
    (hw'c : ContinuousOn w' (Icc a b)) :
    Tendsto (fun i =>
      ∫ t in a..b, w t * Real.cos (c i * radialPSWFExteriorPhase (sigma i) t + theta) ^ (2 : ℕ))
      l (nhds ((1 / 2) * ∫ t in a..b, w t)) := by
  let B := |w b| + |w a| + ∫ t in a..b, |w' t|
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hint : 0 ≤ ∫ t in a..b, |w' t| :=
      intervalIntegral.integral_nonneg hab (fun x _ => abs_nonneg _)
    positivity
  have hmajor : Tendsto (fun i => B / c i) l (nhds 0) := by
    have hinv : Tendsto (fun i => (c i)⁻¹) l (nhds 0) := hc.inv_tendsto_atTop
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul B
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using squeeze_zero'
    (Eventually.of_forall fun i => abs_nonneg _)
    (by
      filter_upwards [hs0, hs1, hc.eventually (eventually_gt_atTop (0 : ℝ))]
        with i h0 h1 hci
      exact abs_integral_weight_mul_cos_sq_radialPhase_add_sub_half_le
        hab ha hci h0 h1 hw hw'c)
    hmajor

end

end RHTower

