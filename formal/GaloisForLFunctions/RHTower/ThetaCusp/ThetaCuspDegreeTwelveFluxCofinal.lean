import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspDegreeTwelveFluxShape
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeOddSchurFarTail
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-!
# Cofinal size of the literal degree-twelve flux derivative

On the physical ray the negative boundary correction is lower order than the
native fourteenth-jet scale. This compares actual completed-source flux with
the exact first-atom mass and scale; it does not assert the native odd-four
Schur reserve or the integrated sign.
-/

open Filter Topology
namespace RHTower
noncomputable section

private theorem radius_eleven_div_scale_six_tendsto_zero :
    Tendsto (fun x : ℝ => (2*x)^(11 : ℕ) /
      thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) atTop (𝓝 0) := by
  have h := (GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop
    (b := (12 : ℝ)) (by norm_num) 11).const_mul
      ((2 : ℝ)^(11 : ℕ)/(Real.pi^(6 : ℕ)))
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards with x
  have hp : Real.exp (12*x) = Real.exp (2*x)^(6 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [show Real.exp (-(12*x)) = (Real.exp (2*x)^(6 : ℕ))⁻¹ by
    rw [Real.exp_neg, hp]]
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow,
    mul_one, mul_pow, div_eq_mul_inv]
  field_simp [Real.pi_ne_zero, Real.exp_ne_zero]

private theorem rcoth_div_scale_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => rcoth (a*(2*x)) /
      thetaCuspSingleAtomReflectionScale 1 x) atTop (𝓝 0) := by
  have htop := thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero.const_mul
    (rcoth (a*2))
  have hbound : ∀ᶠ x : ℝ in atTop,
      0 ≤ rcoth (a*(2*x)) / thetaCuspSingleAtomReflectionScale 1 x ∧
      rcoth (a*(2*x)) / thetaCuspSingleAtomReflectionScale 1 x ≤
        rcoth (a*2)*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
      unfold thetaCuspSingleAtomReflectionScale
      positivity
    have hax : 0 < a*(2*x) := by positivity
    have hc : rcoth (a*(2*x)) < rcoth (a*2) :=
      rcoth_strictAntiOn_pos (mul_pos ha (by norm_num)) hax (by nlinarith [ha, hx])
    constructor
    · exact div_nonneg
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_lt_rcoth_of_pos hax).le) hq.le
    · calc
        rcoth (a*(2*x)) / thetaCuspSingleAtomReflectionScale 1 x ≤
          rcoth (a*2) / thetaCuspSingleAtomReflectionScale 1 x :=
            div_le_div_of_nonneg_right hc.le hq.le
        _ = rcoth (a*2)*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹ := by
          ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [mul_zero] using htop)
    (hbound.mono fun x hx => hx.1) (hbound.mono fun x hx => hx.2)

private theorem flux_logRate_div_scale_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ =>
      thetaCuspDegreeTwelveFluxLogRate a (2*x) /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (𝓝 (-2 : ℝ)) := by
  have hratio := thetaCuspFullSource_deriv_div_firstAtom_scale_tendsto.div
    thetaCuspFullSource_div_firstAtom_tendsto_one (by norm_num)
  have hlog : Tendsto (fun x : ℝ =>
      deriv thetaCuspLogSource x / thetaCuspSingleAtomReflectionScale 1 x)
      atTop (𝓝 (-2 : ℝ)) := by
    apply (show Tendsto _ atTop (𝓝 (-2 : ℝ)) from by simpa using hratio).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hf : thetaCuspSourceTerm x 1 ≠ 0 :=
      (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'
    have hs : thetaCuspFullSource x ≠ 0 := (thetaCuspFullSource_pos_all x).ne'
    have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
      unfold thetaCuspSingleAtomReflectionScale
      positivity
    rw [(hasDerivAt_thetaCuspLogSource x).deriv]
    simp only [iteratedDeriv_one]
    simp only [Pi.div_apply]
    field_simp [hf, hs, hq]
  have hfirst := (tendsto_inv_atTop_zero.mul
    thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero).const_mul (6 : ℝ)
  have hsecond := (rcoth_div_scale_tendsto_zero ha).const_mul a
  have h := (hfirst.add hsecond).add hlog
  apply (show Tendsto _ atTop (𝓝 (-2 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  unfold thetaCuspDegreeTwelveFluxLogRate
  field_simp [hx.ne', hq]
  ring

/-- The lawful degree-twelve flux derivative is negligible at the native odd-four source scale. -/
theorem degree_twelve_flux_deriv_scaled_seven_tendsto_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ =>
      deriv (thetaCuspDegreeTwelveFlux a) (2*x) /
        ((2*x)*Real.sinh (a*(2*x))*thetaCuspSourceTerm x 1^(2 : ℕ)*
          thetaCuspSingleAtomReflectionScale 1 x^(7 : ℕ)))
      atTop (𝓝 0) := by
  have hp := radius_eleven_div_scale_six_tendsto_zero
  have hm := thetaCuspFullSource_div_firstAtom_tendsto_one
  have hl := flux_logRate_div_scale_tendsto ha
  have h := (hp.mul (hm.pow 2)).mul hl
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hr : 0 < 2*x := by linarith
  have hsinh : Real.sinh (a*(2*x)) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos ha hr)).ne'
  have hf : thetaCuspSourceTerm x 1 ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  rw [thetaCuspDegreeTwelveFlux_deriv_eq_mul_logRate ha hr]
  unfold thetaCuspDegreeTwelveFlux
  field_simp [hr.ne', hsinh, hf, hq]

private theorem radius_one_div_scale_four_tendsto_zero :
    Tendsto (fun x : ℝ => (2*x) /
      thetaCuspSingleAtomReflectionScale 1 x^(4 : ℕ)) atTop (𝓝 0) := by
  have h := (GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop
    (b := (8 : ℝ)) (by norm_num) 1).const_mul
      ((2 : ℝ)/(Real.pi^(4 : ℕ)))
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards with x
  have hp : Real.exp (8*x) = Real.exp (2*x)^(4 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [show Real.exp (-(8*x)) = (Real.exp (2*x)^(4 : ℕ))⁻¹ by
    rw [Real.exp_neg, hp]]
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow,
    mul_one, mul_pow, div_eq_mul_inv]
  field_simp [Real.pi_ne_zero, Real.exp_ne_zero]

private def centerFluxLogRate (a r : ℝ) : ℝ :=
  2/r + a*rcoth (a*r) + deriv thetaCuspLogSource (r/2)

private theorem center_flux_logRate_div_scale_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => centerFluxLogRate a (2*x) /
      thetaCuspSingleAtomReflectionScale 1 x) atTop (𝓝 (-2 : ℝ)) := by
  have hfirst := (tendsto_inv_atTop_zero.mul
    thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero).const_mul (5 : ℝ)
  have h := (flux_logRate_div_scale_tendsto ha).sub hfirst
  apply (show Tendsto _ atTop (𝓝 (-2 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  unfold centerFluxLogRate thetaCuspDegreeTwelveFluxLogRate
  field_simp [hx.ne', hq]
  ring

private theorem center_flux_deriv_eq_mul_logRate {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    deriv (thetaCuspCenterCompensationFlux a) r =
      thetaCuspCenterCompensationFlux a r * centerFluxLogRate a r := by
  have hsinh : Real.sinh (a*r) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos ha hr)).ne'
  have hS : thetaCuspFullSource (r/2) ≠ 0 :=
    (thetaCuspFullSource_pos_all (r/2)).ne'
  rw [(hasDerivAt_thetaCuspCenterCompensationFlux a r).deriv]
  unfold thetaCuspCenterCompensationFlux centerFluxLogRate rcoth
  rw [(hasDerivAt_thetaCuspLogSource (r/2)).deriv]
  simp only [iteratedDeriv_one]
  field_simp [hr.ne', hsinh, hS]

/-- The lawful degree-two center correction vanishes at the corrected odd-head scale. -/
theorem center_flux_deriv_scaled_five_tendsto_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ =>
      deriv (thetaCuspCenterCompensationFlux a) (2*x) /
        ((2*x)*Real.sinh (a*(2*x))*thetaCuspSourceTerm x 1^(2 : ℕ)*
          thetaCuspSingleAtomReflectionScale 1 x^(5 : ℕ)))
      atTop (𝓝 0) := by
  have hp := radius_one_div_scale_four_tendsto_zero
  have hm := thetaCuspFullSource_div_firstAtom_tendsto_one
  have hl := center_flux_logRate_div_scale_tendsto ha
  have h := (hp.mul (hm.pow 2)).mul hl
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hr : 0 < 2*x := by linarith
  have hsinh : Real.sinh (a*(2*x)) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos ha hr)).ne'
  have hf : thetaCuspSourceTerm x 1 ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  rw [center_flux_deriv_eq_mul_logRate ha hr]
  unfold thetaCuspCenterCompensationFlux
  field_simp [hr.ne', hsinh, hf, hq]


end
end RHTower
