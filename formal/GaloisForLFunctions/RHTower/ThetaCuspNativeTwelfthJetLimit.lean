import GaloisForLFunctions.RHTower.ThetaCuspNativeOddSchurFarTail

/-! # Exact twelfth-jet Gaussian limit for the complete theta source -/
open Filter Topology
namespace RHTower
noncomputable section

/-- The twelfth first-atom reflection jet has its exact Gaussian scale limit. -/
theorem thetaCuspFirstAtomReflectionJet_12_scaled_tendsto :
    Tendsto (fun x : ℝ => (-1 : ℝ)^(6 : ℕ)*thetaCuspFirstAtomReflectionJet 12 x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)))
      atTop (𝓝 (2724986880 : ℝ)) := by
  let R (u : ℝ) := ((-491520 : ℝ)*u^(7 : ℕ) + 1408303104*u^(6 : ℕ) - 75547148288*u^(5 : ℕ) +
    603009318912*u^(4 : ℕ) - 1280916848640*u^(3 : ℕ) + 886529064960*u^(2 : ℕ) -
    239798845440*u + 43599790080) / (4-6*u)^(2 : ℕ)
  have hc : ContinuousAt R 0 := by
    dsimp only [R]
    apply ContinuousAt.div <;> first | fun_prop | norm_num
  have h := hc.tendsto.comp thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hlim : Tendsto (fun x : ℝ => R ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      atTop (𝓝 (2724986880 : ℝ)) := by
    rw [show R 0 = 2724986880 by norm_num [R]] at h
    exact h
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  have hqn : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by linarith
  have hb : 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    nlinarith [sq_nonneg (thetaCuspSingleAtomReflectionScale 1 x-3)]
  have hd : 4-6*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (by linarith : 0 < thetaCuspSingleAtomReflectionScale 1 x)).mpr
    linarith
  rw [thetaCuspFirstAtomReflectionJet_12, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp only [R]
  field_simp [hqn, hb, hd, Real.exp_ne_zero]
  ring

/-- Complete infinite theta source, including every omitted atom, has the same twelfth limit. -/
theorem thetaCuspNativeScaledEvenJet_six_tendsto :
    Tendsto (thetaCuspNativeScaledEvenJet 6) atTop (𝓝 2724986880) := by
  have herr := ((thetaCuspNativeReflectionJet_firstAtom_error_scaled_tendsto_zero 0 12).mul
    (thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero.pow 6)).const_mul ((-1 : ℝ)^(6 : ℕ))
  have h := thetaCuspFirstAtomReflectionJet_12_scaled_tendsto.add herr
  apply (show Tendsto _ atTop (𝓝 (2724986880 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hf : thetaCuspSourceTerm x 1 ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'
  unfold thetaCuspNativeScaledEvenJet
  norm_num
  field_simp [hq, hf]
  ring

/-- The zeroth normalized native jet converges to unit mass. -/
theorem thetaCuspNativeScaledEvenJet_zero_tendsto :
    Tendsto (thetaCuspNativeScaledEvenJet 0) atTop (𝓝 1) := by
  convert thetaCuspFullSource_div_firstAtom_tendsto_one.pow 2 using 1
  · ext x
    simp [thetaCuspNativeScaledEvenJet, thetaCuspNativeReflectionJet, div_pow]
    ring
  · norm_num

/-- Every fixed center-flux coefficient is lower order than the twelfth source entry. -/
theorem thetaCuspCenterCompensationSource_twelfth_scaled_tendsto_zero :
    Tendsto (fun x : ℝ => thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)))
      atTop (𝓝 0) := by
  have h := thetaCuspCenterCompensationSource_scaled_tendsto_zero.mul
    thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  convert h using 1
  · ext x
    simp only [pow_succ, div_mul_eq_div_mul_one_div, one_div]
    field_simp
  · norm_num

end
end RHTower
