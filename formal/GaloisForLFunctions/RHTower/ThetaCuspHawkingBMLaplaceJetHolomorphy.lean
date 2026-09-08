import GaloisForLFunctions.HTGeometry.HypergeometricSpatialJets
import GaloisForLFunctions.HTGeometry.HypergeometricLocalFamilies
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceFrequencyContinuation

/-! Frequency holomorphy of the original physical spatial jets. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original first horizon Gauss jet is holomorphic even when its numerator series terminates. -/
theorem horizonGaussFirst_frequency_differentiableAt (w chi z : ℂ) (hw : w.im ≠ 0)
    (hz : ‖z‖ < 1) : DifferentiableAt ℂ (fun u => gaussFirst u chi false z) w := by
  have hz' : ‖z‖ₑ < 1 := by simpa only [← ofReal_norm,ENNReal.ofReal_lt_one] using hz
  have he (u : ℂ) : gaussFirst u chi false z =
      (gaussA u chi*gaussB u chi/gaussC u)*
        ordinaryHypergeometric (gaussA u chi+1) (gaussB u chi+1) (gaussC u+1) z :=
    hypergeometric_first_eq_shift _ _ _ _ hz'
  simp_rw [he]
  have hc : (gaussC w+1).im ≠ 0 := by simpa [gaussC] using hw
  have hd := hypergeometric_family_of_im_ne_zero
    (show AnalyticAt ℂ (fun u => gaussA u chi+1) w by unfold gaussA; fun_prop)
    (show AnalyticAt ℂ (fun u => gaussB u chi+1) w by unfold gaussB; fun_prop)
    (show AnalyticAt ℂ (fun u => gaussC u+1) w by unfold gaussC; fun_prop) hc hz
  have hn : gaussC w ≠ 0 := by intro h; apply hw; have hi := congrArg Complex.im h; simpa [gaussC] using hi
  exact ((show DifferentiableAt ℂ (fun u => gaussA u chi*gaussB u chi) w by
    unfold gaussA gaussB; fun_prop).div
      (show DifferentiableAt ℂ gaussC w by unfold gaussC; fun_prop) hn).mul hd

/-- The actual first normalizable Gauss jet is entire in frequency. -/
theorem outerGaussFirst_frequency_entire (chi z : ℂ) (hz : ‖z‖ < 1) :
    Differentiable ℂ (fun w => gaussFirst w chi true z) := by
  intro w
  have hz' : ‖z‖ₑ < 1 := by simpa only [← ofReal_norm,ENNReal.ofReal_lt_one] using hz
  have he (u : ℂ) : gaussFirst u chi true z =
      ((gaussC u-gaussA u chi)*(gaussC u-gaussB u chi)/(3/2))*
        ordinaryHypergeometric (gaussC u-gaussA u chi+1) (gaussC u-gaussB u chi+1) (3/2+1) z :=
    hypergeometric_first_eq_shift _ _ _ _ hz'
  simp_rw [he]
  have hd := hypergeometric_family_of_re_pos
    (show AnalyticAt ℂ (fun u => gaussC u-gaussA u chi+1) w by unfold gaussC gaussA; fun_prop)
    (show AnalyticAt ℂ (fun u => gaussC u-gaussB u chi+1) w by unfold gaussC gaussB; fun_prop)
    (show AnalyticAt ℂ (fun _ : ℂ => (3/2+1:ℂ)) w from analyticAt_const) (by norm_num) hz
  exact (show DifferentiableAt ℂ
    (fun u => (gaussC u-gaussA u chi)*(gaussC u-gaussB u chi)/(3/2)) w by
      unfold gaussC gaussA gaussB; fun_prop).mul hd

/-- The dressed horizon derivative retains its actual power jet under continuation. -/
theorem horizonFirst_frequency_analyticAt (w chi : ℂ) (hw : w.im ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo 0 1) : AnalyticAt ℂ (fun u => horizonFirst u chi z) w := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hw] with u hu
  have hn : ‖(z:ℂ)‖ < 1 := by simpa [abs_of_pos hz.1] using hz.2
  have hp := (power_exponent_entire hz.1).differentiableAt.comp u
    (show DifferentiableAt ℂ (fun v : ℂ => v/2) u by fun_prop)
  have hF := horizonGauss_frequency_differentiableAt u chi z hu hn
  have hD := horizonGaussFirst_frequency_differentiableAt u chi z hu hn
  have hk : DifferentiableAt ℂ (fun v : ℂ => v/2/(z:ℂ)) u := by fun_prop
  simpa only [horizonFirst,dressFirst,powerFirst,Pi.mul_def,Pi.add_def,Function.comp_def,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using!
    ((hk.mul hp).mul hF).add (hp.mul hD)

/-- The dressed normalizable derivative is entire with its outer square-root jet retained. -/
theorem normalizableFirst_frequency_entire (chi : ℂ) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    Differentiable ℂ (fun w => normalizableFirst w chi z) := by
  intro w
  have hn : ‖((1-z:ℝ):ℂ)‖ < 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith [hz.2])]
    linarith [hz.1]
  have hp := (power_exponent_entire hz.1).differentiableAt.comp w
    (show DifferentiableAt ℂ (fun v : ℂ => v/2) w by fun_prop)
  have hF := outerGauss_frequency_differentiableAt w chi ((1-z:ℝ):ℂ) hn
  have hD := (outerGaussFirst_frequency_entire chi ((1-z:ℝ):ℂ) hn).differentiableAt (x := w)
  have hk : DifferentiableAt ℂ (fun v : ℂ => v/2/(z:ℂ)) w := by fun_prop
  have ho := hF.const_mul (power (1/2) (1-z))
  have ho1 := (hF.const_mul (-powerFirst (1/2) (1-z))).sub (hD.const_mul (power (1/2) (1-z)))
  simpa only [normalizableFirst,dressFirst,powerFirst,outerFactor,outerFirst,Pi.mul_def,Pi.add_def,
    Function.comp_def,Pi.sub_def,Complex.ofReal_sub,Complex.ofReal_one,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using!
      ((hk.mul hp).mul ho).add (hp.mul ho1)

end
end RHTower.D4BMLaplaceRadial
