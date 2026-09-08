import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSolutions
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplacePowerLimits

/-! Physical radial endpoint values in the independent-frequency chamber. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem reverse_tendsto :
    Tendsto (fun z : ℝ => 1-z) (𝓝 (1:ℝ)) (𝓝 (0:ℝ)) := by
  simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝 1) (𝓝 1)).sub
    (tendsto_id : Tendsto (fun z : ℝ => z) (𝓝 1) (𝓝 1)))

private theorem reverse_complex_tendsto :
    Tendsto (fun z : ℝ => (1-z:ℂ)) (𝓝 (1:ℝ)) (𝓝 (0:ℂ)) := by
  simpa only [Function.comp_def,Complex.ofReal_sub,Complex.ofReal_one] using!
    Complex.continuous_ofReal.continuousAt.tendsto.comp reverse_tendsto

theorem reversedGauss_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (fun z : ℝ => gaussFactor w chi true (1-z)) (𝓝 (1:ℝ)) (𝓝 1) := by
  have hF := (gaussFactor_derivatives (z := 0) h true (by simp)).1.continuousAt.tendsto
  simpa only [Function.comp_def,gaussFactor_zero] using! hF.comp reverse_complex_tendsto

theorem reversedGaussFirst_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (fun z : ℝ => gaussFirst w chi true (1-z)) (𝓝 (1:ℝ)) (𝓝 (gaussFirst w chi true 0)) :=
  (gaussFactor_derivatives (z := 0) h true (by simp)).2.continuousAt.tendsto.comp reverse_complex_tendsto

/-- The actual physical horizon solution has the proved, nonzero boundary coefficient. -/
theorem horizon_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (horizon w chi) (𝓝[<] (1:ℝ)) (𝓝 (connection w chi)) := by
  unfold horizon dress
  simpa only [one_mul] using! ((power_tendsto_one (w/2)).mono_left inf_le_left).mul (horizonFactor_boundary h)

/-- The actual horizon solution tends to zero at the horizon in the causal chamber. -/
theorem horizon_zero {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (horizon w chi) (𝓝 (0:ℝ)) (𝓝 0) := by
  have hp : 0 < (w/2).re := by simpa using half_pos (chamber_re_pos h)
  have hF := (gaussFactor_derivatives (z := 0) h false (by simp)).1.comp_ofReal.continuousAt.tendsto
  unfold horizon dress
  simpa only [zero_mul] using! (power_tendsto_zero hp).mul hF

/-- The outer solution satisfies the actual zero AdS boundary condition. -/
theorem normalizable_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (normalizable w chi) (𝓝 (1:ℝ)) (𝓝 0) := by
  have hp := (power_tendsto_zero (a := (1/2:ℂ)) (by norm_num)).comp reverse_tendsto
  unfold normalizable dress outerFactor
  simpa only [Function.comp_def,zero_mul,mul_zero] using!
    (power_tendsto_one (w/2)).mul (hp.mul (reversedGauss_boundary h))

/-- The normalizable boundary amplitude is exactly one; the physical
frequency-dependent horizon factor does not alter this boundary normalization. -/
theorem normalizable_boundary_ratio {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (fun z : ℝ => normalizable w chi z/(Real.sqrt (1-z):ℂ))
      (𝓝[<] (1:ℝ)) (𝓝 1) := by
  have ht := ((power_tendsto_one (w/2)).mul (reversedGauss_boundary h)).mono_left
    (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from inf_le_left)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hs : (Real.sqrt (1-z):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hz)))
  dsimp [normalizable,dress,outerFactor]
  rw [power_half_eq_sqrt (sub_nonneg.mpr hz.le)]
  field_simp

end
end RHTower.D4BMLaplaceRadial
