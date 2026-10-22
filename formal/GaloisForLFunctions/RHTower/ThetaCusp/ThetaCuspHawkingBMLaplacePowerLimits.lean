import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplacePowerJets

/-! Endpoint normalization of the physical radial power factors. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

theorem power_half_eq_sqrt {z : ℝ} (hz : 0 ≤ z) : power (1/2) z=(Real.sqrt z:ℂ) := by
  rw [power,Real.sqrt_eq_rpow,Complex.ofReal_cpow hz]
  norm_num

theorem power_tendsto_one (a : ℂ) : Tendsto (power a) (𝓝 (1:ℝ)) (𝓝 1) := by
  have h := (power_derivatives a (show (0:ℝ)<1 by norm_num)).1.continuousAt.tendsto
  simpa [power] using h

/-- Positive real exponent gives the actual zero horizon limit of the
complex power, including its oscillatory phase. -/
theorem power_tendsto_zero {a : ℂ} (ha : 0 < a.re) :
    Tendsto (power a) (𝓝 (0:ℝ)) (𝓝 0) := by
  have h := (Complex.continuousAt_ofReal_cpow_const 0 a (Or.inl ha)).tendsto
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha
  change Tendsto (fun z : ℝ => (z:ℂ)^a) (𝓝 (0:ℝ)) (𝓝 (0:ℂ))
  simpa only [Complex.ofReal_zero,Complex.zero_cpow ha0] using! h

theorem powerFirst_tendsto_one (a : ℂ) :
    Tendsto (powerFirst a) (𝓝 (1:ℝ)) (𝓝 a) := by
  have h := (power_derivatives a (show (0:ℝ)<1 by norm_num)).2.continuousAt.tendsto
  simpa [powerFirst,power] using h

end
end RHTower.D4BMLaplaceRadial
