import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceHorizonModeLimits

/-! Actual value and first-jet limits of the original normalizable tortoise mode. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original normalizable mode has zero outer endpoint value in tortoise coordinates. -/
theorem tortoiseNormalizable_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (tortoiseMode true w chi) (𝓝[<] (0:ℝ)) (𝓝 0) :=
  ((normalizable_boundary h).mono_left inf_le_left).comp horizonCoordinate_tendsto_boundary

/-- The original normalizable tortoise derivative tends to minus one, with its full frequency dressing retained. -/
theorem tortoiseNormalizableFirst_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (tortoiseModeFirst true w chi) (𝓝[<] (0:ℝ)) (𝓝 (-1:ℂ)) := by
  have hz : Tendsto (fun t : ℝ => (horizonCoordinate t:ℂ)) (𝓝[<] (0:ℝ)) (𝓝 1) := by
    have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (horizonCoordinate_tendsto_boundary.mono_right nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_one,Function.comp_def] using ht
  have hn := (normalizableFirst_boundary h).comp horizonCoordinate_tendsto_boundary
  have he := (hz.const_mul 2).mul hn
  have he' : Tendsto (fun t : ℝ => 2*(horizonCoordinate t:ℂ)*
      ((Real.sqrt (1-horizonCoordinate t):ℂ)*normalizableFirst w chi (horizonCoordinate t)))
      (𝓝[<] (0:ℝ)) (𝓝 (-1:ℂ)) := by
    convert he using 1 <;> norm_num
  apply he'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hs : Real.sqrt (1-horizonCoordinate t) = radialUnit t := by
    rw [horizonCoordinate,sub_sub_cancel,Real.sqrt_sq (radialUnit_bounds t ht).1.le]
  rw [hs]
  dsimp [tortoiseModeFirst,radialModeFirst,coordinateFirst]
  push_cast
  ring

end
end RHTower.D4BMJointSource
