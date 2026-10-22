import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceHorizonModeJets

/-! Actual horizon decay of the original independent-frequency mode and its first tortoise jet. -/
open Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- The original compact radius tends to the true horizon along the negative tortoise ray. -/
theorem horizonCoordinate_tendsto_horizon : Tendsto horizonCoordinate atBot (𝓝 (0:ℝ)) := by
  have he : Tendsto (fun t : ℝ => 4*(Real.exp t)^(2 : ℕ)) atBot (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero] using (Real.tendsto_exp_atBot.pow 2).const_mul 4
  apply squeeze_zero' ?_ ?_ he
  · filter_upwards [eventually_lt_atBot (0:ℝ)] with t ht
    exact (horizonCoordinate_interior t ht).1.le
  · filter_upwards [eventually_lt_atBot (0:ℝ)] with t ht
    rw [horizonCoordinate_factor]
    have hu := radialUnit_bounds t ht
    have hx := Real.exp_pos t
    nlinarith [sq_nonneg (Real.exp t),sq_nonneg (1+radialUnit t),
      mul_nonneg (sq_nonneg (Real.exp t)) (show 0 ≤ 4-(1+radialUnit t)^(2 : ℕ) by nlinarith)]

/-- The actual horizon mode decays in the original spatial coordinate. -/
theorem tortoiseHorizon_tendsto_horizon {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (tortoiseMode false w chi) atBot (𝓝 0) :=
  (horizon_zero h).comp horizonCoordinate_tendsto_horizon

/-- The horizon solution retains its proved nonzero physical endpoint value. -/
theorem tortoiseHorizon_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (tortoiseMode false w chi) (𝓝[<] (0:ℝ)) (𝓝 (connection w chi)) :=
  (horizon_boundary h).comp horizonCoordinate_tendsto_boundary

/-- Its actual first tortoise jet also decays; no ingoing derivative phase is assumed. -/
theorem tortoiseHorizonFirst_tendsto_horizon {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (tortoiseModeFirst false w chi) atBot (𝓝 0) := by
  have hZ := horizonCoordinate_tendsto_horizon
  have hP := (power_tendsto_zero (a := w/2) (by simpa using half_pos (chamber_re_pos h))).comp hZ
  have hF := (gaussFactor_derivatives (z := 0) h false (by simp)).1.comp_ofReal.continuousAt.tendsto.comp hZ
  have hD := (gaussFactor_derivatives (z := 0) h false (by simp)).2.comp_ofReal.continuousAt.tendsto.comp hZ
  have hC := Complex.continuous_ofReal.continuousAt.tendsto.comp hZ
  let G : ℝ → ℂ := fun t => power (w/2) (horizonCoordinate t)*
    (w*gaussFactor w chi false (horizonCoordinate t)+
      2*(horizonCoordinate t:ℂ)*gaussFirst w chi false (horizonCoordinate t))
  have hG : Tendsto G atBot (𝓝 0) := by
    have hh := hP.mul ((hF.const_mul w).add ((hC.const_mul 2).mul hD))
    simpa only [G,Function.comp_def,Complex.ofReal_zero,mul_zero,zero_mul] using! hh
  apply squeeze_zero_norm' ?_ (show Tendsto (fun t => ‖G t‖) atBot (𝓝 0) from by simpa only [norm_zero] using hG.norm)
  filter_upwards [eventually_lt_atBot (0:ℝ)] with t ht
  have hz := horizonCoordinate_interior t ht
  have hz0 : (horizonCoordinate t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)
  have he : tortoiseModeFirst false w chi t=(radialUnit t:ℂ)*G t := by
    dsimp [tortoiseModeFirst,radialModeFirst,horizonFirst,dressFirst,powerFirst,coordinateFirst,G]
    push_cast
    field_simp [hz0]
  rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg (radialUnit_bounds t ht).1.le]
  exact mul_le_of_le_one_left (norm_nonneg _) (radialUnit_bounds t ht).2.le

end
end RHTower.D4BMJointSource
