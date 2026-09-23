import GaloisForLFunctions.HTGeometry.GaussBonnetClapeyron
import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalFreeEnergy

/-!
# The coexistence curve terminates at the quartic critical minimum

Limits complete the Model B phase picture in arXiv:2609.00025 section 5.
Along the actual fixed-charge curve both radii merge, entropy and volume
jumps vanish, and the Clapeyron slope has a finite strictly positive limit.
The full pressure and temperature ranges are their positive subcritical intervals,
with a unique parameter at every point. All limits are analytic, with no
numerical sampling or asymptotic premise.
-/
noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.CPV

theorem thermalRatio_tendsto_atBot_one : Tendsto thermalRatio atBot (𝓝 1) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp Real.tendsto_exp_atBot.neg
  unfold thermalRatio
  simpa only [Function.comp_def, neg_zero, Real.exp_zero] using h

theorem thermalRatio_tendsto_atTop_zero : Tendsto thermalRatio atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp Real.tendsto_exp_atTop)

end GaloisForLFunctions.HTGeometry.CPV
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbCoexistenceShape_tendsto_critical : Tendsto egbCoexistenceShape atBot (𝓝 6) := by
  have hr := thermalRatio_tendsto_atBot_one
  have h : Tendsto egbCoexistenceShape atBot (𝓝 ((1 : ℝ)^(2 : ℕ) + 4*1 + 1)) :=
    ((hr.pow 2).add (tendsto_const_nhds.mul hr)).add tendsto_const_nhds
  norm_num at h
  exact h

theorem egbCoexistenceShape_tendsto_cold : Tendsto egbCoexistenceShape atTop (𝓝 1) := by
  have hr := thermalRatio_tendsto_atTop_zero
  have h : Tendsto egbCoexistenceShape atTop (𝓝 ((0 : ℝ)^(2 : ℕ) + 4*0 + 1)) :=
    ((hr.pow 2).add (tendsto_const_nhds.mul hr)).add tendsto_const_nhds
  norm_num at h
  exact h

/-- The small coexistence radius approaches the critical radius sqrt(6) times effective charge. -/
theorem egbFixedCharge_small_radius_critical (w : ℝ) :
    Tendsto (fun tau => egbCoexistenceSmallRadius (egbFixedChargeLogScale w tau) tau) atBot
      (𝓝 (Real.exp w * Real.sqrt 6)) := by
  simp only [funext fun tau => (egbFixedCharge_radii w tau).1]
  exact tendsto_const_nhds.mul egbCoexistenceShape_tendsto_critical.sqrt

/-- The large coexistence radius approaches exactly the same critical radius. -/
theorem egbFixedCharge_large_radius_critical (w : ℝ) :
    Tendsto (fun tau => egbCoexistenceLargeRadius (egbFixedChargeLogScale w tau)) atBot
      (𝓝 (Real.exp w * Real.sqrt 6)) := by
  simp only [funext fun tau => (egbFixedCharge_radii w tau).2]
  have h := (tendsto_const_nhds (x := Real.exp w)).mul egbCoexistenceShape_tendsto_critical.sqrt
  simpa only [div_one, Pi.div_def] using h.div thermalRatio_tendsto_atBot_one one_ne_zero

theorem egbFixedChargePressure_critical_limit (w : ℝ) :
    Tendsto (egbFixedChargePressure w) atBot (𝓝 (1 / (96 * Real.pi * Real.exp w ^ (2 : ℕ)))) := by
  rw [show egbFixedChargePressure w = (fun tau => 3 * thermalRatio tau ^ (2 : ℕ) /
    (8 * Real.pi * Real.exp w ^ (2 : ℕ) * egbCoexistenceShape tau ^ (2 : ℕ))) from funext (egbFixedChargePressure_formula w)]
  have h := ((tendsto_const_nhds (x := (3 : ℝ))).mul (thermalRatio_tendsto_atBot_one.pow 2)).div
    ((tendsto_const_nhds (x := 8 * Real.pi * Real.exp w ^ (2 : ℕ))).mul (egbCoexistenceShape_tendsto_critical.pow 2)) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  norm_num
  ring

theorem egbFixedChargeTemperature_critical_limit (w : ℝ) :
    Tendsto (egbFixedChargeTemperature w) atBot (𝓝 (1 / (3 * Real.pi * Real.exp w * Real.sqrt 6))) := by
  rw [show egbFixedChargeTemperature w = (fun tau => thermalRatio tau * (1 + thermalRatio tau) /
    (Real.pi * Real.exp w * egbCoexistenceShape tau * Real.sqrt (egbCoexistenceShape tau))) from
      funext (egbFixedChargeTemperature_formula w)]
  have hd := ((tendsto_const_nhds (x := Real.pi * Real.exp w)).mul egbCoexistenceShape_tendsto_critical).mul
    egbCoexistenceShape_tendsto_critical.sqrt
  have h := (thermalRatio_tendsto_atBot_one.mul ((tendsto_const_nhds (x := (1 : ℝ))).add thermalRatio_tendsto_atBot_one)).div hd (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  norm_num
  field_simp
  ring

/-- The entropy discontinuity closes continuously at criticality. -/
theorem egbFixedChargeEntropyJump_critical_limit (w : ℝ) :
    Tendsto (egbFixedChargeEntropyJump w) atBot (𝓝 0) := by
  have hs := (tendsto_const_nhds (x := Real.pi)).mul ((egbFixedCharge_small_radius_critical w).pow 2)
  have hl := (tendsto_const_nhds (x := Real.pi)).mul ((egbFixedCharge_large_radius_critical w).pow 2)
  unfold egbFixedChargeEntropyJump egbEntropyB
  simpa only [sub_self] using hl.sub hs

/-- The thermodynamic volume discontinuity vanishes at the same endpoint. -/
theorem egbFixedChargeVolumeJump_critical_limit (w : ℝ) :
    Tendsto (egbFixedChargeVolumeJump w) atBot (𝓝 0) := by
  have hs := ((tendsto_const_nhds (x := 4 * Real.pi)).mul ((egbFixedCharge_small_radius_critical w).pow 3)).div_const 3
  have hl := ((tendsto_const_nhds (x := 4 * Real.pi)).mul ((egbFixedCharge_large_radius_critical w).pow 3)).div_const 3
  unfold egbFixedChargeVolumeJump egbThermodynamicVolume
  simpa only [sub_self] using hl.sub hs

/-- Equality of Gibbs minima gives the actual fixed-charge enthalpy jump. -/
theorem egbFixedCharge_enthalpy_jump (w tau theta : ℝ) :
    egbMass (egbFixedChargePressure w tau) (Real.exp w * Real.cos theta) (Real.exp w * Real.sin theta)
        (egbCoexistenceLargeRadius (egbFixedChargeLogScale w tau)) -
      egbMass (egbFixedChargePressure w tau) (Real.exp w * Real.cos theta) (Real.exp w * Real.sin theta)
        (egbCoexistenceSmallRadius (egbFixedChargeLogScale w tau) tau) =
      egbFixedChargeTemperature w tau * egbFixedChargeEntropyJump w tau := by
  have h := egbCoexistence_latent_heat (egbFixedChargeLogScale w tau) tau theta
  rw [(egbFixedCharge_parameters w tau theta).1, (egbFixedCharge_parameters w tau theta).2] at h
  exact h

/-- The latent heat tends to zero along the same actual coexistence family. -/
theorem egbFixedCharge_latent_heat_critical_limit (w theta : ℝ) :
    Tendsto (fun tau =>
      egbMass (egbFixedChargePressure w tau) (Real.exp w * Real.cos theta) (Real.exp w * Real.sin theta)
          (egbCoexistenceLargeRadius (egbFixedChargeLogScale w tau)) -
        egbMass (egbFixedChargePressure w tau) (Real.exp w * Real.cos theta) (Real.exp w * Real.sin theta)
          (egbCoexistenceSmallRadius (egbFixedChargeLogScale w tau) tau)) atBot (𝓝 0) := by
  simp only [funext fun tau => egbFixedCharge_enthalpy_jump w tau theta]
  simpa only [mul_zero] using (egbFixedChargeTemperature_critical_limit w).mul (egbFixedChargeEntropyJump_critical_limit w)

/-- Cancellation of the common vanishing jump exposes the regular critical slope. -/
theorem egbFixedCharge_clapeyron_slope_formula (w tau : ℝ) :
    deriv (egbFixedChargePressure w) tau / deriv (egbFixedChargeTemperature w) tau =
      3 * thermalRatio tau * (1 + thermalRatio tau) /
        (4 * Real.exp w * Real.sqrt (egbCoexistenceShape tau) * (1 + thermalRatio tau + thermalRatio tau ^ (2 : ℕ))) := by
  rw [egbFixedCharge_clapeyron, egbFixedChargeEntropyJump_formula, egbFixedChargeVolumeJump_formula]
  rw [show 1 - thermalRatio tau ^ (3 : ℕ) = (1 - thermalRatio tau) * (1 + thermalRatio tau + thermalRatio tau ^ (2 : ℕ)) by ring,
    show 1 - thermalRatio tau ^ (2 : ℕ) = (1 - thermalRatio tau) * (1 + thermalRatio tau) by ring]
  have h1 : 1 + thermalRatio tau + thermalRatio tau ^ (2 : ℕ) ≠ 0 := by nlinarith [thermalRatio_pos tau, sq_nonneg (thermalRatio tau)]
  field_simp [Real.pi_ne_zero, (thermalRatio_pos tau).ne', (egbCoexistenceShape_pos tau).ne',
    (Real.sqrt_pos.mpr (egbCoexistenceShape_pos tau)).ne', (sub_pos.mpr (thermalRatio_lt_one tau)).ne', h1]

/-- The 0/0 jump ratio has a finite, positive critical limit. -/
theorem egbFixedCharge_clapeyron_critical_limit (w : ℝ) :
    Tendsto (fun tau => deriv (egbFixedChargePressure w) tau / deriv (egbFixedChargeTemperature w) tau) atBot
      (𝓝 (1 / (2 * Real.exp w * Real.sqrt 6))) := by
  rw [show (fun tau => deriv (egbFixedChargePressure w) tau / deriv (egbFixedChargeTemperature w) tau) =
      (fun tau => 3 * thermalRatio tau * (1 + thermalRatio tau) /
        (4 * Real.exp w * Real.sqrt (egbCoexistenceShape tau) * (1 + thermalRatio tau + thermalRatio tau ^ (2 : ℕ)))) from
    funext (egbFixedCharge_clapeyron_slope_formula w)]
  have hr := thermalRatio_tendsto_atBot_one
  have hn := ((tendsto_const_nhds (x := (3 : ℝ))).mul hr).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hr)
  have hd := ((tendsto_const_nhds (x := 4 * Real.exp w)).mul egbCoexistenceShape_tendsto_critical.sqrt).mul
    (((tendsto_const_nhds (x := (1 : ℝ))).add hr).add (hr.pow 2))
  have h := hn.div hd (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  norm_num
  field_simp
  ring

theorem egbFixedChargePressure_cold_limit (w : ℝ) : Tendsto (egbFixedChargePressure w) atTop (𝓝 0) := by
  rw [show egbFixedChargePressure w = (fun tau => 3 * thermalRatio tau ^ (2 : ℕ) /
    (8 * Real.pi * Real.exp w ^ (2 : ℕ) * egbCoexistenceShape tau ^ (2 : ℕ))) from funext (egbFixedChargePressure_formula w)]
  have h := ((tendsto_const_nhds (x := (3 : ℝ))).mul (thermalRatio_tendsto_atTop_zero.pow 2)).div
    ((tendsto_const_nhds (x := 8 * Real.pi * Real.exp w ^ (2 : ℕ))).mul (egbCoexistenceShape_tendsto_cold.pow 2)) (by positivity)
  simpa [Pi.div_def] using h

theorem egbFixedChargeTemperature_cold_limit (w : ℝ) : Tendsto (egbFixedChargeTemperature w) atTop (𝓝 0) := by
  rw [show egbFixedChargeTemperature w = (fun tau => thermalRatio tau * (1 + thermalRatio tau) /
    (Real.pi * Real.exp w * egbCoexistenceShape tau * Real.sqrt (egbCoexistenceShape tau))) from
      funext (egbFixedChargeTemperature_formula w)]
  have hd := ((tendsto_const_nhds (x := Real.pi * Real.exp w)).mul egbCoexistenceShape_tendsto_cold).mul
    egbCoexistenceShape_tendsto_cold.sqrt
  have h := (thermalRatio_tendsto_atTop_zero.mul ((tendsto_const_nhds (x := (1 : ℝ))).add thermalRatio_tendsto_atTop_zero)).div hd (by positivity)
  simpa [Pi.div_def] using h


/-- Every finite coexistence parameter stays strictly below the critical pressure. -/
theorem egbFixedChargePressure_below_critical (w tau : ℝ) :
    egbFixedChargePressure w tau < 1 / (96 * Real.pi * Real.exp w ^ (2 : ℕ)) := by
  exact lt_of_lt_of_le (egbFixedChargePressure_strictAnti w (show tau - 1 < tau by linarith))
    ((egbFixedChargePressure_strictAnti w).antitone.ge_of_tendsto
      (egbFixedChargePressure_critical_limit w) (tau - 1))

/-- Every finite coexistence parameter stays strictly below the critical temperature. -/
theorem egbFixedChargeTemperature_below_critical (w tau : ℝ) :
    egbFixedChargeTemperature w tau < 1 / (3 * Real.pi * Real.exp w * Real.sqrt 6) := by
  exact lt_of_lt_of_le (egbFixedChargeTemperature_strictAnti w (show tau - 1 < tau by linarith))
    ((egbFixedChargeTemperature_strictAnti w).antitone.ge_of_tendsto
      (egbFixedChargeTemperature_critical_limit w) (tau - 1))

/-- The constructed coexistence family covers every positive subcritical pressure. -/
theorem egbFixedChargePressure_range (w : ℝ) :
    Set.range (egbFixedChargePressure w) = Set.Ioo 0 (1 / (96 * Real.pi * Real.exp w ^ (2 : ℕ))) := by
  ext p
  constructor
  · rintro ⟨tau, rfl⟩
    exact ⟨egbCoexistencePressure_pos _ _, egbFixedChargePressure_below_critical w tau⟩
  · intro hp
    have hc : Continuous (egbFixedChargePressure w) :=
      (show Differentiable ℝ (egbFixedChargePressure w) from
        fun tau => (egbFixedChargePressure_hasDerivAt w tau).differentiableAt).continuous
    have hlo : egbFixedChargePressure w ≤ᶠ[atTop] (fun _ => p) :=
      ((tendsto_order.mp (egbFixedChargePressure_cold_limit w)).2 p hp.1).mono (fun _ h => h.le)
    have hhi : (fun _ => p) ≤ᶠ[atBot] egbFixedChargePressure w :=
      ((tendsto_order.mp (egbFixedChargePressure_critical_limit w)).1 p hp.2).mono (fun _ h => h.le)
    exact intermediate_value_univ₂_eventually₂ hc continuous_const hlo hhi

/-- The same actual curve covers every positive subcritical temperature. -/
theorem egbFixedChargeTemperature_range (w : ℝ) :
    Set.range (egbFixedChargeTemperature w) = Set.Ioo 0 (1 / (3 * Real.pi * Real.exp w * Real.sqrt 6)) := by
  ext t
  constructor
  · rintro ⟨tau, rfl⟩
    exact ⟨egbCoexistenceTemperature_pos _ _, egbFixedChargeTemperature_below_critical w tau⟩
  · intro ht
    have hc : Continuous (egbFixedChargeTemperature w) :=
      (show Differentiable ℝ (egbFixedChargeTemperature w) from
        fun tau => (egbFixedChargeTemperature_hasDerivAt w tau).differentiableAt).continuous
    have hlo : egbFixedChargeTemperature w ≤ᶠ[atTop] (fun _ => t) :=
      ((tendsto_order.mp (egbFixedChargeTemperature_cold_limit w)).2 t ht.1).mono (fun _ h => h.le)
    have hhi : (fun _ => t) ≤ᶠ[atBot] egbFixedChargeTemperature w :=
      ((tendsto_order.mp (egbFixedChargeTemperature_critical_limit w)).1 t ht.2).mono (fun _ h => h.le)
    exact intermediate_value_univ₂_eventually₂ hc continuous_const hlo hhi

/-- Unique coexistence parameter at any positive subcritical pressure, encoded without a premise. -/
theorem egbFixedChargePressure_unique_parameter (w s : ℝ) :
    ∃! tau, egbFixedChargePressure w tau = thermalRatio s / (96 * Real.pi * Real.exp w ^ (2 : ℕ)) := by
  have hd : 0 < 96 * Real.pi * Real.exp w ^ (2 : ℕ) := by positivity
  have hp : thermalRatio s / (96 * Real.pi * Real.exp w ^ (2 : ℕ)) ∈
      Set.Ioo 0 (1 / (96 * Real.pi * Real.exp w ^ (2 : ℕ))) :=
    ⟨div_pos (thermalRatio_pos s) hd, (div_lt_div_iff_of_pos_right hd).mpr (thermalRatio_lt_one s)⟩
  rw [← egbFixedChargePressure_range w] at hp
  obtain ⟨tau, htau⟩ := hp
  exact ⟨tau, htau, fun y hy => (egbFixedChargePressure_strictAnti w).injective (hy.trans htau.symm)⟩

/-- Unique coexistence parameter at any positive subcritical temperature. -/
theorem egbFixedChargeTemperature_unique_parameter (w s : ℝ) :
    ∃! tau, egbFixedChargeTemperature w tau = thermalRatio s / (3 * Real.pi * Real.exp w * Real.sqrt 6) := by
  have hd : 0 < 3 * Real.pi * Real.exp w * Real.sqrt 6 := by positivity
  have ht : thermalRatio s / (3 * Real.pi * Real.exp w * Real.sqrt 6) ∈
      Set.Ioo 0 (1 / (3 * Real.pi * Real.exp w * Real.sqrt 6)) :=
    ⟨div_pos (thermalRatio_pos s) hd, (div_lt_div_iff_of_pos_right hd).mpr (thermalRatio_lt_one s)⟩
  rw [← egbFixedChargeTemperature_range w] at ht
  obtain ⟨tau, htau⟩ := ht
  exact ⟨tau, htau, fun y hy => (egbFixedChargeTemperature_strictAnti w).injective (hy.trans htau.symm)⟩

end GaloisForLFunctions.HTGeometry
