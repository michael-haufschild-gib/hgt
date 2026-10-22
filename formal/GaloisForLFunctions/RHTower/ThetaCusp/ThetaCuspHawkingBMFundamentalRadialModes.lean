import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalNormalizableDomain
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplacePowerLimits

/-! Elementary forms and exact normalization of both original fundamental radial modes. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem hypergeometric_zero_parameter (a b c z : ℂ) (h : a=0 ∨ b=0) :
    (ordinaryHypergeometricSeries ℂ a b c).sum z=1 := by
  rw [ordinaryHypergeometric_sum_eq,tsum_eq_single 0]
  · simp
  · intro n hn
    rcases h with rfl | rfl <;> simp [hn]

/-- At either fundamental resonance the complete outer Gauss series terminates at its constant term. -/
theorem gaussFactor_outer_fundamental (w chi z : ℂ)
    (hf : w=-3/2-I*chi ∨ w=-3/2+I*chi) : gaussFactor w chi true z=1 := by
  apply hypergeometric_zero_parameter
  rcases hf with rfl | rfl
  · right; unfold gaussC gaussB; ring
  · left; unfold gaussC gaussA; ring

/-- The original normalizable mode has its exact elementary fundamental value. -/
theorem normalizable_fundamental_value (w chi : ℂ)
    (hf : w=-3/2-I*chi ∨ w=-3/2+I*chi) (z : ℝ) :
    normalizable w chi z=power (w/2) z*power (1/2) (1-z) := by
  simp only [normalizable,dress,outerFactor,gaussFactor_outer_fundamental w chi _ hf,mul_one]

/-- The connection-zero horizon coefficient is exactly one in the original normalization. -/
theorem fundamental_horizonRegularCoefficient (w chi : ℂ) (hw : w.im ≠ 0)
    (hf : w=-3/2-I*chi ∨ w=-3/2+I*chi) :
    horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)=1 := by
  let A := horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)
  have hc : connection w chi=0 := by
    rcases hf with rfl | rfl
    · exact (connection_fundamental_zero chi).1
    · exact (connection_fundamental_zero chi).2
  have he (z : ℝ) (hz : z ∈ Ioo 0 1) :
      power (1/2) (1-z)=A*gaussFactor w chi false z := by
    have hh := (original_homogeneous_horizon_representation w chi hw
      (fun b hb => (normalizable_derivatives_continued hb).1)
      (fun b hb => (normalizable_derivatives_continued hb).2)
      (fun b hb => normalizable_equation_continued hb) hz).1
    rw [normalizable_opposite_coefficient w chi hw,hc,zero_div,zero_mul,add_zero,
      normalizable_fundamental_value w chi hf z] at hh
    dsimp only [horizon,dress] at hh
    apply mul_left_cancel₀ (power_ne_zero (w/2) hz.1)
    calc
      _ = A*(power (w/2) z*gaussFactor w chi false z) := hh
      _ = _ := by ring
  have hrev : Tendsto (fun z : ℝ => 1-z) (𝓝 (0:ℝ)) (𝓝 (1:ℝ)) := by
    simpa only [sub_zero] using (show Continuous (fun z : ℝ => 1-z) by fun_prop).tendsto (0:ℝ)
  have hleft : Tendsto (fun z : ℝ => power (1/2) (1-z)) (𝓝[>] (0:ℝ)) (𝓝 (1:ℂ)) :=
    ((power_tendsto_one (1/2)).comp hrev).mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun z : ℝ => A*gaussFactor w chi false z) (𝓝[>] (0:ℝ)) (𝓝 A) := by
    have hh := ((gaussFactor_right_contDiffAt w chi).continuousAt.tendsto.const_mul A).mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,gaussFactor_zero,mul_one] using hh
  have hevent : (fun z : ℝ => power (1/2) (1-z)) =ᶠ[𝓝[>] (0:ℝ)]
      fun z : ℝ => A*gaussFactor w chi false z := by
    have hlt : ∀ᶠ z : ℝ in 𝓝[>] (0:ℝ), z < 1 :=
      (show ∀ᶠ z : ℝ in 𝓝 0, z < 1 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hlt] with z hz hz1
    exact he z ⟨hz,hz1⟩
  exact (tendsto_nhds_unique hleft (hright.congr' hevent.symm)).symm

/-- Horizon and outer normalizations agree on the original radial interval at every nonreal fundamental mode. -/
theorem horizon_eq_normalizable_fundamental (w chi : ℂ) (hw : w.im ≠ 0)
    (hf : w=-3/2-I*chi ∨ w=-3/2+I*chi) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    horizon w chi z=normalizable w chi z := by
  have hh := (original_homogeneous_horizon_representation w chi hw
    (fun b hb => (normalizable_derivatives_continued hb).1)
    (fun b hb => (normalizable_derivatives_continued hb).2)
    (fun b hb => normalizable_equation_continued hb) hz).1
  have hc : connection w chi=0 := by
    rcases hf with rfl | rfl
    · exact (connection_fundamental_zero chi).1
    · exact (connection_fundamental_zero chi).2
  rw [fundamental_horizonRegularCoefficient w chi hw hf,normalizable_opposite_coefficient w chi hw,
    hc,zero_div,zero_mul,add_zero,one_mul] at hh
  exact hh.symm

/-- The fundamental horizon Gauss factor is the square-root factor, including its normalized endpoint. -/
theorem gaussFactor_horizon_fundamental (w chi : ℂ) (hw : w.im ≠ 0)
    (hf : w=-3/2-I*chi ∨ w=-3/2+I*chi) {z : ℝ} (hz : z ∈ Ico 0 1) :
    gaussFactor w chi false z=power (1/2) (1-z) := by
  rcases hz.1.eq_or_lt with he | hp
  · subst z; simp [power,gaussFactor_zero]
  · have hh := horizon_eq_normalizable_fundamental w chi hw hf ⟨hp,hz.2⟩
    rw [normalizable_fundamental_value w chi hf] at hh
    exact mul_left_cancel₀ (power_ne_zero (w/2) hp) hh

end
end RHTower.D4BMLaplaceRadial
