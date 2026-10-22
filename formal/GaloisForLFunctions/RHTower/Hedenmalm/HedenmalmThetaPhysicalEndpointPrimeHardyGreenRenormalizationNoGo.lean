import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPhysicalEndpointPrimeHardyGreenScaling

/-!
# Route P prime Hardy--Green renormalization no-go

The P-G30 sampled energy has an exact pole-plus-regular decomposition.  Its `4 / d` principal
term is the continuous exceptional Hardy--Green energy, while the discrepancy extends
continuously to the critical wall and is given by the regular zeta contribution minus all higher
prime valuations.

More strongly, coefficient four is uniquely forced if a scalar `c / d` counterterm is to remove
the scaled pole.  But that unique subtraction works for every abstract positive depth approaching
zero and leaves a finite limit.  Principal Hardy--Green renormalization therefore cannot select
neutrality: it either fails to cancel the universal pole or cancels it for all nearby off-wall
depths.  A Route P producer must act before this scalar principal quotient or use additional
theta-entire structure.
-/

open Complex Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Finite prime/continuous Hardy--Green anomaly after removing the universal pole. -/
def thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly (d : ℝ) : ℝ :=
  8 * (RHTower.Sieve.zetaLogDerivReg ((1 + 2 * d : ℝ) : ℂ) -
    xiPrimeLogHigherValuation ((1 + 2 * d : ℝ) : ℂ)).re

/-- Exact pole-plus-regular decomposition at every positive depth. -/
theorem thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_four_div_add_regularAnomaly
    (d : ℝ) (hd : 0 < d) :
    thetaPhysicalEndpointPrimeHardyGreenEnergy d =
      4 / d + thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly d := by
  rw [thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_primeLogDirichlet d hd,
    xiPrimeLogDirichlet_eq_pole_add_regular_sub_higherValuation
      (show (1 : ℝ) < 1 + 2 * d by linarith)]
  have hd0 : d ≠ 0 := hd.ne'
  unfold thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly
  have hpole : (((((1 + 2 * d : ℝ) : ℂ)) - 1)⁻¹).re = 1 / (2 * d) := by
    have hden : ((((1 + 2 * d : ℝ) : ℂ)) - 1) =
        (((2 * d : ℝ) : ℂ)) := by push_cast; ring
    rw [hden]
    norm_cast
    rw [div_eq_mul_inv]
    simp
  rw [Complex.sub_re, Complex.add_re, hpole]
  simp only [Complex.sub_re]
  field_simp
  ring

/-- The finite anomaly extends continuously to the critical wall. -/
theorem tendsto_thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly :
    Tendsto thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly
      (𝓝[>] (0 : ℝ))
      (𝓝 (8 * (RHTower.Sieve.zetaLogDerivReg 1 -
        xiPrimeLogHigherValuation 1).re)) := by
  change Tendsto (fun d : ℝ =>
      8 * (RHTower.Sieve.zetaLogDerivReg ((1 + 2 * d : ℝ) : ℂ) -
        xiPrimeLogHigherValuation ((1 + 2 * d : ℝ) : ℂ)).re)
      (𝓝[>] (0 : ℝ))
      (𝓝 (8 * (RHTower.Sieve.zetaLogDerivReg 1 -
        xiPrimeLogHigherValuation 1).re))
  have hbase : Tendsto (fun d : ℝ => d)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hmapR : Tendsto (fun d : ℝ => 1 + 2 * d)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hbase.const_mul 2)
  have hmap : Tendsto (fun d : ℝ => ((1 + 2 * d : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hmapR
  have hreg : Tendsto (fun d : ℝ =>
      RHTower.Sieve.zetaLogDerivReg ((1 + 2 * d : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (RHTower.Sieve.zetaLogDerivReg 1)) :=
    RHTower.Sieve.differentiableAt_zetaLogDerivReg_one.continuousAt.tendsto.comp hmap
  have hhigh : Tendsto (fun d : ℝ =>
      xiPrimeLogHigherValuation ((1 + 2 * d : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (xiPrimeLogHigherValuation 1)) :=
    (differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re
      (s := (1 : ℂ)) (by norm_num)).continuousAt.tendsto.comp hmap
  have hre := Complex.continuous_re.continuousAt.tendsto.comp (hreg.sub hhigh)
  simpa only [Function.comp_apply] using hre.const_mul 8

/-- Subtracting the continuous `4 / d` energy leaves exactly the finite wall anomaly. -/
theorem tendsto_thetaPhysicalEndpointPrimeHardyGreenEnergy_sub_four_div :
    Tendsto (fun d : ℝ =>
      thetaPhysicalEndpointPrimeHardyGreenEnergy d - 4 / d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (8 * (RHTower.Sieve.zetaLogDerivReg 1 -
        xiPrimeLogHigherValuation 1).re)) := by
  refine tendsto_thetaPhysicalEndpointPrimeHardyGreenRegularAnomaly.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  change 0 < d at hd
  rw [thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_four_div_add_regularAnomaly d hd]
  ring

/-- Scaled residue left by an arbitrary scalar Hardy--Green counterterm. -/
theorem tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy_sub_counterterm
    (c : ℝ) :
    Tendsto (fun d : ℝ => d *
      (thetaPhysicalEndpointPrimeHardyGreenEnergy d - c / d))
      (𝓝[>] (0 : ℝ)) (𝓝 (4 - c)) := by
  have h := tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy.sub_const c
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  change 0 < d at hd
  field_simp [hd.ne']

/-- Coefficient four is uniquely forced by principal pole cancellation. -/
theorem thetaPhysicalEndpointPrimeHardyGreen_counterterm_cancels_iff
    (c : ℝ) :
    Tendsto (fun d : ℝ => d *
      (thetaPhysicalEndpointPrimeHardyGreenEnergy d - c / d))
      (𝓝[>] (0 : ℝ)) (𝓝 0) ↔ c = 4 := by
  constructor
  · intro hzero
    have hlimit :=
      tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy_sub_counterterm c
    have heq : (0 : ℝ) = 4 - c := tendsto_nhds_unique hzero hlimit
    linarith
  · rintro rfl
    simpa using
      tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy_sub_counterterm 4

end

end RHTower.HedenmalmThetaSource
