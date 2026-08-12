import GaloisForLFunctions.RHTower.HedenmalmThetaPhysicalEndpointHardyGreenResidualBridge
import GaloisForLFunctions.RHTower.XiPrimeLogHigherValuationHalfPlane

/-!
# Route P prime-sampled Hardy--Green scaling

The physical endpoint marginal `log p / p` is the correct logarithmic-time sampling density for
the exceptional residual.  At centered depth `d > 0`, its sampled energy is exactly

`8 * sum_p log(p) * p^(-1 - 2d)`.

The prime logarithmic Dirichlet series has residue one at `s = 1`; consequently this energy has
critical asymptotic `4 / d`.  This agrees coefficient-for-coefficient with the continuous
half-line energy of the Route P residual.  Thus prime sampling does not merely detect the same
singularity class: it recovers the exact Hardy--Green leading energy.

This is an unconditional source/divisor bridge, not a four-unit bound.  As `d -> 0+`, both sides
blow up.  Any RH proof must cancel or exclude this residue by structure specific to theta,
entireness, or the pole order; a generic completed-response sign cannot do it.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Prime-sampled Hardy--Green residual energy at abstract centered depth `d`. -/
def thetaPhysicalEndpointPrimeHardyGreenEnergy (d : ℝ) : ℝ :=
  8 * ∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight d p

/-- Each physical prime sample is exactly the prime-square Euler weight at the copy's centered
depth, with the coefficient forced by the Hardy--Green normalization. -/
theorem physicalPrimeEndpointWeight_mul_hardyGreenResidual_sq
    (p : Nat.Primes) (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    physicalPrimeEndpointWeight p *
        thetaPhysicalEndpointHardyGreenResidual q (Real.log (p : ℝ)) ^ 2 =
      8 * xiMassPrimeSquareEulerWeight
        |primeDepthBVWoldXiCenteredRate q.1| p := by
  let d : ℝ := |primeDepthBVWoldXiCenteredRate q.1|
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [physicalPrimeEndpointWeight,
    thetaPhysicalEndpointHardyGreenResidual_at_prime_log p q h,
    xiMassPrimeSquareEulerWeight_eq]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : (p : ℝ)⁻¹ * ((p : ℝ) ^ (-d)) ^ 2 =
      (p : ℝ) ^ (-(1 + 2 * d)) := by
    rw [pow_two, ← Real.rpow_neg_one, ← Real.rpow_add hp, ← Real.rpow_add hp]
    congr 1
    ring
  change Real.log (p : ℝ) / (p : ℝ) *
      ((2 ^ 2 * 2) * ((p : ℝ) ^ (-d)) ^ 2) =
      8 * (Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d)))
  rw [show (2 : ℝ) ^ 2 * 2 = 8 by norm_num, div_eq_mul_inv, ← hpow]
  ring

/-- Off-center physical residual samples are summable for every fixed divisor copy. -/
theorem summable_physicalPrimeEndpointWeight_mul_hardyGreenResidual_sq
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    Summable (fun p : Nat.Primes =>
      physicalPrimeEndpointWeight p *
        thetaPhysicalEndpointHardyGreenResidual q (Real.log (p : ℝ)) ^ 2) := by
  exact ((summable_xiMassPrimeSquareEulerWeight (abs_pos.mpr h)).mul_left 8).congr
    (fun p => (physicalPrimeEndpointWeight_mul_hardyGreenResidual_sq p q h).symm)

/-- Divisor-indexed version of the sampled residual energy. -/
def thetaPhysicalEndpointSampledHardyGreenResidualEnergy (q : XiZeroCopy) : ℝ :=
  ∑' p : Nat.Primes, physicalPrimeEndpointWeight p *
    thetaPhysicalEndpointHardyGreenResidual q (Real.log (p : ℝ)) ^ 2

/-- Exact reduction of a nonneutral divisor copy to the abstract prime-depth energy. -/
theorem thetaPhysicalEndpointSampledHardyGreenResidualEnergy_eq
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    thetaPhysicalEndpointSampledHardyGreenResidualEnergy q =
      thetaPhysicalEndpointPrimeHardyGreenEnergy
        |primeDepthBVWoldXiCenteredRate q.1| := by
  rw [thetaPhysicalEndpointSampledHardyGreenResidualEnergy,
    thetaPhysicalEndpointPrimeHardyGreenEnergy, ← tsum_mul_left]
  exact tsum_congr (fun p =>
    physicalPrimeEndpointWeight_mul_hardyGreenResidual_sq p q h)

/-- For positive depth, the real prime energy is exactly the real part of the prime logarithmic
Dirichlet series on the ray `s = 1 + 2d`. -/
theorem tsum_xiMassPrimeSquareEulerWeight_eq_re_xiPrimeLogDirichlet
    (d : ℝ) (hd : 0 < d) :
    (∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight d p) =
      (xiPrimeLogDirichlet ((1 + 2 * d : ℝ) : ℂ)).re := by
  have hs : (1 : ℝ) < 1 + 2 * d := by linarith
  rw [xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow (by simpa using hs)]
  rw [Complex.re_tsum]
  · apply tsum_congr
    intro p
    rw [xiMassPrimeSquareEulerWeight_eq]
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hpow : ((p : ℂ) ^ (((1 + 2 * d : ℝ) : ℂ))) =
        (((p : ℝ) ^ (1 + 2 * d) : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_cpow hp0 (1 + 2 * d)).symm
    rw [hpow]
    norm_cast
    rw [div_eq_mul_inv, ← Real.rpow_neg hp0]
  · exact (summable_xiPrimeLogDirichlet_term (by simpa using hs)).congr
      (fun p => xiPrimeLogDirichlet_term_eq _ p)

theorem thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_primeLogDirichlet
    (d : ℝ) (hd : 0 < d) :
    thetaPhysicalEndpointPrimeHardyGreenEnergy d =
      8 * (xiPrimeLogDirichlet ((1 + 2 * d : ℝ) : ℂ)).re := by
  rw [thetaPhysicalEndpointPrimeHardyGreenEnergy,
    tsum_xiMassPrimeSquareEulerWeight_eq_re_xiPrimeLogDirichlet d hd]

/-- Residue-one law for the prime logarithmic Dirichlet series along the physical depth ray. -/
theorem tendsto_two_mul_depth_mul_xiPrimeLogDirichlet_one_add_two_mul_depth :
    Tendsto (fun d : ℝ => ((2 * d : ℝ) : ℂ) *
      xiPrimeLogDirichlet ((1 + 2 * d : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
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
  have hscale : Tendsto (fun d : ℝ => ((2 * d : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hscaleR : Tendsto (fun d : ℝ => 2 * d)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hbase.const_mul 2
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hscaleR
  have hzero := hscale.mul (hreg.sub hhigh)
  have hzero' : Tendsto (fun d : ℝ => ((2 * d : ℝ) : ℂ) *
      (RHTower.Sieve.zetaLogDerivReg ((1 + 2 * d : ℝ) : ℂ) -
        xiPrimeLogHigherValuation ((1 + 2 * d : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hzero
  have hlimit : Tendsto (fun d : ℝ => (1 : ℂ) +
      ((2 * d : ℝ) : ℂ) *
        (RHTower.Sieve.zetaLogDerivReg ((1 + 2 * d : ℝ) : ℂ) -
          xiPrimeLogHigherValuation ((1 + 2 * d : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.add hzero'
  refine hlimit.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  change 0 < d at hd
  have hs : (1 : ℝ) < 1 + 2 * d := by linarith
  rw [xiPrimeLogDirichlet_eq_pole_add_regular_sub_higherValuation
    (by simpa using hs)]
  have hd0 : (((2 * d : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hd.ne')
  have hpole : (((2 * d : ℝ) : ℂ)) *
      (((((1 + 2 * d : ℝ) : ℂ)) - 1)⁻¹) = 1 := by
    have hden : ((((1 + 2 * d : ℝ) : ℂ)) - 1) =
        (((2 * d : ℝ) : ℂ)) := by push_cast; ring
    rw [hden, mul_inv_cancel₀ hd0]
  conv_rhs => rw [mul_sub, mul_add, hpole]
  ring

/-- Exact critical coefficient: prime-sampled residual energy is asymptotic to `4 / d`. -/
theorem tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy :
    Tendsto (fun d : ℝ =>
      d * thetaPhysicalEndpointPrimeHardyGreenEnergy d)
      (𝓝[>] (0 : ℝ)) (𝓝 4) := by
  have hcomplex :=
    tendsto_two_mul_depth_mul_xiPrimeLogDirichlet_one_add_two_mul_depth
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  have heq :
      (fun d : ℝ => d * thetaPhysicalEndpointPrimeHardyGreenEnergy d) =ᶠ[𝓝[>] 0]
        fun d => 4 * (((2 * d : ℝ) : ℂ) *
          xiPrimeLogDirichlet ((1 + 2 * d : ℝ) : ℂ)).re := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    change 0 < d at hd
    rw [thetaPhysicalEndpointPrimeHardyGreenEnergy,
      tsum_xiMassPrimeSquareEulerWeight_eq_re_xiPrimeLogDirichlet d hd]
    simp
    ring
  have hfour : Tendsto (fun d : ℝ => 4 *
      ((((2 * d : ℝ) : ℂ) *
        xiPrimeLogDirichlet ((1 + 2 * d : ℝ) : ℂ))).re)
      (𝓝[>] (0 : ℝ)) (𝓝 4) := by
    simpa only [Function.comp_apply, Complex.one_re, mul_one] using hre.const_mul 4
  exact hfour.congr' heq.symm

/-- Ratio form of the coefficient match with continuous energy `4 / d`. -/
theorem tendsto_normalized_thetaPhysicalEndpointPrimeHardyGreenEnergy :
    Tendsto (fun d : ℝ =>
      (d / 4) * thetaPhysicalEndpointPrimeHardyGreenEnergy d)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h :=
    tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy.const_mul (1 / 4 : ℝ)
  rw [show (fun d : ℝ =>
      (d / 4) * thetaPhysicalEndpointPrimeHardyGreenEnergy d) =
      fun d : ℝ => (1 / 4) *
        (d * thetaPhysicalEndpointPrimeHardyGreenEnergy d) by
      funext d
      ring]
  simpa using h

end

end RHTower.HedenmalmThetaSource
