import GaloisForLFunctions.RHTower.ExponentialPrimitiveCancellation
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompressionRHCriterion

/-!
# Leading cancellation in the literal Weil pole matrix

The prime number theorem passes through the exact logarithmic Chebyshev
primitive. Both entries of the actual pole matrix, and both parity energies,
are little-o of exp(2a). The sign of the smaller remainder is not asserted.
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

theorem tendsto_ccmLogChebyshevDeficitPrimitive_scaled_zero :
    Tendsto (fun t => Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t) atTop (nhds 0) := by
  apply tendsto_exp_neg_mul_primitive_zero
  · intro a b
    exact (Real.continuous_exp.intervalIntegrable a b).sub
      ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable)
  · have hp : Tendsto (fun t => Chebyshev.psi (Real.exp t) / Real.exp t) atTop (nhds 1) := by
      have hident (x : ℝ) : chebyshevPsiReal x = Chebyshev.psi x := by
        rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_Icc]
        congr 1
        ext n
        simp
      simpa only [Function.comp_def, hident] using
        tendsto_chebyshevPsiReal_div.comp Real.tendsto_exp_atTop
    have h := tendsto_const_nhds.sub hp (a := (1 : ℝ))
    simp only [sub_self] at h
    refine h.congr fun t => ?_
    rw [Real.exp_neg]
    field_simp

private theorem aperture_val_tendsto :
    Tendsto (fun a : SuzukiPositiveAperture => a.1) atTop atTop :=
  tendsto_Ioi_atTop.mp tendsto_id

private theorem aperture_twice_tendsto :
    Tendsto (fun a : SuzukiPositiveAperture => 2 * a.1) atTop atTop :=
  aperture_val_tendsto.const_mul_atTop two_pos

theorem tendsto_ccmPoleIntegratedChebyshevDeficit_scaled_zero :
    Tendsto (fun a : SuzukiPositiveAperture =>
      Real.exp (-(2 * a.1)) * ccmPoleIntegratedChebyshevDeficit a) atTop (nhds 0) := by
  simpa only [Function.comp_def, ccmPoleIntegratedChebyshevDeficit_eq_logPrimitive] using
    tendsto_ccmLogChebyshevDeficitPrimitive_scaled_zero.comp aperture_twice_tendsto

theorem tendsto_ccmWeilPoleCross_scaled_zero :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp (-(2 * a.1)) * ccmWeilPoleCross a)
      atTop (nhds 0) := by
  let B := 2 * Real.log 2 + Real.pi + 1
  let K := |-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| + Real.log 4 + 5
  have hD : Tendsto (fun a : SuzukiPositiveAperture =>
      Real.exp (-(2 * a.1)) * |ccmPoleIntegratedChebyshevDeficit a|) atTop (nhds 0) := by
    simpa only [abs_mul, abs_of_pos (Real.exp_pos _), abs_zero] using
      tendsto_ccmPoleIntegratedChebyshevDeficit_scaled_zero.abs
  have hE := Real.tendsto_exp_neg_atTop_nhds_zero.comp aperture_twice_tendsto
  have hA : Tendsto (fun a : SuzukiPositiveAperture =>
      (2 * a.1) * Real.exp (-(2 * a.1))) atTop (nhds 0) := by
    simpa only [Function.comp_def, pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp aperture_twice_tendsto
  have hbound : Tendsto (fun a : SuzukiPositiveAperture =>
      Real.exp (-(2 * a.1)) * |ccmPoleIntegratedChebyshevDeficit a| +
        ((B + 1) * Real.exp (-(2 * a.1)) + K * ((2 * a.1) * Real.exp (-(2 * a.1)))))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using
      hD.add ((hE.const_mul (B + 1)).add (hA.const_mul K))
  apply squeeze_zero_norm _ hbound
  intro a
  have hb := abs_integratedChebyshevDeficit_sub_weilPoleCross_le a
  have hboundary := ccmGammaPoleCrossBoundaryMass_le a
  have hx : |ccmWeilPoleCross a| ≤ |ccmPoleIntegratedChebyshevDeficit a| + B + K * (2 * a.1) + 1 := by
    have ht := abs_add_le (ccmPoleIntegratedChebyshevDeficit a)
      (ccmWeilPoleCross a - ccmPoleIntegratedChebyshevDeficit a)
    rw [show ccmPoleIntegratedChebyshevDeficit a +
      (ccmWeilPoleCross a - ccmPoleIntegratedChebyshevDeficit a) = ccmWeilPoleCross a by ring,
      abs_sub_comm] at ht
    dsimp only [B, K]
    linarith only [hb, hboundary, ht]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hs := mul_le_mul_of_nonneg_left hx (Real.exp_pos (-(2 * a.1))).le
  nlinarith only [hs]

theorem tendsto_ccmWeilPoleDiagonal_scaled_zero :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp (-(2 * a.1)) * ccmWeilPoleDiagonal a)
      atTop (nhds 0) := by
  have hbound : Tendsto (fun a : SuzukiPositiveAperture =>
      ccmWeilPoleUniformDiagonalBound * Real.exp (-a.1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp aperture_val_tendsto).const_mul
        ccmWeilPoleUniformDiagonalBound
  apply squeeze_zero_norm _ hbound
  intro a
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(2 * a.1)) * (ccmWeilPoleUniformDiagonalBound * Real.exp a.1) :=
      mul_le_mul_of_nonneg_left (abs_ccmWeilPoleDiagonal_le a) (Real.exp_pos _).le
    _ = ccmWeilPoleUniformDiagonalBound * Real.exp (-a.1) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring

/-- Both actual parity energies lose their exp(2a) leading order unconditionally. -/
theorem tendsto_ccmWeilParityPole_scaled_zero (r : ℝ) (hr : r = 1 ∨ r = -1) :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp (-(2 * a.1)) *
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r)) atTop (nhds 0) := by
  have h := (tendsto_ccmWeilPoleDiagonal_scaled_zero.add
    (tendsto_ccmWeilPoleCross_scaled_zero.const_mul r)).const_mul 2
  simp only [mul_zero, add_zero] at h
  refine h.congr fun a => ?_
  rw [ccmWeilPoleCompression_parity_energy a hr]
  ring

end RHTower
