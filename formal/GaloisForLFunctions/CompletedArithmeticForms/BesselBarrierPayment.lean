import GaloisForLFunctions.CompletedArithmeticForms.BesselSpectralBand

/-!
# An argument-derivative reserve for the physical Schläfli source

Comparison with the decaying barrier `exp(-x)/x` bounds the negative argument
derivative of the actual imaginary-order Bessel function on its nonoscillatory
band. The bound pays the signed Bessel combination of a reflected theta atom.
-/

noncomputable section

open Complex Set Filter Topology

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry

/-- The literal Schläfli function vanishes at large argument for every fixed order. -/
theorem tendsto_modifiedBesselKOrder_arg_zero (ν : ℂ) :
    Tendsto (fun x : ℝ => modifiedBesselKOrder x ν) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ => Real.exp (1 - x) * besselOrderUnitMass ν)
      atTop (𝓝 0) := by
    simp_rw [Real.exp_sub]
    simpa only [div_eq_mul_inv, ← Real.exp_neg, zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (Real.exp 1)).mul_const
        (besselOrderUnitMass ν)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact norm_modifiedBesselKOrder_le_exp hx ν

/-- Wronskian against `exp(-x)/x`, expressed through the literal argument system. -/
def besselBarrierFlux (ν : ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-x) : ℂ) *
    ((1 + (ν + 1) / x) * modifiedBesselKOrder x ν - modifiedBesselKOrder x (ν + 1))

theorem besselBarrierFlux_eq (ν : ℂ) (x : ℝ) :
    besselBarrierFlux ν x = (Real.exp (-x) : ℂ) *
      (besselArgDeriv ν x + (1 + 1 / (x : ℂ)) * modifiedBesselKOrder x ν) := by
  unfold besselBarrierFlux besselArgDeriv
  congr 1
  rw [add_div]
  ring

/-- Exact barrier flux derivative, with every order and inverse-argument term retained. -/
theorem hasDerivAt_besselBarrierFlux {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    HasDerivAt (besselBarrierFlux ν)
      (-(Real.exp (-x) : ℂ) * (1 / (x : ℂ) + (1 - ν ^ 2) / (x : ℂ) ^ 2) *
        modifiedBesselKOrder x ν) x := by
  have hf := hasDerivAt_modifiedBesselKOrder_arg hx ν
  have hg := hasDerivAt_modifiedBesselKOrder_arg_succ hx ν
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hcoef := ((hasDerivAt_const x (ν + 1)).div hid hxC).const_add 1
  have hexp := ((hasDerivAt_id x).neg.exp).ofReal_comp
  have h : HasDerivAt (besselBarrierFlux ν) _ x := hexp.mul ((hcoef.mul hf).sub hg)
  refine h.congr_deriv ?_
  push_cast
  field_simp
  ring

/-- No asymptotic premise is needed for the barrier flux at infinity. -/
theorem tendsto_besselBarrierFlux_zero (ν : ℂ) :
    Tendsto (besselBarrierFlux ν) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => ((x : ℂ))⁻¹) atTop (𝓝 0) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
    simpa only [Complex.ofReal_inv, Complex.ofReal_zero] using h
  have he : Tendsto (fun x : ℝ => (Real.exp (-x) : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        Real.tendsto_exp_neg_atTop_nhds_zero
  have hc : Tendsto (fun x : ℝ => 1 + (ν + 1) / (x : ℂ)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      tendsto_const_nhds.add (hinv.const_mul (ν + 1))
  have h := he.mul ((hc.mul (tendsto_modifiedBesselKOrder_arg_zero ν)).sub
    (tendsto_modifiedBesselKOrder_arg_zero (ν + 1)))
  simpa only [besselBarrierFlux, mul_zero, sub_zero] using h

end GaloisForLFunctions.CompletedArithmeticForms
