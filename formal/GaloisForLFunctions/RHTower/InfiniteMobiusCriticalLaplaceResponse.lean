import GaloisForLFunctions.RHTower.InfiniteMobiusLaplaceMultiplier
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Critical Laplace response of the all-prime Möbius channel

The normalized all-prime signed Möbius shift has the exact causal Laplace multiplier

`τ_σ(x) = ζ(2σ) / (ζ(σ) ζ(σ + πx))`

for `σ > 1` and `x > 0`.  The simple pole of `ζ` at `1` therefore supplies an unconditional
critical boundary response:

`τ_σ(x) / (σ - 1) → ζ(2) / ζ(1 + πx)` as `σ → 1+`.

The second theorem transports this scalar limit through every positive causal Laplace coordinate.
This closes the arithmetic distributional-limit part of the pole-to-divisor continuation route.
It does not construct the remaining charged archimedean continuation or prove RH.
-/

open Complex MeasureTheory Set Filter ArithmeticFunction LSeries
open scoped BigOperators LSeries.notation Moebius Topology

noncomputable section
namespace RHTower

/-- **Critical all-prime multiplier response.**  After division by the unique vanishing scale
`σ - 1`, the exact all-prime Möbius multiplier has a finite nonzero right boundary value. -/
theorem tendsto_infiniteMobiusLaplaceMultiplier_div_sub_one
    {x : ℝ} (hx : 0 < x) :
    Tendsto
      (fun sigma : ℝ =>
        infiniteMobiusLaplaceMultiplier sigma x / (sigma - 1))
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (2 : ℂ) /
        riemannZeta (((1 + Real.pi * x : ℝ) : ℂ)))) := by
  have hsigma : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have htwoArg : Tendsto (fun sigma : ℝ => 2 * (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hsigma :
      Tendsto (fun sigma : ℝ => (2 : ℂ) * (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 ((2 : ℂ) * 1)))
  have hnum : Tendsto (fun sigma : ℝ => riemannZeta (2 * (sigma : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp htwoArg
  have hresidue : Tendsto (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hsigma
  have hshiftArg : Tendsto
      (fun sigma : ℝ => ((sigma + Real.pi * x : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ))
      (𝓝 (((1 + Real.pi * x : ℝ) : ℂ))) := by
    simpa only [Complex.ofReal_add] using
      hsigma.add_const ((Real.pi * x : ℝ) : ℂ)
  have hshiftPoint : (((1 + Real.pi * x : ℝ) : ℂ)) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    nlinarith [Real.pi_pos]
  have hshift : Tendsto
      (fun sigma : ℝ => riemannZeta (((sigma + Real.pi * x : ℝ) : ℂ)))
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (((1 + Real.pi * x : ℝ) : ℂ)))) :=
    (differentiableAt_riemannZeta hshiftPoint).continuousAt.tendsto.comp hshiftArg
  have hshiftRe : 1 < (((1 + Real.pi * x : ℝ) : ℂ)).re := by
    simp only [ofReal_re]
    nlinarith [Real.pi_pos]
  have hlimit := hnum.div (hresidue.mul hshift)
    (mul_ne_zero one_ne_zero (riemannZeta_ne_zero_of_one_lt_re hshiftRe))
  simpa only [one_mul] using hlimit.congr' (by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigmaGt
    change 1 < sigma at hsigmaGt
    have hsigmaOne : sigma ≠ 1 := ne_of_gt hsigmaGt
    have hsigmaZeta : 1 < ((sigma : ℂ)).re := by simpa using hsigmaGt
    have htwoZeta : 1 < (2 * (sigma : ℂ)).re := by
      norm_num
      linarith
    have hshiftZeta : 1 < (((sigma + Real.pi * x : ℝ) : ℂ)).re := by
      simp only [ofReal_re]
      have hpix : 0 < Real.pi * x := mul_pos Real.pi_pos hx
      linarith
    rw [infiniteMobiusLaplaceMultiplier_eq_zetaRatio hsigmaGt hx.le]
    change riemannZeta (2 * (sigma : ℂ)) /
        (zetaResidueUnit (sigma : ℂ) *
          riemannZeta (((sigma + Real.pi * x : ℝ) : ℂ))) = _
    rw [zetaResidueUnit, Function.update_of_ne (by exact_mod_cast hsigmaOne)]
    field_simp [hsigmaOne,
      riemannZeta_ne_zero_of_one_lt_re hsigmaZeta,
      riemannZeta_ne_zero_of_one_lt_re htwoZeta,
      riemannZeta_ne_zero_of_one_lt_re hshiftZeta])

/-- **Critical weak response of the all-prime Möbius shift.**  Every positive causal Laplace
coordinate has the explicit residue-normalized boundary limit. -/
theorem tendsto_causalLaplacePairing_infiniteMobiusShiftAverage_div_sub_one
    {x : ℝ} (hx : 0 < x)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : HasAELowerSupport (fun t : ℝ => f t) 0) :
    Tendsto
      (fun sigma : ℝ =>
        causalLaplacePairing x hx (infiniteMobiusShiftAverage sigma f) /
          (sigma - 1))
      (𝓝[>] (1 : ℝ))
      (𝓝 ((riemannZeta (2 : ℂ) /
          riemannZeta (((1 + Real.pi * x : ℝ) : ℂ))) *
        causalLaplacePairing x hx f)) := by
  have hlimit :=
    (tendsto_infiniteMobiusLaplaceMultiplier_div_sub_one hx).mul_const
      (causalLaplacePairing x hx f)
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [causalLaplacePairing_infiniteMobiusShiftAverage hsigma hx f hf]
  ring

end RHTower
