import GaloisForLFunctions.RHTower.DeningerMeyerXiGaussianSingularPoissonLift
import GaloisForLFunctions.RHTower.SuzukiAntiPickIdentity

/-!
# Exact Gamma residue of the Deninger--Meyer singular Green lift

The successor-pole theorem proves that completed Xi transport of the singular Meyer lift has one
simple pole.  This module computes its coefficient.  At an off-center strip point `rho`, the
normalized punctured limit is

`-2π archFactor(rho) / (χ_c(rho) (rho-c))`.

The coefficient is independent of Xi multiplicity and nonzero.  Any source-topological
continuation of the Möbius--Gaussian Neumann source must therefore land in the Gamma/co-Poisson
boundary with this exact normalization; multiplying local principal parts by arbitrary scalars is
not source-faithful.
-/

open Complex Filter Topology Set Metric
open scoped Real

namespace RHTower
namespace DeningerMeyerGaussianGreen

noncomputable section

/-- Residue limit before simplifying the derivative of the Gaussian denominator. -/
theorem tendsto_xi_mul_poissonGaussianSingularLift_residue
    {c rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hcr : rho ≠ c) :
    Tendsto
      (fun s => (s - rho) * (xi s * poissonGaussianSingularLift c rho s))
      (𝓝[≠] rho)
      (nhds (archFactor rho /
        (-(gaussianMellinCharacter c rho *
          ((rho - c) / (2 * (Real.pi : ℂ))))))) := by
  have harch : AnalyticAt ℂ archFactor rho := by
    have hpoly : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / 2) rho := by fun_prop
    exact hpoly.mul (Gammaℝ_analyticAt (Gammaℝ_ne_zero_of_re_pos hstrip.1))
  have hderivNe :
      -(gaussianMellinCharacter c rho *
        ((rho - c) / (2 * (Real.pi : ℂ)))) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (Complex.exp_ne_zero _)
      (div_ne_zero (sub_ne_zero.mpr hcr)
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
  have hres := tendsto_residue_of_simple_zero
    (hasDerivAt_gaussianResolventDenominator c rho)
    (gaussianResolventDenominator_self c rho) hderivNe harch.continuousAt
  apply hres.congr'
  filter_upwards [eventually_xi_mul_poissonGaussianSingularLift_eq_archFactor_mul_green
      hstrip hcr] with s hs
  rw [hs]
  rfl

/-- Closed formula for the universal simple Gamma/Green residue. -/
theorem xi_mul_poissonGaussianSingularLift_residue_eq_explicit
    {c rho : ℂ} (hcr : rho ≠ c) :
    archFactor rho /
        (-(gaussianMellinCharacter c rho *
          ((rho - c) / (2 * (Real.pi : ℂ))))) =
      -(2 * (Real.pi : ℂ) * archFactor rho /
        (gaussianMellinCharacter c rho * (rho - c))) := by
  have hchar : gaussianMellinCharacter c rho ≠ 0 := Complex.exp_ne_zero _
  field_simp [hchar, hcr, Real.pi_ne_zero]

/-- The completed Gamma/Green residue is nonzero throughout the off-center open strip. -/
theorem xi_mul_poissonGaussianSingularLift_residue_ne_zero
    {c rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hcr : rho ≠ c) :
    -(2 * (Real.pi : ℂ) * archFactor rho /
        (gaussianMellinCharacter c rho * (rho - c))) ≠ 0 := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact neg_ne_zero.mpr (div_ne_zero
    (mul_ne_zero (mul_ne_zero htwo hpi) (archFactor_ne_zero_strip hstrip))
    (mul_ne_zero (Complex.exp_ne_zero _) (sub_ne_zero.mpr hcr)))

end
end DeningerMeyerGaussianGreen
end RHTower
