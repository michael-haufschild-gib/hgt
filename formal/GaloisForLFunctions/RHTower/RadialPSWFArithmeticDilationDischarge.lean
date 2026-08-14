import GaloisForLFunctions.RHTower.RadialPSWFLeadingTightness
import GaloisForLFunctions.RHTower.ArcsineZetaDerivativeSpectrum

/-!
# Unconditional PSWF leading density limit to arithmetic eigenvalues

This module discharges the exact limiting arithmetic eigenvalue formula directly from the
asymptotic Dunster leading arclength density of the exterior radial prolate spheroidal wave
functions (PSWF).

1. **PSWF Leading Dilation Weight Limit**:
   $$\lim_{i} \frac{8}{11} \frac{1}{k} \int_{\sqrt{k^2-1}}^\infty \text{radialPSWFLeadingArclengthDensity}(c_i, \sigma_i, \theta, t) dt = \frac{8}{11\pi k} \arcsin\frac{1}{k}$$
2. **PSWF Arithmetic Eigenvalue Convergence**:
   $$\lim_{i} 2 \log(n+2) \left(\frac{8}{11(n+2)} \int_{\sqrt{(n+2)^2-1}}^\infty \text{density}_i(t) dt\right) = \kappa_{n+2} = \frac{16\log(n+2)}{11\pi(n+2)} \arcsin\frac{1}{n+2}$$
-/

open Filter MeasureTheory Set RHTower GaloisForLFunctions

namespace RHTower

/-- The exact convergence of the radial PSWF leading density integral to the arithmetic eigenvalue weight. -/
theorem tendsto_radialPSWF_leading_tail_to_arithmetic_weight
    {ι : Type*} {l : Filter ι} {c sigma : ι → ℝ} {theta k : ℝ}
    (hc : Tendsto c l atTop) (hsigma : Tendsto sigma l (nhds 0)) (hk : 1 ≤ k) :
    Tendsto (fun i => (8 / 11) * (1 / k) *
        ∫ t in Ioi (Real.sqrt (k ^ 2 - 1)),
          radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t)
      l (nhds ((8 / (11 * Real.pi * k)) * Real.arcsin (1 / k))) := by
  have h := tendsto_integral_Ioi_sqrt_sq_sub_one_radialPSWFLeadingArclengthDensity
    hc hsigma hk (theta := theta)
  have hmul := Tendsto.const_mul ((8 / 11) * (1 / k)) h
  have heq : ((8 / 11) * (1 / k)) * ((1 / Real.pi) * Real.arcsin (1 / k)) =
      (8 / (11 * Real.pi * k)) * Real.arcsin (1 / k) := by
    ring
  rw [heq] at hmul
  exact hmul

/-- The exact convergence of the full PSWF-weighted spectral density to the arithmetic eigenvalue. -/
theorem tendsto_radialPSWF_leading_tail_to_arithmetic_eigenvalue
    {ι : Type*} {l : Filter ι} {c sigma : ι → ℝ} {theta : ℝ} (n : ℕ)
    (hc : Tendsto c l atTop) (hsigma : Tendsto sigma l (nhds 0)) :
    Tendsto (fun i => 2 * Real.log ((n + 2 : ℕ) : ℝ) *
        ((8 / 11) * (1 / ((n + 2 : ℕ) : ℝ)) *
          ∫ t in Ioi (Real.sqrt (((n + 2 : ℕ) : ℝ) ^ 2 - 1)),
            radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t))
      l (nhds (constrainedProlateArithmeticEigenvalue n)) := by
  have hk : 1 ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n + 2)
  have hweight := tendsto_radialPSWF_leading_tail_to_arithmetic_weight hc hsigma hk (theta := theta)
  have heig := Tendsto.const_mul (2 * Real.log ((n + 2 : ℕ) : ℝ)) hweight
  have heq : 2 * Real.log ((n + 2 : ℕ) : ℝ) *
        ((8 / (11 * Real.pi * ((n + 2 : ℕ) : ℝ))) * Real.arcsin (1 / ((n + 2 : ℕ) : ℝ))) =
      constrainedProlateArithmeticEigenvalue n := by
    rw [constrainedProlateArithmeticEigenvalue_eq]
    ring
  rw [heq] at heig
  exact heig

end RHTower
