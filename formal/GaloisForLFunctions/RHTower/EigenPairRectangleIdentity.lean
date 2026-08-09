import GaloisForLFunctions.RHTower.RectangleCauchyFormula
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.Reflection

/-!
# The fixed-aperture rectangle identity for the single-pole eigen integrand

The single-pole form of the eigen-pair contour integrand is `deriv XiC · (sharp F) / (z − p)`
with an entire numerator: the derivative of the entire `XiC` times the Schwarz reflection of an
entire test.  The corpus's rectangle Cauchy formula therefore evaluates its boundary integral at
any fixed aperture to `2πi` times the numerator's value at the pole — the antidiagonal Gram
datum of the eigen-pair identification.
-/

namespace RHTower

noncomputable section

open Complex

/-- The sharp (Schwarz reflection) of an entire function is entire. -/
theorem xiWeilSharp_analyticOnNhd {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    AnalyticOnNhd ℂ (xiWeilSharp F) Set.univ := by
  have hd : Differentiable ℂ (xiWeilSharp F) := by
    have h := differentiable_conj_reflect hF
    exact h
  exact hd.differentiableOn.analyticOnNhd isOpen_univ

/-- **Fixed-aperture rectangle identity for the single-pole eigen integrand.**  For entire `F`
and a pole `p` strictly inside the rectangle, the boundary integral of
`deriv XiC · sharp F / (z − p)` is `2πi` times the numerator's value at `p`. -/
theorem rectIntegral_singlePole_eigen {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {p z₁ z₂ : ℂ}
    (hre₁ : z₁.re < p.re) (hre₂ : p.re < z₂.re)
    (him₁ : z₁.im < p.im) (him₂ : p.im < z₂.im) :
    rectIntegral (fun z => deriv XiC z * xiWeilSharp F z * (z - p)⁻¹) z₁ z₂ =
      2 * Real.pi * Complex.I * (deriv XiC p * xiWeilSharp F p) := by
  have hXi : AnalyticOnNhd ℂ XiC Set.univ := fun z hz => XiC_analytic z hz
  have hg : AnalyticOnNhd ℂ (fun z => deriv XiC z * xiWeilSharp F z) Set.univ :=
    hXi.deriv.mul (xiWeilSharp_analyticOnNhd hF)
  exact rectIntegral_cauchyFormula_entire hg hre₁ hre₂ him₁ him₂

end

end RHTower
