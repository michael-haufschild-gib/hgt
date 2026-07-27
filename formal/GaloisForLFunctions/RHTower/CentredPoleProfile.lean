import GaloisForLFunctions.HTGeometry.CentredPoleProfileIntegral
import GaloisForLFunctions.RHTower.GammaCriticalConstant

/-!
# The critical centred-pole profile

The scaled limit of a simple Dirichlet pole seen through a first logarithmic moment is the centred
double pole `w^(-2) - w^(-1)` at `w = 1/2 - i y`.  Its imaginary part is the rational profile
`y (3/4 - y²)/(y² + 1/4)²`, and its energy is the universal number

```text
∫_ℝ (Im [(1/2 - i y)^(-2) - (1/2 - i y)^(-1)])² dy = π .
```

This is the third factor of the residue--density--profile law: the critical constant is
`(pole residue) × (archimedean spectral density at zero) × (centred-pole profile energy)`.
-/

namespace RHTower

noncomputable section

/-- Imaginary part of the centred double pole on the critical vertical line. -/
def criticalPoleProfile (y : ℝ) : ℝ :=
  ((((1 : ℂ) / 2 - (y : ℂ) * Complex.I)⁻¹) ^ 2 - (((1 : ℂ) / 2 - (y : ℂ) * Complex.I)⁻¹)).im

/-- The centred double pole has the rational imaginary part `y (3/4 - y²)/(y² + 1/4)²`. -/
theorem criticalPoleProfile_eq (y : ℝ) : criticalPoleProfile y = HTGeometry.poleProfile y := by
  have hR : (0 : ℝ) < y ^ 2 + 1 / 4 := by positivity
  have hre : ((1 : ℂ) / 2 - (y : ℂ) * Complex.I).re = 1 / 2 := by simp
  have him : ((1 : ℂ) / 2 - (y : ℂ) * Complex.I).im = -y := by simp
  have hns : Complex.normSq ((1 : ℂ) / 2 - (y : ℂ) * Complex.I) = y ^ 2 + 1 / 4 := by
    rw [Complex.normSq_apply, hre, him]
    ring
  rw [criticalPoleProfile, Complex.sub_im, sq, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    hre, him, hns, HTGeometry.poleProfile]
  field_simp
  ring

/-- **The centred-pole profile energy.**  `∫_ℝ (Im [(1/2 - iy)^(-2) - (1/2 - iy)^(-1)])² dy = π`. -/
theorem integral_criticalPoleProfile_sq : ∫ y : ℝ, criticalPoleProfile y ^ 2 = Real.pi := by
  simp only [criticalPoleProfile_eq]
  exact HTGeometry.integral_poleProfile_sq

/-- **Residue--density--profile law with the profile in integral form.**  The critical constant is
the squarefree pole residue `1/ζ(2)` times the archimedean spectral density at zero times the
energy of the centred-pole profile. -/
theorem gammaCriticalConstant_eq_profileEnergy :
    gammaCriticalConstant
      = 2 * Real.sqrt 2 * gammaCyclicDensityZero *
          (∫ y : ℝ, criticalPoleProfile y ^ 2) / (riemannZeta 2).re := by
  rw [integral_criticalPoleProfile_sq]
  exact gammaCriticalConstant_eq_residueDensityProfile

end

end RHTower
