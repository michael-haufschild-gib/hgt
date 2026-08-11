import GaloisForLFunctions.HTGeometry.MeromorphicEllipticGamma
import GaloisForLFunctions.HTGeometry.EllipticGammaConeOrder

/-!
# The two presentations of the elliptic gamma function agree

The meromorphic-field presentation builds the elliptic gamma function from the multiplicative
coordinate `x = -e(τ/2)e(z)` and the nomes `e(σ)`, `e(τ)`; the divisor presentation builds it from
the additive exponential cone product.  The two agree after the half-period shift `τ/2 + 1/2` that
relates the coordinates: factor by factor, hence product by product.

* `ellipticGammaForwardProduct_eq_coneProduct`, `ellipticGammaBackwardProduct_eq_coneProduct`;
* `ellipticGammaCone_shift_eq`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The coordinate shift relating the two presentations. -/
def gammaPresentationShift (τ : ℂ) : ℂ := τ / 2 + 1 / 2

theorem neg_one_eq_exp_pi_mul_I : (-1 : ℂ) = Complex.exp (Real.pi * Complex.I) :=
  Complex.exp_pi_mul_I.symm

/-- The numerator factors of the two presentations agree after the shift. -/
theorem ellipticGammaForwardFactor_eq_coneFactor (σ τ : ℂ) (jk : ℕ × ℕ) (z : ℂ) :
    ellipticGammaForwardFactor σ τ jk z
      = coneFactor σ τ jk (σ + τ - gammaPresentationShift τ - z) := by
  have hτ2 : Complex.exp (Real.pi * Complex.I * τ) ≠ 0 := Complex.exp_ne_zero _
  have hz : Complex.exp (2 * Real.pi * Complex.I * z) ≠ 0 := Complex.exp_ne_zero _
  simp only [ellipticGammaForwardFactor, ellipticGammaForwardArgument, ellipticNome,
    ellipticThetaCoordinate, coneFactor, expChar, gammaPresentationShift,
    ← Complex.exp_nat_mul]
  congr 1
  rw [div_eq_iff (by simp [hτ2, hz])]
  rw [show -Complex.exp (Real.pi * Complex.I * τ) * Complex.exp (2 * Real.pi * Complex.I * z)
      = Complex.exp (Real.pi * Complex.I) * Complex.exp (Real.pi * Complex.I * τ)
        * Complex.exp (2 * Real.pi * Complex.I * z) by
    rw [← neg_one_eq_exp_pi_mul_I]
    ring]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The denominator factors of the two presentations agree after the shift. -/
theorem ellipticGammaBackwardFactor_eq_coneFactor (σ τ : ℂ) (jk : ℕ × ℕ) (z : ℂ) :
    ellipticGammaBackwardFactor σ τ jk z
      = coneFactor σ τ jk (z + gammaPresentationShift τ) := by
  simp only [ellipticGammaBackwardFactor, ellipticGammaBackwardArgument, ellipticNome,
    ellipticThetaCoordinate, coneFactor, expChar, gammaPresentationShift,
    ← Complex.exp_nat_mul]
  congr 1
  rw [show Complex.exp ((jk.1 : ℂ) * (2 * Real.pi * Complex.I * σ))
        * Complex.exp ((jk.2 : ℂ) * (2 * Real.pi * Complex.I * τ))
        * (-Complex.exp (Real.pi * Complex.I * τ) * Complex.exp (2 * Real.pi * Complex.I * z))
      = Complex.exp ((jk.1 : ℂ) * (2 * Real.pi * Complex.I * σ))
        * Complex.exp ((jk.2 : ℂ) * (2 * Real.pi * Complex.I * τ))
        * (Complex.exp (Real.pi * Complex.I) * Complex.exp (Real.pi * Complex.I * τ)
          * Complex.exp (2 * Real.pi * Complex.I * z)) by
    rw [← neg_one_eq_exp_pi_mul_I]
    ring]
  simp only [← Complex.exp_add]
  congr 1
  ring

theorem ellipticGammaForwardProduct_eq_coneProduct (σ τ z : ℂ) :
    ellipticGammaForwardProduct σ τ z
      = coneProduct σ τ (σ + τ - gammaPresentationShift τ - z) := by
  rw [ellipticGammaForwardProduct, coneProduct]
  exact tprod_congr fun jk ↦ ellipticGammaForwardFactor_eq_coneFactor σ τ jk z

theorem ellipticGammaBackwardProduct_eq_coneProduct (σ τ z : ℂ) :
    ellipticGammaBackwardProduct σ τ z = coneProduct σ τ (z + gammaPresentationShift τ) := by
  rw [ellipticGammaBackwardProduct, coneProduct]
  exact tprod_congr fun jk ↦ ellipticGammaBackwardFactor_eq_coneFactor σ τ jk z

/-- **The two presentations of the elliptic gamma function agree after the coordinate shift.** -/
theorem ellipticGammaCone_shift_eq (σ τ z : ℂ) :
    ellipticGammaCone σ τ (z + gammaPresentationShift τ)
      = ellipticGammaForwardProduct σ τ z / ellipticGammaBackwardProduct σ τ z := by
  rw [ellipticGammaForwardProduct_eq_coneProduct, ellipticGammaBackwardProduct_eq_coneProduct,
    ellipticGammaCone]
  simp only [Pi.div_apply]
  congr 2
  ring

end

end GaloisForLFunctions.HTGeometry
