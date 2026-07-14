import GaloisForLFunctions.HTGeometry.EllipticGammaProduct

/-!
# Elliptic-gamma inversion from the integrable-model reflection

The elliptic-gamma Boltzmann weights of solvable lattice models obey an inversion, or unitarity,
relation.  This file extracts its source-general algebraic content for the HTGeometry hierarchy.

In multiplicative coordinates the involution is `x ↦ p*q/x`.  The repository uses the centered
coordinate

`x(τ,z) = -exp(π i τ) exp(2 π i z)`,

so the corresponding additive reflection is `z ↦ σ - z`.  Under this reflection every forward
elliptic-gamma factor becomes a backward factor and conversely.  Consequently the two entire
products are exchanged, the quotient is inverted, and its logarithmic-derivative kernel is fixed.
The final theorem applies these identities to the existing analytic product theorem and discharges
all regularity hypotheses at the reflected point from those at the original point.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- The centered additive coordinate realizes the multiplicative elliptic-gamma reflection:
`x(τ,σ-z) * x(τ,z) = p*q`. -/
theorem ellipticThetaCoordinate_reflection_mul (σ τ z : ℂ) :
    ellipticThetaCoordinate τ (σ - z) * ellipticThetaCoordinate τ z =
      ellipticNome σ * ellipticNome τ := by
  rw [ellipticThetaCoordinate, ellipticThetaCoordinate, ellipticNome, ellipticNome]
  rw [show 2 * Real.pi * I * (σ - z) =
      2 * Real.pi * I * σ + -(2 * Real.pi * I * z) by ring,
    Complex.exp_add, Complex.exp_neg]
  rw [show 2 * Real.pi * I * τ =
      Real.pi * I * τ + Real.pi * I * τ by ring, Complex.exp_add]
  field_simp [Complex.exp_ne_zero]

/-- Division form of the centered-coordinate reflection. -/
theorem ellipticThetaCoordinate_reflection (σ τ z : ℂ) :
    ellipticThetaCoordinate τ (σ - z) =
      ellipticNome σ * ellipticNome τ / ellipticThetaCoordinate τ z := by
  exact (eq_div_iff (ellipticThetaCoordinate_ne_zero τ z)).2
    (ellipticThetaCoordinate_reflection_mul σ τ z)

/-- Multiplicative reflection exchanges a forward elliptic-gamma argument with the corresponding
backward argument. -/
theorem ellipticGammaForwardArgument_reflection
    {p q x : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) (hx : x ≠ 0) (j k : ℕ) :
    ellipticGammaForwardArgument p q (p * q / x) j k =
      ellipticGammaBackwardArgument p q x j k := by
  simp only [ellipticGammaForwardArgument, ellipticGammaBackwardArgument, pow_succ]
  field_simp [hp, hq, hx]

/-- Multiplicative reflection exchanges a backward elliptic-gamma argument with the corresponding
forward argument. -/
theorem ellipticGammaBackwardArgument_reflection
    {p q x : ℂ} (j k : ℕ) :
    ellipticGammaBackwardArgument p q (p * q / x) j k =
      ellipticGammaForwardArgument p q x j k := by
  simp only [ellipticGammaForwardArgument, ellipticGammaBackwardArgument, pow_succ]
  rw [div_eq_mul_inv]
  ring

/-- Each logarithmic-derivative summand is fixed by multiplicative reflection. -/
theorem ellipticGammaLogSummand_reflection
    {p q x : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) (hx : x ≠ 0) (j k : ℕ) :
    ellipticGammaLogSummand p q (p * q / x) j k =
      ellipticGammaLogSummand p q x j k := by
  rw [ellipticGammaLogSummand, ellipticGammaLogSummand,
    ellipticGammaForwardArgument_reflection hp hq hx,
    ellipticGammaBackwardArgument_reflection]
  ring

/-- The full multiplicative logarithmic kernel is fixed by reflection.  No convergence hypothesis
is needed: the equality is termwise. -/
theorem ellipticGammaLogKernel_reflection
    {p q x : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) (hx : x ≠ 0) :
    ellipticGammaLogKernel p q (p * q / x) = ellipticGammaLogKernel p q x := by
  rw [ellipticGammaLogKernel, ellipticGammaLogKernel]
  apply tsum_congr
  intro jk
  exact ellipticGammaLogSummand_reflection hp hq hx jk.1 jk.2

/-- The additive elliptic-gamma logarithmic kernel is reflection invariant. -/
theorem ellipticGammaAdditiveLogKernel_reflection (σ τ z : ℂ) :
    ellipticGammaAdditiveLogKernel σ τ (σ - z) =
      ellipticGammaAdditiveLogKernel σ τ z := by
  rw [ellipticGammaAdditiveLogKernel, ellipticGammaAdditiveLogKernel,
    ellipticThetaCoordinate_reflection]
  rw [ellipticGammaLogKernel_reflection
    (ellipticNome_ne_zero σ) (ellipticNome_ne_zero τ)
      (ellipticThetaCoordinate_ne_zero τ z)]

/-- Additive reflection exchanges every forward factor with its backward partner. -/
theorem ellipticGammaForwardFactor_reflection (σ τ : ℂ) (jk : ℕ × ℕ) (z : ℂ) :
    ellipticGammaForwardFactor σ τ jk (σ - z) =
      ellipticGammaBackwardFactor σ τ jk z := by
  rw [ellipticGammaForwardFactor, ellipticGammaBackwardFactor,
    ellipticThetaCoordinate_reflection]
  rw [ellipticGammaForwardArgument_reflection
    (ellipticNome_ne_zero σ) (ellipticNome_ne_zero τ)
      (ellipticThetaCoordinate_ne_zero τ z)]

/-- Additive reflection exchanges every backward factor with its forward partner. -/
theorem ellipticGammaBackwardFactor_reflection (σ τ : ℂ) (jk : ℕ × ℕ) (z : ℂ) :
    ellipticGammaBackwardFactor σ τ jk (σ - z) =
      ellipticGammaForwardFactor σ τ jk z := by
  rw [ellipticGammaBackwardFactor, ellipticGammaForwardFactor,
    ellipticThetaCoordinate_reflection]
  rw [ellipticGammaBackwardArgument_reflection]

/-- Reflection exchanges the two entire elliptic-gamma products. -/
theorem ellipticGammaForwardProduct_reflection (σ τ z : ℂ) :
    ellipticGammaForwardProduct σ τ (σ - z) =
      ellipticGammaBackwardProduct σ τ z := by
  rw [ellipticGammaForwardProduct, ellipticGammaBackwardProduct]
  apply tprod_congr
  intro jk
  exact ellipticGammaForwardFactor_reflection σ τ jk z

/-- Reflection exchanges the two entire elliptic-gamma products in the opposite direction. -/
theorem ellipticGammaBackwardProduct_reflection (σ τ z : ℂ) :
    ellipticGammaBackwardProduct σ τ (σ - z) =
      ellipticGammaForwardProduct σ τ z := by
  rw [ellipticGammaBackwardProduct, ellipticGammaForwardProduct]
  apply tprod_congr
  intro jk
  exact ellipticGammaBackwardFactor_reflection σ τ jk z

/-- Exact inversion of the additive elliptic-gamma product. -/
theorem ellipticGammaProduct_reflection (σ τ z : ℂ) :
    ellipticGammaProduct σ τ (σ - z) = (ellipticGammaProduct σ τ z)⁻¹ := by
  rw [ellipticGammaProduct, ellipticGammaProduct,
    ellipticGammaForwardProduct_reflection,
    ellipticGammaBackwardProduct_reflection]
  exact (inv_div _ _).symm

/-- Original-point regularity transports to the reflected point; callers do not need a second pair
of nonvanishing hypotheses. -/
theorem ellipticGammaProducts_reflection_ne_zero
    {σ τ z : ℂ}
    (hzF : ellipticGammaForwardProduct σ τ z ≠ 0)
    (hzB : ellipticGammaBackwardProduct σ τ z ≠ 0) :
    ellipticGammaForwardProduct σ τ (σ - z) ≠ 0 ∧
      ellipticGammaBackwardProduct σ τ (σ - z) ≠ 0 := by
  rw [ellipticGammaForwardProduct_reflection,
    ellipticGammaBackwardProduct_reflection]
  exact ⟨hzB, hzF⟩

/-- The regular-locus inversion, in the product-one form used as unitarity in solvable lattice
models. -/
theorem ellipticGammaProduct_mul_reflection
    {σ τ z : ℂ}
    (hzF : ellipticGammaForwardProduct σ τ z ≠ 0)
    (hzB : ellipticGammaBackwardProduct σ τ z ≠ 0) :
    ellipticGammaProduct σ τ z * ellipticGammaProduct σ τ (σ - z) = 1 := by
  rw [ellipticGammaProduct_reflection]
  exact mul_inv_cancel₀ (div_ne_zero hzF hzB)

/-- Direct application to the analytic product theorem: the logarithmic derivative at the reflected
point equals the original one, and the reflected regularity obligations are discharged internally. -/
theorem logDeriv_ellipticGammaProduct_reflection
    {σ τ z : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hzF : ellipticGammaForwardProduct σ τ z ≠ 0)
    (hzB : ellipticGammaBackwardProduct σ τ z ≠ 0) :
    logDeriv (ellipticGammaProduct σ τ) (σ - z) =
      logDeriv (ellipticGammaProduct σ τ) z := by
  obtain ⟨hrF, hrB⟩ := ellipticGammaProducts_reflection_ne_zero hzF hzB
  rw [logDeriv_ellipticGammaProduct_eq_additiveKernel hσ hτ hrF hrB,
    logDeriv_ellipticGammaProduct_eq_additiveKernel hσ hτ hzF hzB,
    ellipticGammaAdditiveLogKernel_reflection]

end

end GaloisForLFunctions
