import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Antipodal L² distortion and spectral conversion

This module formalizes Okten--Turan, arXiv:2608.19244v1, equations `(53)`--`(58)`.  The exact
change-of-variables equality and the Poincaré/spectral-gap inequality remain visible inputs: they
are the geometric facts assumed in the paper for its selected smooth compact reference slice.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Spatial scalar L² norm written directly in terms of its defining integral. -/
def spatialL2Norm {X : Type*} [MeasurableSpace X] (mu : Measure X) (f : X → ℝ) : ℝ :=
  Real.sqrt (∫ x, f x ^ 2 ∂mu)

/-- A positive pointwise lower bound on a Jacobian gives the inverse-Jacobian upper bound used in
equation `(53)`. -/
theorem inv_jacobian_le_inv_min {X : Type*}
    (J : X → ℝ) {Jmin : ℝ} (hJmin : 0 < Jmin)
    (hmin : ∀ x, Jmin ≤ J x) (x : X) :
    (J x)⁻¹ ≤ Jmin⁻¹ :=
  inv_anti₀ hJmin (hmin x)

variable {X : Type*} [MeasurableSpace X]

/-- Equation `(53)`, change-of-variables equality derived from the measure-level Jacobian law.
The map condition says that pushforward by the involution has density `J⁻¹`, equivalent to the
paper's pullback convention `A* dA = J dA`. -/
theorem integral_sq_comp_eq_integral_invJacobian
    (mu : Measure X) (A : X → X) (J xi : X → ℝ)
    (hA : AEMeasurable A mu)
    (hmap : Measure.map A mu = mu.withDensity (fun x => ENNReal.ofReal ((J x)⁻¹)))
    (hJpos : ∀ x, 0 < J x) (hJmeas : Measurable fun x => (J x)⁻¹)
    (hxi : StronglyMeasurable fun x => xi x ^ 2) :
    (∫ x, (xi (A x)) ^ 2 ∂mu) = ∫ x, xi x ^ 2 * (J x)⁻¹ ∂mu := by
  rw [← integral_map hA hxi.aestronglyMeasurable, hmap,
    integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards with x
    simp [ENNReal.toReal_ofReal (inv_nonneg.mpr (hJpos x).le), smul_eq_mul, mul_comm]
  · exact hJmeas.ennreal_ofReal
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

/-- The inverse-Jacobian weighted square is integrable under the same uniform bound used in
equation `(53)`. -/
theorem integrable_sq_mul_invJacobian
    (mu : Measure X) (J xi : X → ℝ) (Jmin : ℝ)
    (hJpos : ∀ x, 0 < J x) (hJmeas : Measurable fun x => (J x)⁻¹)
    (hxi : Integrable (fun x => xi x ^ 2) mu)
    (hJbound : ∀ x, (J x)⁻¹ ≤ Jmin⁻¹) :
    Integrable (fun x => xi x ^ 2 * (J x)⁻¹) mu := by
  apply (hxi.const_mul Jmin⁻¹).mono'
  · exact hxi.aestronglyMeasurable.mul hJmeas.aestronglyMeasurable
  · filter_upwards with x
    change |xi x ^ 2 * (J x)⁻¹| ≤ Jmin⁻¹ * xi x ^ 2
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (hJpos x).le))]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hJbound x) (sq_nonneg (xi x))

/-- Equation `(53)`: the Jacobian change-of-variables identity implies the squared L² distortion
bound.  `hchange` is precisely the standard change-of-variables equality displayed in the paper. -/
theorem integral_sq_comp_le_inv_mul
    (mu : Measure X) (A : X → X) (J : X → ℝ) (Jmin : ℝ) (xi : X → ℝ)
    (hchange : (∫ x, (xi (A x)) ^ 2 ∂mu) = ∫ x, xi x ^ 2 * (J x)⁻¹ ∂mu)
    (hxi : Integrable (fun x => xi x ^ 2) mu)
    (hweighted : Integrable (fun x => xi x ^ 2 * (J x)⁻¹) mu)
    (hJbound : ∀ x, (J x)⁻¹ ≤ Jmin⁻¹) :
    (∫ x, (xi (A x)) ^ 2 ∂mu) ≤ Jmin⁻¹ * ∫ x, xi x ^ 2 ∂mu := by
  rw [hchange, ← integral_const_mul]
  apply integral_mono hweighted (hxi.const_mul Jmin⁻¹)
  intro x
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (hJbound x) (sq_nonneg (xi x))

/-- Equation `(54)`: square-root form of the L² composition bound. -/
theorem spatialL2Norm_comp_le
    (mu : Measure X) (A : X → X) (J : X → ℝ) (Jmin : ℝ) (xi : X → ℝ)
    (hJmin : 0 < Jmin)
    (hchange : (∫ x, (xi (A x)) ^ 2 ∂mu) = ∫ x, xi x ^ 2 * (J x)⁻¹ ∂mu)
    (hxi : Integrable (fun x => xi x ^ 2) mu)
    (hweighted : Integrable (fun x => xi x ^ 2 * (J x)⁻¹) mu)
    (hJbound : ∀ x, (J x)⁻¹ ≤ Jmin⁻¹) :
    spatialL2Norm mu (xi ∘ A) ≤ Real.sqrt Jmin⁻¹ * spatialL2Norm mu xi := by
  have hs := integral_sq_comp_le_inv_mul mu A J Jmin xi hchange hxi hweighted hJbound
  rw [spatialL2Norm, spatialL2Norm]
  have hinv : 0 ≤ Jmin⁻¹ := inv_nonneg.mpr hJmin.le
  have hint : 0 ≤ ∫ x, xi x ^ 2 ∂mu := integral_nonneg fun _ => sq_nonneg _
  calc
    Real.sqrt (∫ x, (xi ∘ A) x ^ 2 ∂mu)
        ≤ Real.sqrt (Jmin⁻¹ * ∫ x, xi x ^ 2 ∂mu) := Real.sqrt_le_sqrt hs
    _ = Real.sqrt Jmin⁻¹ * Real.sqrt (∫ x, xi x ^ 2 ∂mu) := by
      rw [Real.sqrt_mul hinv]

/-- End-to-end form of equations `(53)`--`(54)` from the measure-level Jacobian law, with no
separately assumed change-of-variables or weighted-integrability equality. -/
theorem spatialL2Norm_comp_le_of_map
    (mu : Measure X) (A : X → X) (J : X → ℝ) (Jmin : ℝ) (xi : X → ℝ)
    (hJmin : 0 < Jmin) (hmin : ∀ x, Jmin ≤ J x)
    (hA : AEMeasurable A mu)
    (hmap : Measure.map A mu = mu.withDensity (fun x => ENNReal.ofReal ((J x)⁻¹)))
    (hJpos : ∀ x, 0 < J x) (hJmeas : Measurable fun x => (J x)⁻¹)
    (hxiStrong : StronglyMeasurable fun x => xi x ^ 2)
    (hxi : Integrable (fun x => xi x ^ 2) mu) :
    spatialL2Norm mu (xi ∘ A) ≤ Real.sqrt Jmin⁻¹ * spatialL2Norm mu xi := by
  have hJbound : ∀ x, (J x)⁻¹ ≤ Jmin⁻¹ :=
    inv_jacobian_le_inv_min J hJmin hmin
  exact spatialL2Norm_comp_le mu A J Jmin xi hJmin
    (integral_sq_comp_eq_integral_invJacobian mu A J xi hA hmap hJpos hJmeas hxiStrong)
    hxi (integrable_sq_mul_invJacobian mu J xi Jmin hJpos hJmeas hxi hJbound) hJbound

/-- Pointwise inequality underlying equation `(56)`. -/
theorem norm_sub_sq_le_two {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have htri := norm_sub_le x y
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y, norm_nonneg (x - y)]

/-- Integrated gradient-difference estimate in equation `(56)`. -/
theorem integral_norm_sub_sq_le_two {E : Type*} [NormedAddCommGroup E]
    (mu : Measure X) (f g : X → E)
    (hf : Integrable (fun x => ‖f x‖ ^ 2) mu)
    (hg : Integrable (fun x => ‖g x‖ ^ 2) mu)
    (hsub : Integrable (fun x => ‖f x - g x‖ ^ 2) mu) :
    (∫ x, ‖f x - g x‖ ^ 2 ∂mu) ≤
      2 * ∫ x, ‖f x‖ ^ 2 ∂mu + 2 * ∫ x, ‖g x‖ ^ 2 ∂mu := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf.const_mul 2) (hg.const_mul 2)]
  apply integral_mono hsub ((hf.const_mul 2).add (hg.const_mul 2))
  exact fun x => norm_sub_sq_le_two (f x) (g x)

/-- Local two-dimensional cancellation behind equation `(55)`: inverse metric contributes
`exp (-2 sigma)` while area contributes `exp (2 sigma)`, leaving Dirichlet density unchanged. -/
theorem conformalDirichletDensity_invariant (sigma gradientSq : ℝ) :
    Real.exp (-2 * sigma) * gradientSq * Real.exp (2 * sigma) = gradientSq := by
  calc
    Real.exp (-2 * sigma) * gradientSq * Real.exp (2 * sigma) =
        gradientSq * (Real.exp (-2 * sigma) * Real.exp (2 * sigma)) := by ring
    _ = gradientSq * Real.exp (-2 * sigma + 2 * sigma) := by rw [Real.exp_add]
    _ = gradientSq := by simp

/-- Equations `(55)`--`(57)`: conformal invariance of Dirichlet energy, the mismatch gradient
estimate, and a spectral gap imply the sharp factor `lambda / 4`. -/
theorem spectral_mismatch_energy_lower_bound
    (lambda energyF energyFA energyW mismatch : ℝ)
    (hcomp : energyFA = energyF)
    (hgradient : energyW ≤ 2 * energyF + 2 * energyFA)
    (hspectral : lambda * mismatch ≤ energyW) :
    lambda / 4 * mismatch ≤ energyF := by
  rw [hcomp] at hgradient
  linarith

/-- Equation `(58)`: substituting the round-sphere gap `lambda = 2 / R²` into equation `(57)`. -/
theorem roundSphere_spectral_mismatch_energy_lower_bound
    (R energyF mismatch : ℝ) (hR : R ≠ 0)
    (hbound : (2 / R ^ 2) / 4 * mismatch ≤ energyF) :
    1 / (2 * R ^ 2) * mismatch ≤ energyF := by
  convert hbound using 1
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
