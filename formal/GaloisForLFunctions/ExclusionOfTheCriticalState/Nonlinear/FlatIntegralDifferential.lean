import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralEnergy
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Differentiation and descent of the flat L² energy

The integrated quadratic remainder identifies the Fréchet derivative
without differentiation under an integral. Its gradient is a contraction.
A unit gradient step dissipates half the squared gradient norm, and the
same Taylor estimate gives a coercive Bregman bound between any profiles.
-/

open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The pointwise flat gradient represents the genuine Fréchet derivative on L². -/
theorem integralEnergy_hasFDerivAt (f : Lp ℝ 2 μ) :
    HasFDerivAt integralEnergy (innerSL ℝ (gradientLp f)) f := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨2 * c, by positivity, ?_⟩
  intro h hh
  have hb := integral_tangent_error_bounds (f + h) f
  rw [add_sub_cancel_left] at hb
  change ‖integralEnergy (f + h) - integralEnergy f - inner ℝ (gradientLp f) h‖ ≤ c * ‖h‖
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  rw [dist_zero_right] at hh
  nlinarith only [hb.2, mul_nonneg (norm_nonneg h) (le_of_lt (sub_pos.mpr hh))]

/-- No profile restrictions are needed for differentiability of the integral energy. -/
theorem integralEnergy_differentiable : Differentiable ℝ (integralEnergy : Lp ℝ 2 μ → ℝ) :=
  fun f => (integralEnergy_hasFDerivAt f).differentiableAt

/-- The Fréchet derivative varies continuously in operator norm. -/
theorem integralEnergy_continuous_fderiv :
    Continuous (fderiv ℝ (integralEnergy : Lp ℝ 2 μ → ℝ)) := by
  have he : fderiv ℝ (integralEnergy : Lp ℝ 2 μ → ℝ) =
      fun f => innerSL ℝ (gradientLp f) := funext fun f => (integralEnergy_hasFDerivAt f).fderiv
  rw [he]
  exact (innerSL ℝ).continuous.comp gradientLp_contraction.continuous

/-- The flat integral energy is continuously Fréchet differentiable. -/
theorem integralEnergy_contDiff_one : ContDiff ℝ 1 (integralEnergy : Lp ℝ 2 μ → ℝ) :=
  contDiff_one_iff_fderiv.mpr ⟨integralEnergy_differentiable, integralEnergy_continuous_fderiv⟩

/-- A unit gradient step has a definite energy decrease. -/
theorem integralEnergy_unit_descent (f : Lp ℝ 2 μ) :
    integralEnergy (f - gradientLp f) ≤ integralEnergy f - ‖gradientLp f‖ ^ 2 / 2 := by
  have hb := (integral_tangent_error_bounds (f - gradientLp f) f).2
  have he : f - gradientLp f - f = -gradientLp f := by abel
  rw [he, norm_neg, inner_neg_right, real_inner_self_eq_norm_sq] at hb
  linarith only [hb]

/-- The gradient norm is controlled by the energy, on arbitrary measure spaces. -/
theorem gradientLp_sq_le_energy (f : Lp ℝ 2 μ) :
    ‖gradientLp f‖ ^ 2 ≤ 2 * integralEnergy f := by
  linarith only [integralEnergy_unit_descent f,
    (integral_energy_bounds (f - gradientLp f)).1]

/-- Bregman energy controls the entire L² gradient displacement. -/
theorem gradientLp_displacement_le_tangent_error (f g : Lp ℝ 2 μ) :
    ‖gradientLp f - gradientLp g‖ ^ 2 / 2 ≤
      integralEnergy f - integralEnergy g - inner ℝ (gradientLp g) (f - g) := by
  let d := gradientLp f - gradientLp g
  have hu := (integral_tangent_error_bounds (f - d) f).2
  have hl := integral_support (f - d) g
  have he : f - d - f = -d := by abel
  have hf : f - d - g = (f - g) - d := by abel
  rw [he, norm_neg, inner_neg_right] at hu
  rw [hf, inner_sub_right] at hl
  have hd : inner ℝ (gradientLp f) d - inner ℝ (gradientLp g) d = ‖d‖ ^ 2 := by
    rw [← inner_sub_left]
    exact real_inner_self_eq_norm_sq d
  change ‖d‖ ^ 2 / 2 ≤ _
  linarith only [hu, hl, hd]

/-- The nonlinear L² gradient is firmly nonexpansive. -/
theorem gradientLp_firm (f g : Lp ℝ 2 μ) :
    ‖gradientLp f - gradientLp g‖ ^ 2 ≤
      inner ℝ (gradientLp f - gradientLp g) (f - g) := by
  have hfg := gradientLp_displacement_le_tangent_error f g
  have hgf := gradientLp_displacement_le_tangent_error g f
  rw [norm_sub_rev, show g - f = -(f - g) by abel, inner_neg_right] at hgf
  rw [inner_sub_left]
  linarith only [hfg, hgf]

/-- Gradient and complementary displacement together fit within the original distance. -/
theorem gradientLp_complementary_bound (f g : Lp ℝ 2 μ) :
    ‖gradientLp f - gradientLp g‖ ^ 2 +
      ‖(f - gradientLp f) - (g - gradientLp g)‖ ^ 2 ≤ ‖f - g‖ ^ 2 := by
  have he : (f - gradientLp f) - (g - gradientLp g) =
      (f - g) - (gradientLp f - gradientLp g) := by abel
  rw [he, norm_sub_sq_real (f - g) (gradientLp f - gradientLp g)]
  rw [real_inner_comm]
  linarith only [gradientLp_firm f g]

/-- A unit gradient step is nonexpansive on the whole L² space. -/
theorem integral_descent_contraction :
    LipschitzWith 1 (fun f : Lp ℝ 2 μ => f - gradientLp f) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hb := gradientLp_complementary_bound f g
  nlinarith only [hb, sq_nonneg ‖gradientLp f - gradientLp g‖,
    norm_nonneg ((f - gradientLp f) - (g - gradientLp g)), norm_nonneg (f - g)]

/-- Gradient norms decrease, with a square-summable correction between successive steps. -/
theorem gradientLp_unit_descent (f : Lp ℝ 2 μ) :
    ‖gradientLp (f - gradientLp f)‖ ^ 2 +
      ‖gradientLp f - gradientLp (f - gradientLp f)‖ ^ 2 ≤ ‖gradientLp f‖ ^ 2 := by
  have h := gradientLp_firm f (f - gradientLp f)
  rw [show f - (f - gradientLp f) = gradientLp f by abel, inner_sub_left,
    real_inner_self_eq_norm_sq] at h
  have he := norm_sub_sq_real (gradientLp f) (gradientLp (f - gradientLp f))
  rw [real_inner_comm] at he
  linarith only [h, he]

#print axioms integralEnergy_hasFDerivAt
#print axioms integralEnergy_continuous_fderiv
#print axioms integralEnergy_contDiff_one
#print axioms integralEnergy_unit_descent
#print axioms gradientLp_sq_le_energy
#print axioms gradientLp_displacement_le_tangent_error
#print axioms gradientLp_firm
#print axioms gradientLp_complementary_bound
#print axioms integral_descent_contraction
#print axioms gradientLp_unit_descent
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
