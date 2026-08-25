import GaloisForLFunctions.RHTower.DeningerRadialIntegral
import GaloisForLFunctions.RHTower.PolynomialFockPotentialGeometry
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.GaussianMonomialTailAsymptotic

/-!
# Tangent Gaussian for polynomial Fock potentials

The holomorphic exponential tangent to `(1+|z|²)^(m/2)` at a real point removes the large linear
variation of the weight.  The global Bregman estimate leaves a centered Gaussian at the exact
adapted scale.  This module proves its plane integral and the resulting sharp tangent-density norm
bound; it is shared input for the normalized-kernel lower estimate and local Carleson producer.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exact centered Gaussian mass on the complex plane. -/
theorem integral_complex_gaussian (c : ℝ) (hc : 0 < c) :
    (∫ z : ℂ, Real.exp (-c * ‖z‖ ^ 2)) = Real.pi / c := by
  calc
    (∫ z : ℂ, Real.exp (-c * ‖z‖ ^ 2)) =
        Real.pi * ∫ s in Ioi (0 : ℝ), Real.exp (-c * s) :=
      deningerRadial_integral_eq (fun s => Real.exp (-c * s))
    _ = Real.pi * (1 / c) := by
      rw [show (fun s : ℝ => Real.exp (-c * s)) =
          fun s => Real.exp (-c * (s - 0)) by funext s; ring_nf]
      rw [HedenmalmThetaSource.integral_Ioi_exp_neg_shift hc]
    _ = Real.pi / c := by ring

/-- Integrability of the centered complex Gaussian. -/
theorem integrable_complex_gaussian (c : ℝ) (hc : 0 < c) :
    Integrable (fun z : ℂ => Real.exp (-c * ‖z‖ ^ 2)) := by
  change Integrable (fun z : ℂ => (fun r : ℝ => Real.exp (-c * r ^ 2)) ‖z‖)
  apply (MeasureTheory.integrable_fun_norm_addHaar (E := ℂ) (F := ℝ) volume
    (f := fun r : ℝ => Real.exp (-c * r ^ 2))).2
  simpa [Complex.finrank_real_complex, smul_eq_mul] using
    (integrableOn_pow_mul_exp_neg_mul_sq_Ioi_zero 1 hc)

/-- Translation does not alter complex Gaussian mass. -/
theorem integral_complex_gaussian_sub_real (c x : ℝ) (hc : 0 < c) :
    (∫ z : ℂ, Real.exp (-c * ‖z - (x : ℂ)‖ ^ 2)) = Real.pi / c := by
  have h := MeasureTheory.integral_add_right_eq_self (μ := volume)
    (f := fun z : ℂ => Real.exp (-c * ‖z‖ ^ 2)) (-(x : ℂ))
  simpa [sub_eq_add_neg] using h.trans (integral_complex_gaussian c hc)

/-- Integrability of a real-centered complex Gaussian. -/
theorem integrable_complex_gaussian_sub_real (c x : ℝ) (hc : 0 < c) :
    Integrable (fun z : ℂ => Real.exp (-c * ‖z - (x : ℂ)‖ ^ 2)) := by
  have h := (integrable_complex_gaussian c hc).comp_add_right (-(x : ℂ))
  simpa [sub_eq_add_neg] using h

/-- Squared modulus of the holomorphic tangent exponential against the polynomial Fock weight. -/
def polynomialFockTangentDensity (m x : ℝ) (z : ℂ) : ℝ :=
  Real.exp (2 * polynomialFockRadialSlope m x * (z.re - x) -
    2 * polynomialFockPotential m ‖z‖)

/-- Global Gaussian domination of the tangent density at the exact curvature scale. -/
theorem polynomialFockTangentDensity_le_gaussian
    {m x : ℝ} (hm : 2 ≤ m) (z : ℂ) :
    polynomialFockTangentDensity m x z ≤
      Real.exp (-2 * polynomialFockPotential m x) *
        Real.exp (-(m * (1 + x ^ 2) ^ (m / 2 - 1) * ‖z - (x : ℂ)‖ ^ 2)) := by
  have h := polynomialFockPotential_bregman_lower (m := m) (x := x) hm z
  have hexp :
      2 * polynomialFockRadialSlope m x * (z.re - x) -
          2 * polynomialFockPotential m ‖z‖ ≤
        -2 * polynomialFockPotential m x -
          m * (1 + x ^ 2) ^ (m / 2 - 1) * ‖z - (x : ℂ)‖ ^ 2 := by
    linarith
  rw [polynomialFockTangentDensity, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa [sub_eq_add_neg] using hexp)

/-- The polynomial-Fock tangent density is integrable. -/
theorem integrable_polynomialFockTangentDensity
    {m x : ℝ} (hm : 2 ≤ m) : Integrable (polynomialFockTangentDensity m x) := by
  let c : ℝ := m * (1 + x ^ 2) ^ (m / 2 - 1)
  have hc : 0 < c := by dsimp [c]; positivity
  let g : ℂ → ℝ := fun z =>
    Real.exp (-2 * polynomialFockPotential m x) *
      Real.exp (-c * ‖z - (x : ℂ)‖ ^ 2)
  have hg : Integrable g := by
    simpa [g] using (integrable_complex_gaussian_sub_real c x hc).const_mul
      (Real.exp (-2 * polynomialFockPotential m x))
  apply hg.mono
  · have hcont : Continuous (polynomialFockTangentDensity m x) := by
      unfold polynomialFockTangentDensity
      apply Real.continuous_exp.comp
      exact
        (continuous_const.mul (Complex.continuous_re.sub continuous_const)).sub
          (continuous_const.mul
            ((continuous_polynomialFockPotential m).comp continuous_norm))
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_of_nonneg (by unfold polynomialFockTangentDensity; positivity),
      Real.norm_of_nonneg (by dsimp [g]; positivity)]
    simpa [g, c] using polynomialFockTangentDensity_le_gaussian hm z

/-- Sharp plane-norm upper bound for the holomorphic tangent exponential. -/
theorem integral_polynomialFockTangentDensity_le
    {m x : ℝ} (hm : 2 ≤ m) :
    (∫ z : ℂ, polynomialFockTangentDensity m x z) ≤
      Real.exp (-2 * polynomialFockPotential m x) *
        (Real.pi / (m * (1 + x ^ 2) ^ (m / 2 - 1))) := by
  let c : ℝ := m * (1 + x ^ 2) ^ (m / 2 - 1)
  have hc : 0 < c := by dsimp [c]; positivity
  let g : ℂ → ℝ := fun z =>
    Real.exp (-2 * polynomialFockPotential m x) *
      Real.exp (-c * ‖z - (x : ℂ)‖ ^ 2)
  have hg : Integrable g := by
    simpa [g] using (integrable_complex_gaussian_sub_real c x hc).const_mul
      (Real.exp (-2 * polynomialFockPotential m x))
  have hf := integrable_polynomialFockTangentDensity (m := m) (x := x) hm
  calc
    (∫ z : ℂ, polynomialFockTangentDensity m x z) ≤ ∫ z : ℂ, g z := by
      apply MeasureTheory.integral_mono_ae hf hg
      filter_upwards [] with z
      simpa [g, c] using polynomialFockTangentDensity_le_gaussian hm z
    _ = Real.exp (-2 * polynomialFockPotential m x) * (Real.pi / c) := by
      rw [MeasureTheory.integral_const_mul, integral_complex_gaussian_sub_real c x hc]
    _ = _ := by rfl

end


end RHTower
