import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleChart
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCayleyDensity
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCayleyPolar
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
The literal native hyperbolic circle chart becomes ordinary Euclidean polar
coordinates after the Cayley map about `I`.  This is the global change-of-arena
needed for the cyclic Peierls cap measure, not a replacement chart.
-/
namespace RHTower.D4BMNativeCircle
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open MeasureTheory Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Literal native circle about `I`, viewed in the upper-half-plane complex chart. -/
def baseCircleComplex (d theta : ℝ) : ℂ :=
  (offset d theta : ℂ) + (height d theta : ℂ) * Complex.I

/-- Cayley coordinate about `I` used only to transport the literal native circle. -/
def baseCayley (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

private theorem tanh_half_eq_sinh_div_cosh_add_one (d : ℝ) :
    Real.tanh (d / 2) = Real.sinh d / (Real.cosh d + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hCpos : 0 < Real.cosh (d / 2) := Real.cosh_pos _
  have hCne : Real.cosh (d / 2) ≠ 0 := hCpos.ne'
  have hsq := Real.cosh_sq_sub_sinh_sq (d / 2)
  have hsinh : Real.sinh d =
      Real.sinh (d / 2) * Real.cosh (d / 2) + Real.cosh (d / 2) * Real.sinh (d / 2) := by
    convert Real.sinh_add (d / 2) (d / 2) using 1; ring
  have hcosh : Real.cosh d =
      Real.cosh (d / 2) * Real.cosh (d / 2) + Real.sinh (d / 2) * Real.sinh (d / 2) := by
    convert Real.cosh_add (d / 2) (d / 2) using 1; ring
  rw [hsinh, hcosh]
  have hden : Real.cosh (d / 2) * Real.cosh (d / 2) +
      Real.sinh (d / 2) * Real.sinh (d / 2) + 1 =
      2 * (Real.cosh (d / 2) * Real.cosh (d / 2)) := by
    nlinarith [hsq]
  rw [hden]
  field_simp [hCne]
  ring

private theorem cayley_denominator (d theta : ℝ) :
    offset d theta ^ 2 + (height d theta + 1) ^ 2 =
      2 * (Real.cosh d + 1) / denominator d theta := by
  have hDne : denominator d theta ≠ 0 := (denominator_pos d theta).ne'
  dsimp [offset, height]
  field_simp [hDne]
  dsimp [denominator]
  have htrig := Real.sin_sq_add_cos_sq theta
  have hhyp := Real.cosh_sq_sub_sinh_sq d
  linear_combination (Real.sinh d) ^ 2 * htrig - hhyp

private theorem cayley_re_numerator (d theta : ℝ) :
    offset d theta ^ 2 + height d theta ^ 2 - 1 =
      2 * Real.sinh d * Real.cos theta / denominator d theta := by
  have hDne : denominator d theta ≠ 0 := (denominator_pos d theta).ne'
  dsimp [offset, height]
  field_simp [hDne]
  dsimp [denominator]
  have htrig := Real.sin_sq_add_cos_sq theta
  have hhyp := Real.cosh_sq_sub_sinh_sq d
  linear_combination (Real.sinh d) ^ 2 * htrig - hhyp

private theorem cayley_re (d theta : ℝ) :
    (offset d theta ^ 2 + height d theta ^ 2 - 1) /
      (offset d theta ^ 2 + (height d theta + 1) ^ 2) =
      Real.sinh d * Real.cos theta / (Real.cosh d + 1) := by
  have hDne : denominator d theta ≠ 0 := (denominator_pos d theta).ne'
  have hc1ne : Real.cosh d + 1 ≠ 0 := by linarith [Real.cosh_pos d]
  rw [cayley_re_numerator, cayley_denominator]
  field_simp [hDne, hc1ne]

private theorem cayley_im (d theta : ℝ) :
    -2 * offset d theta /
      (offset d theta ^ 2 + (height d theta + 1) ^ 2) =
      -(Real.sinh d * Real.sin theta / (Real.cosh d + 1)) := by
  have hDne : denominator d theta ≠ 0 := (denominator_pos d theta).ne'
  have hc1ne : Real.cosh d + 1 ≠ 0 := by linarith [Real.cosh_pos d]
  rw [cayley_denominator, offset]
  field_simp [hDne, hc1ne]

private theorem baseCayley_re (d theta : ℝ) :
    (baseCayley (baseCircleComplex d theta)).re =
      (offset d theta ^ 2 + height d theta ^ 2 - 1) /
        (offset d theta ^ 2 + (height d theta + 1) ^ 2) := by
  rw [baseCayley, Complex.div_re]
  simp only [baseCircleComplex, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_im, mul_one, Complex.I_re, mul_zero,
    sub_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, add_zero,
    Complex.normSq_apply]
  ring

private theorem baseCayley_im (d theta : ℝ) :
    (baseCayley (baseCircleComplex d theta)).im =
      -2 * offset d theta /
        (offset d theta ^ 2 + (height d theta + 1) ^ 2) := by
  rw [baseCayley, Complex.div_im]
  simp only [baseCircleComplex, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_im, mul_one, Complex.I_re, mul_zero,
    sub_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, add_zero,
    Complex.normSq_apply]
  ring

/-- Cayley conjugates the literal native circle about `I` to Euclidean polar coordinates. -/
theorem baseCayley_eq_polarCoord (d theta : ℝ) :
    baseCayley (baseCircleComplex d theta) =
      Complex.polarCoord.symm (Real.tanh (d / 2), -theta) := by
  have hre : (baseCayley (baseCircleComplex d theta)).re =
      Real.tanh (d / 2) * Real.cos theta := by
    rw [baseCayley_re, cayley_re, tanh_half_eq_sinh_div_cosh_add_one]
    ring
  have him : (baseCayley (baseCircleComplex d theta)).im =
      -(Real.tanh (d / 2) * Real.sin theta) := by
    rw [baseCayley_im, cayley_im, tanh_half_eq_sinh_div_cosh_add_one]
    ring
  apply Complex.ext
  · rw [hre, Complex.polarCoord_symm_apply]
    simp only [Real.cos_neg, Complex.mul_re, Complex.ofReal_re, Complex.add_re,
      Complex.ofReal_im, Complex.I_im, mul_one, Complex.I_re, mul_zero,
      sub_zero, add_zero]
    ring
  · rw [him, Complex.polarCoord_symm_apply]
    simp only [Real.sin_neg, Complex.mul_im, Complex.ofReal_im, Complex.add_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
      add_zero]
    ring

/-- The Cayley Euclidean polar density is exactly the native hyperbolic radial density. -/
theorem baseCayley_polar_radial_density (d : ℝ) :
    (4 * Real.tanh (d / 2) / (1 - Real.tanh (d / 2) ^ 2) ^ 2) *
        (1 / (2 * Real.cosh (d / 2) ^ 2)) = Real.sinh d := by
  have hcosh : Real.cosh (d / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hpyth := HTGeometry.one_sub_tanh_sq (d / 2)
  have hsinh : Real.sinh d =
      Real.sinh (d / 2) * Real.cosh (d / 2) + Real.cosh (d / 2) * Real.sinh (d / 2) := by
    convert Real.sinh_add (d / 2) (d / 2) using 1; ring
  rw [hpyth, Real.tanh_eq_sinh_div_cosh, hsinh]
  field_simp [hcosh]
  ring

/-- Inverse Cayley sends the literal polar image back to the literal native
circle.  This is an equality of the actual chart points, not a replacement
coordinate system. -/
theorem diskToUpper_polar_eq_baseCircle (d theta : ℝ) :
    diskToUpper (Complex.polarCoord.symm (Real.tanh (d / 2), -theta)) =
      baseCircleComplex d theta := by
  rw [← baseCayley_eq_polarCoord]
  have him : 0 < (baseCircleComplex d theta).im := by
    simp only [baseCircleComplex, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    exact one_div_pos.mpr (denominator_pos d theta)
  simpa only [baseCayley, upperToDisk] using diskToUpper_upperToDisk him

/-- At positive native radius, the exact disk-polar density is the literal
native-circle density.  The angle sign is retained from `baseCayley_eq_polarCoord`. -/
theorem diskPolarDensity_tanh_eq_nativeCircle {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) {d : ℝ} (hd : d ∈ Ioi (0 : ℝ)) (theta : ℝ) :
    (1 / (2 * Real.cosh (d / 2) ^ 2)) •
        diskPolarDensity f (Real.tanh (d / 2), theta) =
      Real.sinh d • f (baseCircleComplex d (-theta)) := by
  have hradial : 0 < Real.tanh (d / 2) := by
    have hd0 : 0 < d := Set.mem_Ioi.mp hd
    have hhalf : 0 < d / 2 := by linarith
    have hmono := HTGeometry.tanh_strictMono hhalf
    rwa [Real.tanh_zero] at hmono
  have hnorm : Complex.normSq
      (Complex.polarCoord.symm (Real.tanh (d / 2), theta)) = Real.tanh (d / 2) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, abs_of_pos hradial]
  have hcircle : diskToUpper
      (Complex.polarCoord.symm (Real.tanh (d / 2), theta)) =
      baseCircleComplex d (-theta) := by
    simpa only [neg_neg] using diskToUpper_polar_eq_baseCircle d (-theta)
  rw [diskPolarDensity, hnorm, hcircle]
  simp only [smul_smul]
  have hcoefficient :
      (1 / (2 * Real.cosh (d / 2) ^ 2)) *
          (Real.tanh (d / 2) * (4 / (1 - Real.tanh (d / 2) ^ 2) ^ 2)) =
        Real.sinh d := by
    calc
      (1 / (2 * Real.cosh (d / 2) ^ 2)) *
          (Real.tanh (d / 2) * (4 / (1 - Real.tanh (d / 2) ^ 2) ^ 2)) =
          (4 * Real.tanh (d / 2) / (1 - Real.tanh (d / 2) ^ 2) ^ 2) *
            (1 / (2 * Real.cosh (d / 2) ^ 2)) := by ring
      _ = Real.sinh d := baseCayley_polar_radial_density d
  rw [hcoefficient]

attribute [instance] instInnerProductSpaceRealComplex RCLike.toInnerProductSpaceReal
  NormedSpace.complexToReal

/-- Literal global hyperbolic-area realization of the native circle about `I`.
This transports the actual upper-half-plane source through inverse Cayley and
the native polar chart; it does not substitute a proxy circle or reverse the
chart orientation. -/
theorem integral_hyperbolic_eq_nativeCircle_polar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E)
    (hf : IntegrableOn (diskPolarDensity f)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)) :
    (∫ z in {z : ℂ | 0 < z.im}, (z.im)⁻¹ ^ 2 • f z) =
      ∫ d in Ioi (0 : ℝ), ∫ theta in Ioo (-Real.pi) Real.pi,
        Real.sinh d • f (baseCircleComplex d (-theta)) := by
  rw [integral_diskToUpper_hyperbolic_polar_tanh f hf]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro d hd
  dsimp only
  rw [← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro theta _
  exact diskPolarDensity_tanh_eq_nativeCircle f hd theta

end
end RHTower.D4BMNativeCircle
