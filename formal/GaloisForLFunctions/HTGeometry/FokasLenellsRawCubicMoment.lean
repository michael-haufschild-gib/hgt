import GaloisForLFunctions.HTGeometry.FokasLenellsRawMomentIdentities
import GaloisForLFunctions.HTGeometry.FokasLenellsRawCoefficientEntries

/-!
# The genuine cubic reflection coefficient is twice the compatibility moment

The actual scattering matrix was constructed from the spatial Lax flow. Its
third-order coefficient now reduces to the moment displayed in equations
(3.51)–(3.52) of arXiv:2607.19649. No time evolution or PDE compatibility is
assumed. The same identity therefore exposes the precise additional condition
needed for this coefficient to vanish.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The actual lower-left cubic scattering coefficient is exactly twice the displayed moment. -/
theorem rawScatteringCubicCoefficient_lower (q : SchwartzMap ℝ ℂ) :
    rawScatteringCubicCoefficient q 1 0 = 2*compatibilityMoment q := by
  have hn : Integrable (fun x : ℝ => deriv q x*rawMixedPrimitive q x) := by
    have hh := integrable_schwartz_mul_rawMixedPrimitive q (SchwartzMap.derivCLM ℂ ℂ q)
    simpa only [SchwartzMap.derivCLM_apply] using hh
  have h1 : Integrable (fun x : ℝ => (-I)*(deriv q x*rawMixedPrimitive q x)) := hn.const_mul (-I)
  have h2 : Integrable (fun x : ℝ => (I*q 0)*(deriv q x*q (-x))) :=
    (integrable_derivative_reflected_product q).const_mul (I*q 0)
  have h3 : Integrable (fun x : ℝ => (I*(q 0)^(2 : ℕ))*deriv q x) := by
    have hh : Integrable (fun x : ℝ => (I*(q 0)^(2 : ℕ))*(SchwartzMap.derivCLM ℂ ℂ q) x) :=
      (SchwartzMap.derivCLM ℂ ℂ q).integrable.const_mul _
    simpa only [SchwartzMap.derivCLM_apply] using hh
  have h4 : Integrable (fun x : ℝ => (2 : ℂ)*((x : ℂ)*deriv q x)) :=
    (integrable_coordinate_derivative q).const_mul 2
  have he : (fun x : ℝ => (rawThirdIntegrand q 0 (1,0) x).2) =
      fun x => (-I)*(deriv q x*rawMixedPrimitive q x)+(I*q 0)*(deriv q x*q (-x))-
        (I*(q 0)^(2 : ℕ))*deriv q x-(2 : ℂ)*((x : ℂ)*deriv q x) := by
    funext x
    rw [rawThirdIntegrand_zero_lower]
    ring
  have h12 : Integrable (fun x : ℝ => (-I)*(deriv q x*rawMixedPrimitive q x)+
      (I*q 0)*(deriv q x*q (-x))) := by convert! h1.add h2
  have h123 : Integrable (fun x : ℝ => (-I)*(deriv q x*rawMixedPrimitive q x)+
      (I*q 0)*(deriv q x*q (-x))-(I*(q 0)^(2 : ℕ))*deriv q x) := by convert! h12.sub h3
  rw [rawScatteringCubicCoefficient_lower_integral,he,
    integral_sub h123 h4,integral_sub h12 h3,integral_add h1 h2]
  simp only [integral_const_mul,integral_q_deriv_mul_rawMixedPrimitive,
    integral_derivative_reflected_product,RHTower.integral_deriv_schwartz_eq_zero,
    integral_coordinate_derivative,integral_square_reflected_derivative,compatibilityMoment_eq]
  ring

/-- Cubic reflection cancellation is exactly the initial-data compatibility moment, not automatic decay. -/
theorem rawScatteringCubicCoefficient_lower_zero_iff (q : SchwartzMap ℝ ℂ) :
    rawScatteringCubicCoefficient q 1 0 = 0 ↔ compatibilityMoment q = 0 := by
  rw [rawScatteringCubicCoefficient_lower]
  exact mul_eq_zero.trans (or_iff_right (by norm_num : (2 : ℂ) ≠ 0))

/-- The actual reflection quotient converges, with its coefficient evaluated in closed form. -/
theorem rawReflection_cubic_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun k : ℝ => rawScatteringMatrix q k 1 0/(k : ℂ)^(3 : ℕ))
      (𝓝[≠] 0) (𝓝 (2*compatibilityMoment q)) := by
  have hc : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) := by fun_prop
  have hh := (hc.tendsto (rawScatteringCubicCoefficient q)).comp
    (rawScatteringMatrix_cubic_quotient_tendsto q)
  change Tendsto (fun k : ℝ =>
    (((k : ℂ)^(3 : ℕ))⁻¹ • (rawScatteringMatrix q k-1-(k : ℂ)^(2 : ℕ) • rawScatteringQuadraticCoefficient q)) 1 0)
    (𝓝[≠] 0) (𝓝 (rawScatteringCubicCoefficient q 1 0)) at hh
  simpa only [Matrix.smul_apply,Matrix.sub_apply,Matrix.one_apply_ne (by omega : (1 : Fin 2) ≠ 0),
    rawScatteringQuadraticCoefficient_lower,smul_zero,sub_zero,smul_eq_mul,mul_zero,zero_mul,
    rawScatteringCubicCoefficient_lower,div_eq_mul_inv,mul_comm] using hh

/-- The even projection has cubic reflection equal to twice the original mass. -/
theorem rawScatteringCubicCoefficient_evenInitialPart (q : SchwartzMap ℝ ℂ) :
    rawScatteringCubicCoefficient (evenInitialPart q) 1 0 = 2*∫ x : ℝ, q x := by
  rw [rawScatteringCubicCoefficient_lower,compatibilityMoment_evenInitialPart]

/-- The odd projection has no cubic reflection coefficient. -/
theorem rawScatteringCubicCoefficient_oddInitialPart (q : SchwartzMap ℝ ℂ) :
    rawScatteringCubicCoefficient (oddInitialPart q) 1 0 = 0 := by
  rw [rawScatteringCubicCoefficient_lower,compatibilityMoment_oddInitialPart,mul_zero]

/-- The normalized Gaussian has a nonzero genuine cubic reflection coefficient. -/
theorem rawScatteringCubicCoefficient_gaussian (a : ℝ) :
    rawScatteringCubicCoefficient (compatibilityGaussian a) 1 0 = 2 := by
  rw [rawScatteringCubicCoefficient_lower,compatibilityMoment_gaussian,mul_one]

/-- The nonzero cubic coefficient persists for the explicit small-scattering Gaussian family. -/
theorem rawScatteringCubicCoefficient_globalSmallGaussian (a : ℝ) :
    rawScatteringCubicCoefficient (globalSmallScatteringPotential (compatibilityGaussian a)) 1 0 =
      2*(globalScatteringScale (compatibilityGaussian a) : ℂ) := by
  rw [rawScatteringCubicCoefficient_lower,compatibilityMoment_globalSmallGaussian]

theorem rawScatteringCubicCoefficient_globalSmallGaussian_ne_zero (a : ℝ) :
    rawScatteringCubicCoefficient (globalSmallScatteringPotential (compatibilityGaussian a)) 1 0 ≠ 0 := by
  rw [rawScatteringCubicCoefficient_lower]
  exact mul_ne_zero (by norm_num) (compatibilityMoment_globalSmallGaussian_ne_zero a)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
