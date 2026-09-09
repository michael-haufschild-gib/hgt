import GaloisForLFunctions.RHTower.FokasLenellsCausalComplexShift

/-! Unit vectors with exact exponentially small imaginary-axis residuals, built from the actual
rational eigenvectors of the completed causal Cauchy generator. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Exact left-half-plane rates approaching any given imaginary-axis point. -/
def causalBoundaryRate (b ω : ℝ) : {z : ℂ // z.re < 0} :=
  ⟨-(Real.exp b : ℂ) + (ω : ℂ)*I, by
    simpa only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero, add_zero] using neg_neg_of_pos (Real.exp_pos b)⟩

/-- A normalized actual-domain rational eigenvector approaching the chosen boundary frequency. -/
def causalBoundaryEigenvector (b ω : ℝ) : causalGeneratorDomain :=
  ((‖causalLeftEigenvector (causalBoundaryRate b ω)‖ : ℝ) : ℂ)⁻¹ •
    causalLeftEigenvector (causalBoundaryRate b ω)

/-- The boundary test vectors have exactly unit data norm. -/
theorem norm_causalBoundaryEigenvector (b ω : ℝ) : ‖causalBoundaryEigenvector b ω‖ = 1 := by
  have hn := norm_ne_zero_iff.mpr (causalLeftEigenvector_ne_zero (causalBoundaryRate b ω))
  rw [causalBoundaryEigenvector, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]

/-- Every normalized boundary test vector retains the exact left-half-plane eigenvalue. -/
theorem causalGenerator_boundaryEigenvector (b ω : ℝ) :
    causalGenerator (causalBoundaryEigenvector b ω) =
      (causalBoundaryRate b ω).val • (causalBoundaryEigenvector b ω).val := by
  change causalGenerator (_ • causalLeftEigenvector (causalBoundaryRate b ω)) = _
  rw [map_smul, causalGenerator_leftEigenvector]
  change _ • ((causalBoundaryRate b ω).val • _) =
    (causalBoundaryRate b ω).val • (_ • _)
  exact smul_comm _ _ _

/-- The imaginary-axis residual is exactly the real damping times the normalized vector. -/
theorem causalComplexGeneratorShift_boundaryEigenvector (b ω : ℝ) :
    causalComplexGeneratorShift ((ω : ℂ)*I) (causalBoundaryEigenvector b ω) =
      (Real.exp b : ℂ) • (causalBoundaryEigenvector b ω).val := by
  change ((ω : ℂ)*I) • (causalBoundaryEigenvector b ω).val -
    causalGenerator (causalBoundaryEigenvector b ω) = _
  rw [causalGenerator_boundaryEigenvector]
  change ((ω : ℂ)*I) • (causalBoundaryEigenvector b ω).val -
    (-(Real.exp b : ℂ)+(ω : ℂ)*I) • (causalBoundaryEigenvector b ω).val = _
  module

/-- Every imaginary-axis point has exact unit approximate eigenvectors with residual `exp b`. -/
theorem norm_causalComplexGeneratorShift_boundaryEigenvector (b ω : ℝ) :
    ‖causalComplexGeneratorShift ((ω : ℂ)*I) (causalBoundaryEigenvector b ω)‖ = Real.exp b := by
  rw [causalComplexGeneratorShift_boundaryEigenvector, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos b)]
  change Real.exp b * ‖causalBoundaryEigenvector b ω‖ = _
  rw [norm_causalBoundaryEigenvector, mul_one]

/-- The actual imaginary-axis residual norms tend to zero along the explicit family. -/
theorem causalBoundaryEigenvector_residual_tendsto (ω : ℝ) :
    Tendsto (fun b : ℝ =>
      ‖causalComplexGeneratorShift ((ω : ℂ)*I) (causalBoundaryEigenvector b ω)‖)
      atBot (𝓝 0) := by
  simpa only [norm_causalComplexGeneratorShift_boundaryEigenvector] using Real.tendsto_exp_atBot

end
end RHTower.FokasLenells
