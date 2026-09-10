import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPolynomialPointSpectrum
import GaloisForLFunctions.HTGeometry.DistributionalLinearODE

/-! Actual entire polynomial evolution on the genuine bounded Cauchy derivative space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialFlowLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPolynomialFlowChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPolynomialFlowChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPolynomialFlowChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPolynomialFlowEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPolynomialFlowEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPolynomialFlowEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPolynomialFlowEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPolynomialFlowEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open Polynomial

/-- A finite coefficient bound for the actual polynomial derivative operator. -/
def causalBoundedPolynomialSize (p : ℂ[X]) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree+1), ‖p.coeff k‖

/-- The coefficient bound is nonnegative for every complex polynomial. -/
theorem causalBoundedPolynomialSize_nonneg (p : ℂ[X]) : 0 ≤ causalBoundedPolynomialSize p :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- Genuine bounded derivative chains control every polynomial combination by its coefficients. -/
theorem norm_causalBoundedPolynomialOperator_le (p : ℂ[X]) :
    ‖causalBoundedPolynomialOperator p‖ ≤ causalBoundedPolynomialSize p := by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    (causalBoundedPolynomialOperator_sum p)
  have hs : ‖(∑ k ∈ Finset.range (p.natDegree+1), p.coeff k • causalBoundedChainShift^k :
      causalBoundedChain →L[ℂ] causalBoundedChain)‖ ≤
      ∑ k ∈ Finset.range (p.natDegree+1), ‖p.coeff k • causalBoundedChainShift^k‖ := norm_sum_le _ _
  have ht := Finset.sum_congr (s₁ := Finset.range (p.natDegree+1)) rfl (fun k _ =>
    (norm_smul (p.coeff k) (causalBoundedChainShift^k)).trans
      ((congrArg (fun r : ℝ => ‖p.coeff k‖*r) (norm_causalBoundedChainShift_pow k)).trans (mul_one _)))
  exact he.trans_le (hs.trans_eq ht)

/-- Actual bounded polynomial derivatives evolve through the convergent operator exponential. -/
def causalBoundedPolynomialExponential (p : ℂ[X]) (z : ℂ) :
    causalBoundedChain →L[ℂ] causalBoundedChain :=
  NormedSpace.exp (z • causalBoundedPolynomialOperator p)

/-- The genuine polynomial flow is the literal convergent exponential series on each chain. -/
theorem causalBoundedPolynomialExponential_series (p : ℂ[X]) (z : ℂ) (u : causalBoundedChain) :
    causalBoundedPolynomialExponential p z u = ∑' k : ℕ,
      (((k.factorial : ℂ))⁻¹*z^k) • (((causalBoundedPolynomialOperator p)^k) u) :=
  exp_smul_apply_eq_tsum (causalBoundedPolynomialOperator p) z u

private theorem polynomial_majorant_hasSum (p : ℂ[X]) (z : ℂ) (u : causalBoundedChain) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ))⁻¹ *
      (‖z‖*‖causalBoundedPolynomialOperator p‖)^k * ‖u‖)
      (Real.exp (‖z‖*‖causalBoundedPolynomialOperator p‖)*‖u‖) := by
  simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (‖z‖*‖causalBoundedPolynomialOperator p‖)).mul_right ‖u‖

private theorem polynomial_term_norm_le (p : ℂ[X]) (z : ℂ) (u : causalBoundedChain) (k : ℕ) :
    ‖(((k.factorial : ℂ))⁻¹*z^k) • (((causalBoundedPolynomialOperator p)^k) u)‖ ≤
      ((k.factorial : ℝ))⁻¹ * (‖z‖*‖causalBoundedPolynomialOperator p‖)^k * ‖u‖ := by
  have hc : ‖((k.factorial : ℂ))⁻¹*z^k‖ = ((k.factorial : ℝ))⁻¹*‖z‖^k := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  have he := congrArg (fun r : ℝ => r*‖((causalBoundedPolynomialOperator p)^k) u‖) hc
  have hb := mul_le_mul_of_nonneg_left (norm_pow_apply_le (causalBoundedPolynomialOperator p) k u)
    (show 0 ≤ ((k.factorial : ℝ))⁻¹*‖z‖^k by positivity)
  have hr : (((k.factorial : ℝ))⁻¹*‖z‖^k) * (‖causalBoundedPolynomialOperator p‖^k*‖u‖) =
      ((k.factorial : ℝ))⁻¹ * (‖z‖*‖causalBoundedPolynomialOperator p‖)^k * ‖u‖ := by
    rw [mul_pow]; ring
  exact (norm_smul _ _).trans_le (he.trans_le (hb.trans_eq hr))

/-- Every actual polynomial orbit has an exponential bound in its true operator norm. -/
theorem causalBoundedPolynomialExponential_norm_le (p : ℂ[X]) (z : ℂ) (u : causalBoundedChain) :
    ‖causalBoundedPolynomialExponential p z u‖ ≤
      Real.exp (‖z‖*‖causalBoundedPolynomialOperator p‖)*‖u‖ := by
  have he := congrArg (fun v : causalBoundedChain => ‖v‖)
    (causalBoundedPolynomialExponential_series p z u)
  exact he.trans_le (tsum_of_norm_bounded (polynomial_majorant_hasSum p z u)
    (polynomial_term_norm_le p z u))

/-- The entire polynomial flow has the corresponding operator norm bound. -/
theorem norm_causalBoundedPolynomialExponential_le (p : ℂ[X]) (z : ℂ) :
    ‖causalBoundedPolynomialExponential p z‖ ≤ Real.exp (‖z‖*‖causalBoundedPolynomialOperator p‖) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le (causalBoundedPolynomialExponential_norm_le p z)

/-- A finite formula in the coefficients controls the complete actual polynomial flow. -/
theorem norm_causalBoundedPolynomialExponential_le_coefficients (p : ℂ[X]) (z : ℂ) :
    ‖causalBoundedPolynomialExponential p z‖ ≤ Real.exp (‖z‖*causalBoundedPolynomialSize p) :=
  (norm_causalBoundedPolynomialExponential_le p z).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_causalBoundedPolynomialOperator_le p) (norm_nonneg z)))

/-- Time differentiation composes with the actual polynomial differential operator. -/
theorem causalBoundedPolynomialExponential_hasDerivAt (p : ℂ[X]) (z : ℂ) :
    HasDerivAt (causalBoundedPolynomialExponential p)
      (causalBoundedPolynomialOperator p * causalBoundedPolynomialExponential p z) z :=
  hasDerivAt_exp_smul_const' (causalBoundedPolynomialOperator p) z

/-- The actual polynomial flow starts at the identity. -/
theorem causalBoundedPolynomialExponential_zero (p : ℂ[X]) :
    causalBoundedPolynomialExponential p 0 = 1 := by
  simp only [causalBoundedPolynomialExponential, zero_smul, NormedSpace.exp_zero]

end
end RHTower.FokasLenells
