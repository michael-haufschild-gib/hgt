import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedExponentialGroup
import GaloisForLFunctions.HTGeometry.DistributionalLinearODE

/-! Quantitative entire growth in the actual bounded derivative-chain Banach norm.
The corpus's operator orbit series is bounded by the scalar exponential series. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- Every actual derivative-shift power remains contractive in the bounded-chain norm. -/
theorem causalBoundedChainShift_pow_norm_le (k : ℕ) (u : causalBoundedChain) :
    ‖(causalBoundedChainShift ^ k) u‖ ≤ ‖u‖ := by
  have hp : ‖causalBoundedChainShift‖^k ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) norm_causalBoundedChainShift_le
  exact (norm_pow_apply_le causalBoundedChainShift k u).trans
    ((mul_le_mul_of_nonneg_right hp (norm_nonneg u)).trans_eq (one_mul _))

/-- Apply the existing operator-series theorem to the genuine bounded derivative shift. -/
theorem causalBoundedChainExponential_series (z : ℂ) (u : causalBoundedChain) :
    causalBoundedChainExponential z u = ∑' k : ℕ,
      (((k.factorial : ℂ))⁻¹ * z^k) • ((causalBoundedChainShift^k) u) :=
  exp_smul_apply_eq_tsum causalBoundedChainShift z u

private theorem exponential_majorant_hasSum (z : ℂ) (u : causalBoundedChain) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ))⁻¹ * ‖z‖^k * ‖u‖)
      (Real.exp ‖z‖ * ‖u‖) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖z‖).mul_right ‖u‖
  simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using h

private theorem exponential_term_norm_le (z : ℂ) (u : causalBoundedChain) (k : ℕ) :
    ‖(((k.factorial : ℂ))⁻¹ * z^k) • ((causalBoundedChainShift^k) u)‖ ≤
      ((k.factorial : ℝ))⁻¹ * ‖z‖^k * ‖u‖ := by
  have hc : ‖((k.factorial : ℂ))⁻¹ * z^k‖ = ((k.factorial : ℝ))⁻¹ * ‖z‖^k := by
    rw [norm_mul, norm_pow]
    have hf : ‖((k.factorial : ℂ))⁻¹‖ = ((k.factorial : ℝ))⁻¹ := by simp
    exact congrArg (fun r : ℝ => r * ‖z‖^k) hf
  exact (norm_smul _ _).trans_le ((congrArg
    (fun r : ℝ => r * ‖(causalBoundedChainShift^k) u‖) hc).trans_le
      (mul_le_mul_of_nonneg_left (causalBoundedChainShift_pow_norm_le k u) (by positivity)))

/-- The actual entire chain evolution has exponential type at most one. -/
theorem causalBoundedChainExponential_norm_le (z : ℂ) (u : causalBoundedChain) :
    ‖causalBoundedChainExponential z u‖ ≤ Real.exp ‖z‖ * ‖u‖ := by
  exact (congrArg (fun v : causalBoundedChain => ‖v‖)
    (causalBoundedChainExponential_series z u)).trans_le
      (tsum_of_norm_bounded (exponential_majorant_hasSum z u) (exponential_term_norm_le z u))

/-- The same exponential-type estimate holds in the actual operator norm. -/
theorem norm_causalBoundedChainExponential_le (z : ℂ) :
    ‖causalBoundedChainExponential z‖ ≤ Real.exp ‖z‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_nonneg _) (causalBoundedChainExponential_norm_le z)

/-- The candidate sharp growth exponent distinguishes contracting real time from backward growth. -/
def causalBoundedGrowthExponent (z : ℂ) : ℝ := if 0 ≤ z.re then |z.im| else ‖z‖

/-- Factoring off the genuine positive-time contraction sharpens the entire growth estimate. -/
theorem norm_causalBoundedChainExponential_le_growth (z : ℂ) :
    ‖causalBoundedChainExponential z‖ ≤ Real.exp (causalBoundedGrowthExponent z) := by
  by_cases hz : 0 ≤ z.re
  · have he : causalBoundedChainExponential z =
        causalBoundedChainExponential (z.re : ℂ) *
          causalBoundedChainExponential ((z.im : ℂ)*I) := by
      have h := causalBoundedChainExponential_add (z.re : ℂ) ((z.im : ℂ)*I)
      exact (congrArg causalBoundedChainExponential (Complex.re_add_im z)).symm.trans h
    have hn : ‖causalBoundedChainExponential (z.re : ℂ)‖ = 1 :=
      norm_causalBoundedChainExponential_real ⟨z.re, hz⟩
    have hi : ‖((z.im : ℂ)*I)‖ = |z.im| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hb := norm_mul_le (causalBoundedChainExponential (z.re : ℂ))
      (causalBoundedChainExponential ((z.im : ℂ)*I))
    have hc : ‖causalBoundedChainExponential z‖ ≤
        ‖causalBoundedChainExponential ((z.im : ℂ)*I)‖ :=
      (congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖) he).trans_le
        (hb.trans_eq ((congrArg (fun r : ℝ =>
          r * ‖causalBoundedChainExponential ((z.im : ℂ)*I)‖) hn).trans (one_mul _)))
    change ‖causalBoundedChainExponential z‖ ≤ Real.exp (if 0 ≤ z.re then |z.im| else ‖z‖)
    rw [if_pos hz]
    exact hc.trans ((norm_causalBoundedChainExponential_le _).trans_eq
      (congrArg Real.exp hi))
  · simpa only [causalBoundedGrowthExponent, if_neg hz] using norm_causalBoundedChainExponential_le z

/-- One growth estimate controls every actual derivative coordinate throughout the complex plane. -/
theorem causalBoundedEntireOrbit_norm_le_growth (j : ℕ) (u : causalBoundedChain) (z : ℂ) :
    ‖causalBoundedEntireOrbit j u z‖ ≤ Real.exp (causalBoundedGrowthExponent z) * ‖u‖ :=
  (causalBoundedChainCoordinate_norm_le j _).trans
    (((causalBoundedChainExponential z).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (norm_causalBoundedChainExponential_le_growth z) (norm_nonneg u)))

end
end RHTower.FokasLenells
