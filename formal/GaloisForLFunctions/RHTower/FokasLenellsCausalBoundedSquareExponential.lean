import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPowerSpectrum
import GaloisForLFunctions.HTGeometry.DistributionalLinearODE

/-! Entire evolution by the actual second derivative on bounded genuine derivative chains. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fokasLenellsCausalBoundedSquareExponentialInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance fokasLenellsCausalBoundedSquareExponentialInst2 : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance fokasLenellsCausalBoundedSquareExponentialInst3 : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance fokasLenellsCausalBoundedSquareExponentialInst4 : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance fokasLenellsCausalBoundedSquareExponentialInst5 : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance fokasLenellsCausalBoundedSquareExponentialInst6 : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance fokasLenellsCausalBoundedSquareExponentialInst7 : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance fokasLenellsCausalBoundedSquareExponentialInst8 : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance fokasLenellsCausalBoundedSquareExponentialInst9 : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


/-- The actual exponential of the square of the genuine bounded derivative shift. -/
def causalBoundedSquareExponential (z : ℂ) : causalBoundedChain →L[ℂ] causalBoundedChain :=
  NormedSpace.exp (z • causalBoundedChainShift^(2 : ℕ))

/-- Apply the corpus's genuine operator series to the actual second derivative. -/
theorem causalBoundedSquareExponential_series (z : ℂ) (u : causalBoundedChain) :
    causalBoundedSquareExponential z u = ∑' k : ℕ,
      (((k.factorial : ℂ))⁻¹*z^k) • (((causalBoundedChainShift^(2 : ℕ))^k) u) :=
  exp_smul_apply_eq_tsum (causalBoundedChainShift^(2 : ℕ)) z u

private theorem square_power_norm_le (k : ℕ) (u : causalBoundedChain) :
    ‖((causalBoundedChainShift^(2 : ℕ))^k) u‖ ≤ ‖u‖ := by
  have hp : ‖causalBoundedChainShift^(2 : ℕ)‖^k = 1 :=
    (congrArg (fun r : ℝ => r^k) (norm_causalBoundedChainShift_pow 2)).trans (one_pow k)
  have he := congrArg (fun r : ℝ => r*‖u‖) hp
  exact (norm_pow_apply_le (causalBoundedChainShift^(2 : ℕ)) k u).trans_eq (he.trans (one_mul _))

private theorem square_majorant_hasSum (z : ℂ) (u : causalBoundedChain) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ))⁻¹*‖z‖^k*‖u‖) (Real.exp ‖z‖*‖u‖) := by
  simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖z‖).mul_right ‖u‖

private theorem square_term_norm_le (z : ℂ) (u : causalBoundedChain) (k : ℕ) :
    ‖(((k.factorial : ℂ))⁻¹*z^k) • (((causalBoundedChainShift^(2 : ℕ))^k) u)‖ ≤
      ((k.factorial : ℝ))⁻¹*‖z‖^k*‖u‖ := by
  have hc : ‖((k.factorial : ℂ))⁻¹*z^k‖ = ((k.factorial : ℝ))⁻¹*‖z‖^k := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  have he := congrArg (fun r : ℝ => r*‖((causalBoundedChainShift^(2 : ℕ))^k) u‖) hc
  exact (norm_smul _ _).trans_le (he.trans_le
    (mul_le_mul_of_nonneg_left (square_power_norm_le k u) (by positivity)))

/-- Every actual second-derivative orbit has exponential type at most one. -/
theorem causalBoundedSquareExponential_norm_le (z : ℂ) (u : causalBoundedChain) :
    ‖causalBoundedSquareExponential z u‖ ≤ Real.exp ‖z‖*‖u‖ := by
  have he := congrArg (fun v : causalBoundedChain => ‖v‖) (causalBoundedSquareExponential_series z u)
  exact he.trans_le (tsum_of_norm_bounded (square_majorant_hasSum z u) (square_term_norm_le z u))

/-- The whole actual second-derivative operator satisfies the same exponential-type bound. -/
theorem norm_causalBoundedSquareExponential_le (z : ℂ) :
    ‖causalBoundedSquareExponential z‖ ≤ Real.exp ‖z‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le (causalBoundedSquareExponential_norm_le z)

/-- The actual complex-time derivative is composition with the genuine second derivative. -/
theorem causalBoundedSquareExponential_hasDerivAt (z : ℂ) :
    HasDerivAt causalBoundedSquareExponential
      (causalBoundedChainShift^(2 : ℕ) * causalBoundedSquareExponential z) z :=
  hasDerivAt_exp_smul_const' (causalBoundedChainShift^(2 : ℕ)) z

/-- The genuine second-derivative evolution starts at the actual identity. -/
theorem causalBoundedSquareExponential_zero : causalBoundedSquareExponential 0 = 1 := by
  simp only [causalBoundedSquareExponential, zero_smul, NormedSpace.exp_zero]

/-- Read an original Hilbert-valued derivative coordinate of the genuine second-derivative evolution. -/
def causalBoundedSquareEntireOrbit (j : ℕ) (u : causalBoundedChain) (z : ℂ) : hardyL2ᗮ :=
  causalBoundedChainCoordinate j (causalBoundedSquareExponential z u)

/-- Complex time differentiation advances the genuine spatial derivative hierarchy by two orders. -/
theorem causalBoundedSquareEntireOrbit_hasDerivAt (j : ℕ) (u : causalBoundedChain) (z : ℂ) :
    HasDerivAt (causalBoundedSquareEntireOrbit j u) (causalBoundedSquareEntireOrbit (j+2) u z) z := by
  have h := (causalBoundedSquareExponential_hasDerivAt z).clm_apply (hasDerivAt_const z u)
  have he : HasDerivAt (fun w : ℂ => causalBoundedSquareExponential w u)
      ((causalBoundedChainShift^(2 : ℕ)) (causalBoundedSquareExponential z u)) z := by
    convert! h using 1
    simp only [map_zero, add_zero]
    rfl
  exact (causalBoundedChainCoordinate j).hasFDerivAt.comp_hasDerivAt z he

/-- Each actual second-derivative coordinate orbit is entire in the original Hilbert norm. -/
theorem causalBoundedSquareEntireOrbit_analyticAt (j : ℕ) (u : causalBoundedChain) (z : ℂ) :
    AnalyticAt ℂ (causalBoundedSquareEntireOrbit j u) z :=
  (show Differentiable ℂ (causalBoundedSquareEntireOrbit j u) from fun w =>
    (causalBoundedSquareEntireOrbit_hasDerivAt j u w).differentiableAt).analyticAt z

/-- The original coordinate is the initial datum of its actual second-derivative evolution. -/
theorem causalBoundedSquareEntireOrbit_zero (j : ℕ) (u : causalBoundedChain) :
    causalBoundedSquareEntireOrbit j u 0 = causalBoundedChainCoordinate j u :=
  congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => causalBoundedChainCoordinate j (A u))
    causalBoundedSquareExponential_zero

/-- The original causal generator still reads the next genuine derivative at every complex time. -/
theorem causalBoundedSquareEntireOrbit_hasRightDeriv (j : ℕ) (u : causalBoundedChain) (z : ℂ) :
    HasDerivWithinAt (causalForwardOrbit (causalBoundedSquareEntireOrbit j u z))
      (causalBoundedSquareEntireOrbit (j+1) u z) (Ioi 0) 0 :=
  causalBoundedChainCoordinate_hasRightDeriv j (causalBoundedSquareExponential z u)

end
end RHTower.FokasLenells
