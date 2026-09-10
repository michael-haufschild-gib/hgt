import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedHigherSpectrum
import GaloisForLFunctions.HTGeometry.DistributionalLinearODE

/-! Entire evolution by the actual derivative of order `m` on bounded genuine derivative chains. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPowerExponentialLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPowerExponentialChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPowerExponentialChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPowerExponentialChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPowerExponentialEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPowerExponentialEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPowerExponentialEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPowerExponentialEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPowerExponentialEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


/-- The actual exponential of the chosen power of the genuine bounded derivative shift. -/
def causalBoundedPowerExponential (m : ℕ) (z : ℂ) : causalBoundedChain →L[ℂ] causalBoundedChain :=
  NormedSpace.exp (z • causalBoundedChainShift^m)

/-- Apply the corpus's genuine operator series to the actual derivative of order `m`. -/
theorem causalBoundedPowerExponential_series (m : ℕ) (z : ℂ) (u : causalBoundedChain) :
    causalBoundedPowerExponential m z u = ∑' k : ℕ,
      (((k.factorial : ℂ))⁻¹*z^k) • (((causalBoundedChainShift^m)^k) u) :=
  exp_smul_apply_eq_tsum (causalBoundedChainShift^m) z u

private theorem power_power_norm_le (m k : ℕ) (u : causalBoundedChain) :
    ‖((causalBoundedChainShift^m)^k) u‖ ≤ ‖u‖ := by
  have hp : ‖causalBoundedChainShift^m‖^k = 1 :=
    (congrArg (fun r : ℝ => r^k) (norm_causalBoundedChainShift_pow m)).trans (one_pow k)
  have he := congrArg (fun r : ℝ => r*‖u‖) hp
  exact (norm_pow_apply_le (causalBoundedChainShift^m) k u).trans_eq (he.trans (one_mul _))

private theorem power_majorant_hasSum (z : ℂ) (u : causalBoundedChain) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ))⁻¹*‖z‖^k*‖u‖) (Real.exp ‖z‖*‖u‖) := by
  simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖z‖).mul_right ‖u‖

private theorem power_term_norm_le (m : ℕ) (z : ℂ) (u : causalBoundedChain) (k : ℕ) :
    ‖(((k.factorial : ℂ))⁻¹*z^k) • (((causalBoundedChainShift^m)^k) u)‖ ≤
      ((k.factorial : ℝ))⁻¹*‖z‖^k*‖u‖ := by
  have hc : ‖((k.factorial : ℂ))⁻¹*z^k‖ = ((k.factorial : ℝ))⁻¹*‖z‖^k := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  have he := congrArg (fun r : ℝ => r*‖((causalBoundedChainShift^m)^k) u‖) hc
  exact (norm_smul _ _).trans_le (he.trans_le
    (mul_le_mul_of_nonneg_left (power_power_norm_le m k u) (by positivity)))

/-- Every actual arbitrary-order derivative orbit has exponential type at most one. -/
theorem causalBoundedPowerExponential_norm_le (m : ℕ) (z : ℂ) (u : causalBoundedChain) :
    ‖causalBoundedPowerExponential m z u‖ ≤ Real.exp ‖z‖*‖u‖ := by
  have he := congrArg (fun v : causalBoundedChain => ‖v‖) (causalBoundedPowerExponential_series m z u)
  exact he.trans_le (tsum_of_norm_bounded (power_majorant_hasSum z u) (power_term_norm_le m z u))

/-- The whole actual arbitrary-order derivative operator satisfies the same exponential-type bound. -/
theorem norm_causalBoundedPowerExponential_le (m : ℕ) (z : ℂ) :
    ‖causalBoundedPowerExponential m z‖ ≤ Real.exp ‖z‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le (causalBoundedPowerExponential_norm_le m z)

/-- The actual complex-time derivative is composition with the genuine derivative of order `m`. -/
theorem causalBoundedPowerExponential_hasDerivAt (m : ℕ) (z : ℂ) :
    HasDerivAt (causalBoundedPowerExponential m)
      (causalBoundedChainShift^m * causalBoundedPowerExponential m z) z :=
  hasDerivAt_exp_smul_const' (causalBoundedChainShift^m) z

/-- The genuine arbitrary-order derivative evolution starts at the actual identity. -/
theorem causalBoundedPowerExponential_zero (m : ℕ) : causalBoundedPowerExponential m 0 = 1 := by
  simp only [causalBoundedPowerExponential, zero_smul, NormedSpace.exp_zero]

/-- Read an original Hilbert-valued derivative coordinate of the genuine arbitrary-order derivative evolution. -/
def causalBoundedPowerEntireOrbit (m j : ℕ) (u : causalBoundedChain) (z : ℂ) : hardyL2ᗮ :=
  causalBoundedChainCoordinate j (causalBoundedPowerExponential m z u)

/-- Complex time differentiation advances the genuine spatial derivative hierarchy by its full order. -/
theorem causalBoundedPowerEntireOrbit_hasDerivAt (m j : ℕ) (u : causalBoundedChain) (z : ℂ) :
    HasDerivAt (causalBoundedPowerEntireOrbit m j u) (causalBoundedPowerEntireOrbit m (j+m) u z) z := by
  have h := (causalBoundedPowerExponential_hasDerivAt m z).clm_apply (hasDerivAt_const z u)
  have he : HasDerivAt (fun w : ℂ => causalBoundedPowerExponential m w u)
      ((causalBoundedChainShift^m) (causalBoundedPowerExponential m z u)) z := by
    convert! h using 1
    simp only [map_zero, add_zero]
    rfl
  have hc := (causalBoundedChainCoordinate j).hasFDerivAt.comp_hasDerivAt z he
  have hd := causalBoundedChainShift_pow_coordinate m j (causalBoundedPowerExponential m z u)
  have ht := congrArg (fun v : hardyL2ᗮ => HasDerivAt (causalBoundedPowerEntireOrbit m j u) v z) hd
  exact ht.mp hc

/-- Each actual arbitrary-order derivative coordinate orbit is entire in the original Hilbert norm. -/
theorem causalBoundedPowerEntireOrbit_analyticAt (m j : ℕ) (u : causalBoundedChain) (z : ℂ) :
    AnalyticAt ℂ (causalBoundedPowerEntireOrbit m j u) z :=
  (show Differentiable ℂ (causalBoundedPowerEntireOrbit m j u) from fun w =>
    (causalBoundedPowerEntireOrbit_hasDerivAt m j u w).differentiableAt).analyticAt z

/-- The original coordinate is the initial datum of its actual arbitrary-order derivative evolution. -/
theorem causalBoundedPowerEntireOrbit_zero (m j : ℕ) (u : causalBoundedChain) :
    causalBoundedPowerEntireOrbit m j u 0 = causalBoundedChainCoordinate j u :=
  congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => causalBoundedChainCoordinate j (A u))
    (causalBoundedPowerExponential_zero m)

/-- The original causal generator still reads the next genuine derivative at every complex time. -/
theorem causalBoundedPowerEntireOrbit_hasRightDeriv (m j : ℕ) (u : causalBoundedChain) (z : ℂ) :
    HasDerivWithinAt (causalForwardOrbit (causalBoundedPowerEntireOrbit m j u z))
      (causalBoundedPowerEntireOrbit m (j+1) u z) (Ioi 0) 0 :=
  causalBoundedChainCoordinate_hasRightDeriv j (causalBoundedPowerExponential m z u)

end
end RHTower.FokasLenells
