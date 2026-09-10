import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPolynomialExponential

/-! Actual entire polynomial evolution on the genuine bounded Cauchy derivative space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialModesLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPolynomialModesChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPolynomialModesChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPolynomialModesChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPolynomialModesEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPolynomialModesEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPolynomialModesEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPolynomialModesEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPolynomialModesEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open Polynomial

private theorem polynomial_exp_eigenvector (p : ℂ[X]) (z q : ℂ) (u : causalBoundedChain)
    (he : (causalBoundedPolynomialOperator p) u = q • u) :
    causalBoundedPolynomialExponential p z u = Complex.exp (z*q) • u := by
  have hp (k : ℕ) : ((causalBoundedPolynomialOperator p)^k) u = q^k • u := by
    induction k with
    | zero => simp only [pow_zero, one_smul]; rfl
    | succ k ih =>
      have ha := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
        (pow_succ' (causalBoundedPolynomialOperator p) k)
      have hb := congrArg (fun v : causalBoundedChain => (causalBoundedPolynomialOperator p) v) ih
      have hc := (causalBoundedPolynomialOperator p).map_smul (q^k) u
      have hd := congrArg (fun v : causalBoundedChain => q^k • v) he
      have hf := smul_smul (q^k) q u
      have hg := congrArg (fun c : ℂ => c • u) (pow_succ q k).symm
      exact ha.trans (hb.trans (hc.trans (hd.trans (hf.trans hg))))
  have hc : HasSum (fun k : ℕ => ((k.factorial : ℂ))⁻¹ * (z*q)^k) (Complex.exp (z*q)) := by
    simpa only [smul_eq_mul, Complex.exp_eq_exp_ℂ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z*q)
  calc
    _ = ∑' k : ℕ, (((k.factorial : ℂ))⁻¹*z^k) • (((causalBoundedPolynomialOperator p)^k) u) :=
      causalBoundedPolynomialExponential_series p z u
    _ = ∑' k : ℕ, (((k.factorial : ℂ))⁻¹*(z*q)^k) • u := by
      apply tsum_congr
      intro k
      have ha := congrArg (fun v : causalBoundedChain => (((k.factorial : ℂ))⁻¹*z^k) • v) (hp k)
      have hb := smul_smul (((k.factorial : ℂ))⁻¹*z^k) (q^k) u
      have he' : (((k.factorial : ℂ))⁻¹*z^k) * q^k = ((k.factorial : ℂ))⁻¹*(z*q)^k := by
        rw [mul_pow, mul_assoc]
      exact ha.trans (hb.trans (congrArg (fun c : ℂ => c • u) he'))
    _ = _ := (hc.smul_const u).tsum_eq

/-- Each concrete rational chain evolves by its evaluated polynomial exponential character. -/
theorem causalBoundedPolynomialExponential_diskEigenchain (p : ℂ[X]) (z : ℂ)
    (q : causalBoundedDiskRate) :
    causalBoundedPolynomialExponential p z (causalBoundedDiskEigenchain q) =
      Complex.exp (z*p.eval q.val) • causalBoundedDiskEigenchain q :=
  polynomial_exp_eigenvector p z (p.eval q.val) (causalBoundedDiskEigenchain q)
    (causalBoundedPolynomialOperator_diskEigenchain p q)

/-- Actual rational initial data give exact growth or decay for every polynomial differential flow. -/
theorem norm_causalBoundedPolynomialExponential_diskEigenchain (p : ℂ[X]) (z : ℂ)
    (q : causalBoundedDiskRate) :
    ‖causalBoundedPolynomialExponential p z (causalBoundedDiskEigenchain q)‖ =
      Real.exp ((z*p.eval q.val).re) := by
  have he := congrArg (fun u : causalBoundedChain => ‖u‖)
    (causalBoundedPolynomialExponential_diskEigenchain p z q)
  have hs := norm_smul (Complex.exp (z*p.eval q.val)) (causalBoundedDiskEigenchain q)
  have hn := congrArg (fun r : ℝ => ‖Complex.exp (z*p.eval q.val)‖*r) (norm_causalBoundedDiskEigenchain q)
  exact he.trans (hs.trans (hn.trans ((mul_one _).trans (Complex.norm_exp _))))

/-- The same genuine normalized datum retains its exact growth exponent along an entire positive ray. -/
theorem causalBoundedPolynomialEigenchain_ray_norm (p : ℂ[X]) (z : ℂ)
    (q : causalBoundedDiskRate) (t : ℝ≥0) :
    ‖causalBoundedPolynomialExponential p ((t : ℂ)*z) (causalBoundedDiskEigenchain q)‖ =
      Real.exp ((t : ℝ)*(z*p.eval q.val).re) := by
  have he := norm_causalBoundedPolynomialExponential_diskEigenchain p ((t : ℂ)*z) q
  have hr : (((t : ℂ)*z)*p.eval q.val).re = (t : ℝ)*(z*p.eval q.val).re := by
    rw [mul_assoc, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact he.trans (congrArg Real.exp hr)

/-- Every genuine rational mode gives a lower bound on the complete polynomial evolution norm. -/
theorem causalBoundedPolynomialExponential_norm_ge_mode (p : ℂ[X]) (z : ℂ)
    (q : causalBoundedDiskRate) :
    Real.exp ((z*p.eval q.val).re) ≤ ‖causalBoundedPolynomialExponential p z‖ := by
  have he := norm_causalBoundedPolynomialExponential_diskEigenchain p z q
  have hb := (causalBoundedPolynomialExponential p z).le_opNorm (causalBoundedDiskEigenchain q)
  have hn := congrArg (fun r : ℝ => ‖causalBoundedPolynomialExponential p z‖*r)
    (norm_causalBoundedDiskEigenchain q)
  exact he.symm.trans_le (hb.trans_eq (hn.trans (mul_one _)))

end
end RHTower.FokasLenells
