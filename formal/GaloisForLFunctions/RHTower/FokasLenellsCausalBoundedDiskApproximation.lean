import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedDiskEigenchains

/-! Genuine left-half-plane rational rates approximate every point of the closed left unit disk. -/
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

local instance : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


/-- The actual closed left half of the complex unit disk. -/
abbrev causalClosedLeftDisk := {z : ℂ // z.re ≤ 0 ∧ ‖z‖ ≤ 1}

private theorem disk_approx_re (z : causalClosedLeftDisk) (b : ℝ) :
    ((z.val - (Real.exp b : ℂ)) / ((1 + Real.exp b : ℝ) : ℂ)).re < 0 := by
  rw [Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re]
  exact div_neg_of_neg_of_pos (sub_neg.mpr (z.property.1.trans_lt (Real.exp_pos b)))
    (by positivity)

private theorem disk_approx_norm (z : causalClosedLeftDisk) (b : ℝ) :
    ‖(z.val - (Real.exp b : ℂ)) / ((1 + Real.exp b : ℝ) : ℂ)‖ ≤ 1 := by
  have hp : 0 < 1 + Real.exp b := by positivity
  have he : ‖(Real.exp b : ℂ)‖ = Real.exp b := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos b)]
  have hn : ‖z.val - (Real.exp b : ℂ)‖ ≤ 1 + Real.exp b := by
    exact (norm_sub_le _ _).trans ((add_le_add z.property.2 he.le))
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  exact (div_le_one hp).mpr hn

/-- An explicit genuine left-disk rate approaching the given closed-disk point. -/
def causalBoundedDiskApproxRate (z : causalClosedLeftDisk) (b : ℝ) : causalBoundedDiskRate :=
  ⟨(z.val - (Real.exp b : ℂ)) / ((1 + Real.exp b : ℝ) : ℂ),
    disk_approx_re z b, disk_approx_norm z b⟩

/-- The approximation moves the real part strictly into the negative half-plane. -/
theorem causalBoundedDiskApproxRate_re (z : causalClosedLeftDisk) (b : ℝ) :
    (causalBoundedDiskApproxRate z b).val.re = (z.val.re - Real.exp b)/(1 + Real.exp b) := by
  change ((z.val - (Real.exp b : ℂ)) / ((1 + Real.exp b : ℝ) : ℂ)).re = _
  rw [Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re]

/-- The imaginary part retains its sign and converges back to the original coordinate. -/
theorem causalBoundedDiskApproxRate_im (z : causalClosedLeftDisk) (b : ℝ) :
    (causalBoundedDiskApproxRate z b).val.im = z.val.im/(1 + Real.exp b) := by
  change ((z.val - (Real.exp b : ℂ)) / ((1 + Real.exp b : ℝ) : ℂ)).im = _
  rw [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]

/-- Actual rational spectral rates converge to every closed left-disk point. -/
theorem causalBoundedDiskApproxRate_tendsto (z : causalClosedLeftDisk) :
    Tendsto (fun b : ℝ => (causalBoundedDiskApproxRate z b).val) atBot (𝓝 z.val) := by
  have he : Tendsto (fun b : ℝ => (Real.exp b : ℂ)) atBot (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero, Function.comp_def] using!
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp Real.tendsto_exp_atBot
  have hd : Tendsto (fun b : ℝ => ((1 + Real.exp b : ℝ) : ℂ)) atBot (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one, add_zero] using
      (tendsto_const_nhds (x := (1 : ℂ))).add he
  have ht := ((tendsto_const_nhds (x := z.val)).sub he).div hd one_ne_zero
  simpa only [causalBoundedDiskApproxRate, sub_zero, div_one] using! ht

end
end RHTower.FokasLenells
