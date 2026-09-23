import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedSimilarity
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Contractivity and the actual exponential spectral map confine the genuine derivative-shift spectrum. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fokasLenellsCausalBoundedSpectrumUpperInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance fokasLenellsCausalBoundedSpectrumUpperInst2 : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance fokasLenellsCausalBoundedSpectrumUpperInst3 : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance fokasLenellsCausalBoundedSpectrumUpperInst4 : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance fokasLenellsCausalBoundedSpectrumUpperInst5 : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance fokasLenellsCausalBoundedSpectrumUpperInst6 : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance fokasLenellsCausalBoundedSpectrumUpperInst7 : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance fokasLenellsCausalBoundedSpectrumUpperInst8 : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance fokasLenellsCausalBoundedSpectrumUpperInst9 : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


/-- Every actual spectral value of the bounded genuine derivative shift lies in the closed unit disk. -/
theorem causalBoundedChainShift_spectrum_norm :
    spectrum ℂ causalBoundedChainShift ⊆ {z : ℂ | ‖z‖ ≤ 1} := by
  intro z hz
  exact (spectrum.norm_le_norm_of_mem hz).trans norm_causalBoundedChainShift_le

/-- The actual spectral exponential and positive-time contraction exclude every positive real part. -/
theorem causalBoundedChainShift_spectrum_re :
    spectrum ℂ causalBoundedChainShift ⊆ {z : ℂ | z.re ≤ 0} := by
  intro z hz
  have he : NormedSpace.exp causalBoundedChainShift = causalBoundedChainExponential (1 : ℂ) :=
    congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => NormedSpace.exp A)
      (one_smul ℂ causalBoundedChainShift).symm
  have hs : Complex.exp z ∈ spectrum ℂ (causalBoundedChainExponential (1 : ℂ)) := by
    simpa only [he, ← Complex.exp_eq_exp_ℂ] using spectrum.exp_mem_exp causalBoundedChainShift hz
  have hn : ‖Complex.exp z‖ ≤ 1 :=
    (spectrum.norm_le_norm_of_mem hs).trans_eq (norm_causalBoundedChainExponential_real (1 : ℝ≥0))
  have hr : Real.exp z.re ≤ Real.exp 0 := by
    simpa only [Complex.norm_exp, Real.exp_zero] using hn
  exact Real.exp_le_exp.mp hr

/-- The actual bounded generator spectrum is confined to the closed left half of the unit disk. -/
theorem causalBoundedChainShift_spectrum_subset :
    spectrum ℂ causalBoundedChainShift ⊆ {z : ℂ | z.re ≤ 0 ∧ ‖z‖ ≤ 1} := by
  intro z hz
  exact ⟨causalBoundedChainShift_spectrum_re hz, causalBoundedChainShift_spectrum_norm hz⟩

end
end RHTower.FokasLenells
