import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedDiskApproximation

/-! Exact spectrum and bounded-inverse locus of the actual bounded derivative shift. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fokasLenellsCausalBoundedExactSpectrumInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance fokasLenellsCausalBoundedExactSpectrumInst2 : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance fokasLenellsCausalBoundedExactSpectrumInst3 : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance fokasLenellsCausalBoundedExactSpectrumInst4 : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance fokasLenellsCausalBoundedExactSpectrumInst5 : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance fokasLenellsCausalBoundedExactSpectrumInst6 : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance fokasLenellsCausalBoundedExactSpectrumInst7 : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance fokasLenellsCausalBoundedExactSpectrumInst8 : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance fokasLenellsCausalBoundedExactSpectrumInst9 : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


/-- Closedness and genuine rational approximants place the full left disk in the actual spectrum. -/
theorem causalClosedLeftDisk_mem_spectrum (z : causalClosedLeftDisk) :
    z.val ∈ spectrum ℂ causalBoundedChainShift := by
  have hc : IsClosed (spectrum ℂ causalBoundedChainShift) := spectrum.isClosed _
  exact hc.mem_of_tendsto (causalBoundedDiskApproxRate_tendsto z)
    (Filter.Eventually.of_forall (fun b => causalBoundedDiskRate_mem_spectrum (causalBoundedDiskApproxRate z b)))

/-- The complete actual bounded-generator spectrum is precisely the closed left unit disk. -/
theorem causalBoundedChainShift_spectrum :
    spectrum ℂ causalBoundedChainShift = {z : ℂ | z.re ≤ 0 ∧ ‖z‖ ≤ 1} := by
  apply Set.Subset.antisymm causalBoundedChainShift_spectrum_subset
  intro z hz
  exact causalClosedLeftDisk_mem_spectrum ⟨z, hz⟩

/-- An exact unconditional membership criterion for the genuine bounded-shift spectrum. -/
theorem causalBoundedChainShift_mem_spectrum_iff (z : ℂ) :
    z ∈ spectrum ℂ causalBoundedChainShift ↔ z.re ≤ 0 ∧ ‖z‖ ≤ 1 := by
  rw [causalBoundedChainShift_spectrum]
  rfl

/-- The actual bounded-inverse region is the union of the right half-plane and unit-disk exterior. -/
theorem causalBoundedChainShift_resolventSet :
    resolventSet ℂ causalBoundedChainShift = {z : ℂ | 0 < z.re ∨ 1 < ‖z‖} := by
  ext z
  have h := not_congr (causalBoundedChainShift_mem_spectrum_iff z)
  simpa only [spectrum, Set.mem_compl_iff, Set.mem_setOf_eq, not_not, not_and_or, not_le] using! h

/-- Exact invertibility classification of every scalar shift of the genuine derivative operator. -/
theorem causalBoundedChainShift_isUnit_iff (z : ℂ) :
    IsUnit (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) z - causalBoundedChainShift) ↔
      0 < z.re ∨ 1 < ‖z‖ := by
  change z ∈ resolventSet ℂ causalBoundedChainShift ↔ _
  rw [causalBoundedChainShift_resolventSet]
  rfl

end
end RHTower.FokasLenells
