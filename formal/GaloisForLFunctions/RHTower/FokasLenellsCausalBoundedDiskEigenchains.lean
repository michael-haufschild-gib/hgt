import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedSpectrumUpper

/-! Genuine rational derivative eigenchains throughout the left unit disk. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fokasLenellsCausalBoundedDiskEigenchainsInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance fokasLenellsCausalBoundedDiskEigenchainsInst2 : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance fokasLenellsCausalBoundedDiskEigenchainsInst3 : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance fokasLenellsCausalBoundedDiskEigenchainsInst4 : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance fokasLenellsCausalBoundedDiskEigenchainsInst5 : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance fokasLenellsCausalBoundedDiskEigenchainsInst6 : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance fokasLenellsCausalBoundedDiskEigenchainsInst7 : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance fokasLenellsCausalBoundedDiskEigenchainsInst8 : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance fokasLenellsCausalBoundedDiskEigenchainsInst9 : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


/-- Spectral rates in the actual open left half-plane and closed unit disk. -/
abbrev causalBoundedDiskRate := {z : ℂ // z.re < 0 ∧ ‖z‖ ≤ 1}

/-- Normalize the already constructed genuine maximal-generator rational eigenvector. -/
def causalBoundedDiskEigenvector (z : causalBoundedDiskRate) : causalGeneratorDomain :=
  (‖causalLeftEigenvector ⟨z.val, z.property.1⟩‖ : ℂ)⁻¹ •
    causalLeftEigenvector ⟨z.val, z.property.1⟩

/-- Every actual disk-rate rational input has unit norm. -/
theorem norm_causalBoundedDiskEigenvector (z : causalBoundedDiskRate) :
    ‖causalBoundedDiskEigenvector z‖ = 1 := by
  have hn := norm_ne_zero_iff.mpr (causalLeftEigenvector_ne_zero ⟨z.val, z.property.1⟩)
  change ‖(‖causalLeftEigenvector ⟨z.val, z.property.1⟩‖ : ℂ)⁻¹ •
    causalLeftEigenvector ⟨z.val, z.property.1⟩‖ = 1
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ hn]

/-- These normalized rational data satisfy the actual maximal generator equation. -/
theorem causalGenerator_boundedDiskEigenvector (z : causalBoundedDiskRate) :
    causalGenerator (causalBoundedDiskEigenvector z) = z.val • (causalBoundedDiskEigenvector z).val := by
  change causalGenerator ((‖causalLeftEigenvector ⟨z.val, z.property.1⟩‖ : ℂ)⁻¹ •
    causalLeftEigenvector ⟨z.val, z.property.1⟩) = _
  rw [map_smul, causalGenerator_leftEigenvector]
  change (‖causalLeftEigenvector ⟨z.val, z.property.1⟩‖ : ℂ)⁻¹ •
    (z.val • (causalLeftEigenvector ⟨z.val, z.property.1⟩).val) =
    z.val • ((‖causalLeftEigenvector ⟨z.val, z.property.1⟩‖ : ℂ)⁻¹ •
      (causalLeftEigenvector ⟨z.val, z.property.1⟩).val)
  exact smul_comm _ _ _

private theorem disk_power_norm (z : causalBoundedDiskRate) (j : ℕ) :
    ‖z.val^j • (causalBoundedDiskEigenvector z).val‖ = ‖z.val‖^j := by
  rw [norm_smul, norm_pow]
  change ‖z.val‖^j * ‖causalBoundedDiskEigenvector z‖ = _
  rw [norm_causalBoundedDiskEigenvector, mul_one]

private theorem disk_power_bound (z : causalBoundedDiskRate) (j : ℕ) :
    ‖z.val^j • (causalBoundedDiskEigenvector z).val‖ ≤ 1 :=
  (disk_power_norm z j).trans_le (pow_le_one₀ (norm_nonneg _) z.property.2)

private theorem disk_graph_pair (z : causalBoundedDiskRate) (j : ℕ) :
    (z.val^j • (causalBoundedDiskEigenvector z).val,
      z.val^(j+1) • (causalBoundedDiskEigenvector z).val) ∈ causalGeneratorGraph := by
  apply (causalGeneratorGraph_mem_iff _ _).2
  have h := causalGenerator_hasRightDeriv (z.val^j • causalBoundedDiskEigenvector z)
  rw [map_smul, causalGenerator_boundedDiskEigenvector] at h
  change HasDerivWithinAt (causalForwardOrbit (z.val^j • (causalBoundedDiskEigenvector z).val))
    (z.val^j • (z.val • (causalBoundedDiskEigenvector z).val)) (Ioi 0) 0 at h
  rw [smul_smul, ← pow_succ] at h
  exact h

/-- The literal rational datum and all its genuine derivatives form a bounded chain. -/
def causalBoundedDiskEigenchain (z : causalBoundedDiskRate) : causalBoundedChain :=
  ⟨⟨fun j => z.val^j • (causalBoundedDiskEigenvector z).val,
    memℓp_infty ⟨1, by rintro y ⟨j, rfl⟩; exact disk_power_bound z j⟩⟩,
    (causalBoundedChain_mem_iff _).2 (disk_graph_pair z)⟩

/-- Every genuine derivative of the rational disk chain has the exact rate-power norm. -/
theorem causalBoundedDiskEigenchain_coordinate_norm (z : causalBoundedDiskRate) (j : ℕ) :
    ‖causalBoundedChainCoordinate j (causalBoundedDiskEigenchain z)‖ = ‖z.val‖^j := disk_power_norm z j

/-- The initial coordinate is the actual normalized rational maximal-domain datum. -/
theorem causalBoundedDiskEigenchain_zero (z : causalBoundedDiskRate) :
    causalBoundedChainCoordinate 0 (causalBoundedDiskEigenchain z) = (causalBoundedDiskEigenvector z).val := by
  change z.val^(0 : ℕ) • (causalBoundedDiskEigenvector z).val = _
  rw [pow_zero, one_smul]

/-- Genuine eigenchains throughout the left unit disk lie on the actual chain unit sphere. -/
theorem norm_causalBoundedDiskEigenchain (z : causalBoundedDiskRate) :
    ‖causalBoundedDiskEigenchain z‖ = 1 := by
  apply le_antisymm
  · exact lp.norm_le_of_forall_le zero_le_one (disk_power_bound z)
  · have he : ‖causalBoundedChainCoordinate 0 (causalBoundedDiskEigenchain z)‖ = 1 :=
      (causalBoundedDiskEigenchain_coordinate_norm z 0).trans (pow_zero _)
    exact he.symm.trans_le (causalBoundedChainCoordinate_norm_le 0 _)

/-- The bounded shift acts on every genuine rational disk chain by its exact scalar rate. -/
theorem causalBoundedChainShift_diskEigenchain (z : causalBoundedDiskRate) :
    causalBoundedChainShift (causalBoundedDiskEigenchain z) = z.val • causalBoundedDiskEigenchain z := by
  apply Subtype.ext
  apply lp.ext
  funext j
  change z.val^(j+1) • (causalBoundedDiskEigenvector z).val =
    z.val • (z.val^j • (causalBoundedDiskEigenvector z).val)
  rw [pow_succ', mul_smul]

/-- Every constructed genuine disk-rate eigenchain is nonzero. -/
theorem causalBoundedDiskEigenchain_ne_zero (z : causalBoundedDiskRate) :
    causalBoundedDiskEigenchain z ≠ 0 := by
  intro h
  have he := congrArg (fun u : causalBoundedChain => ‖u‖) h
  exact one_ne_zero ((norm_causalBoundedDiskEigenchain z).symm.trans (he.trans (norm_zero)))

/-- Every point of the open-left closed-unit disk belongs to the actual bounded-shift spectrum. -/
theorem causalBoundedDiskRate_mem_spectrum (z : causalBoundedDiskRate) :
    z.val ∈ spectrum ℂ causalBoundedChainShift := by
  rw [spectrum.mem_iff]
  intro hu
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  have he : (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) z.val -
      causalBoundedChainShift) (causalBoundedDiskEigenchain z) = 0 := by
    change z.val • causalBoundedDiskEigenchain z -
      causalBoundedChainShift (causalBoundedDiskEigenchain z) = 0
    exact sub_eq_zero.mpr (causalBoundedChainShift_diskEigenchain z).symm
  exact causalBoundedDiskEigenchain_ne_zero z (hinj (he.trans (map_zero _).symm))

/-- Each actual left-disk rate has a unit vector satisfying its bounded generator eigen-equation. -/
theorem causalBoundedDiskRate_has_unit_eigenvector (z : causalBoundedDiskRate) :
    ∃ u : causalBoundedChain, ‖u‖ = 1 ∧ causalBoundedChainShift u = z.val • u :=
  ⟨causalBoundedDiskEigenchain z, norm_causalBoundedDiskEigenchain z, causalBoundedChainShift_diskEigenchain z⟩

end
end RHTower.FokasLenells
