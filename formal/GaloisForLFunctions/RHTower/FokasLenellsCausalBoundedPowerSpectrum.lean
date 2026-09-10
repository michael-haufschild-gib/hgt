import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPointSpectrum
import GaloisForLFunctions.HTGeometry.PrincipalSquareRootDeriv

/-! The actual derivative powers retain norm one; squaring fills the entire complex unit-disk spectrum. -/
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


private theorem minus_one_mem_spectrum : (-1 : ℂ) ∈ spectrum ℂ causalBoundedChainShift := by
  apply (causalBoundedChainShift_mem_spectrum_iff (-1)).mpr
  constructor <;> norm_num

/-- Every genuine derivative-shift power has exactly unit operator norm. -/
theorem norm_causalBoundedChainShift_pow (n : ℕ) : ‖causalBoundedChainShift^n‖ = 1 := by
  apply le_antisymm
  · exact (norm_pow_le causalBoundedChainShift n).trans
      (pow_le_one₀ (norm_nonneg _) norm_causalBoundedChainShift_le)
  · have hs := spectrum.pow_mem_pow causalBoundedChainShift n minus_one_mem_spectrum
    have hn : ‖(-1 : ℂ)^n‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
    exact hn.symm.trans_le (spectrum.norm_le_norm_of_mem hs)

private theorem exists_left_square_root (z : {z : ℂ // ‖z‖ ≤ 1}) :
    ∃ w : causalClosedLeftDisk, w.val^2 = z.val := by
  let w : ℂ := z.val ^ (1 / 2 : ℂ)
  have hw : w^2 = z.val := _root_.HTGeometry.cpow_half_sq
  have hn : ‖w‖^2 = ‖z.val‖ := (norm_pow w 2).symm.trans (congrArg (fun q : ℂ => ‖q‖) hw)
  have hb : ‖w‖ ≤ 1 := by nlinarith only [norm_nonneg w, z.property, hn]
  by_cases hr : w.re ≤ 0
  · exact ⟨⟨w, hr, hb⟩, hw⟩
  · have hnre : (-w).re ≤ 0 := by
      rw [Complex.neg_re]
      exact neg_nonpos.mpr (le_of_lt (lt_of_not_ge hr))
    have hnb : ‖-w‖ ≤ 1 := by simpa only [norm_neg] using hb
    exact ⟨⟨-w, hnre, hnb⟩, (neg_sq w).trans hw⟩

/-- The squared bounded shift is literally two successive genuine derivative coordinates. -/
theorem causalBoundedChainShift_square_coordinate (j : ℕ) (u : causalBoundedChain) :
    causalBoundedChainCoordinate j ((causalBoundedChainShift^2) u) =
      causalBoundedChainCoordinate (j+2) u :=
  (causalBoundedChainShift_coordinate j (causalBoundedChainShift u)).trans
    (causalBoundedChainShift_coordinate (j+1) u)

/-- Squaring the actual derivative shift fills the entire closed complex unit disk with spectrum. -/
theorem causalBoundedChainShift_square_spectrum :
    spectrum ℂ (causalBoundedChainShift^2) = {z : ℂ | ‖z‖ ≤ 1} := by
  apply Set.ext
  intro z
  change (z ∈ spectrum ℂ (causalBoundedChainShift^2)) ↔ ‖z‖ ≤ 1
  constructor
  · intro hz
    exact (spectrum.norm_le_norm_of_mem hz).trans_eq (norm_causalBoundedChainShift_pow 2)
  · intro hz
    let w : causalClosedLeftDisk := Classical.choose (exists_left_square_root ⟨z, hz⟩)
    have hw : w.val^2 = z := Classical.choose_spec (exists_left_square_root ⟨z, hz⟩)
    have hs := spectrum.pow_mem_pow causalBoundedChainShift 2 (causalClosedLeftDisk_mem_spectrum w)
    have he := congrArg (fun q : ℂ => q ∈ spectrum ℂ (causalBoundedChainShift^2)) hw
    exact he.mp hs

/-- Exact membership in the genuine second-derivative spectrum. -/
theorem causalBoundedChainShift_square_mem_spectrum_iff (z : ℂ) :
    z ∈ spectrum ℂ (causalBoundedChainShift^2) ↔ ‖z‖ ≤ 1 := by
  rw [causalBoundedChainShift_square_spectrum]
  rfl

/-- A scalar shift of the actual second derivative is invertible precisely outside the unit disk. -/
theorem causalBoundedChainShift_square_isUnit_iff (z : ℂ) :
    IsUnit (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) z - causalBoundedChainShift^2) ↔
      1 < ‖z‖ := by
  have h := not_congr (causalBoundedChainShift_square_mem_spectrum_iff z)
  simpa only [spectrum.mem_iff, not_not, not_le] using h

/-- Two genuine derivatives retain injectivity on the same actual bounded-chain carrier. -/
theorem causalBoundedChainShift_square_injective : Function.Injective (causalBoundedChainShift^2 : causalBoundedChain →L[ℂ] causalBoundedChain) := by
  change Function.Injective (fun u : causalBoundedChain => causalBoundedChainShift (causalBoundedChainShift u))
  exact causalBoundedChainShift_injective.comp causalBoundedChainShift_injective

/-- The actual second derivative remains non-surjective on the stronger bounded-chain space. -/
theorem causalBoundedChainShift_square_not_surjective :
    ¬ Function.Surjective (causalBoundedChainShift^2 : causalBoundedChain →L[ℂ] causalBoundedChain) := by
  intro hs
  have hu : IsUnit (causalBoundedChainShift^2) := ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨causalBoundedChainShift_square_injective, hs⟩
  have hz : (0 : ℂ) ∈ spectrum ℂ (causalBoundedChainShift^2) :=
    (causalBoundedChainShift_square_mem_spectrum_iff 0).mpr (by simp)
  apply spectrum.mem_iff.mp hz
  simpa only [map_zero, zero_sub] using hu.neg

end
end RHTower.FokasLenells
