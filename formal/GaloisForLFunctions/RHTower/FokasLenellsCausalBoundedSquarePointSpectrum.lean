import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedHigherPointSpectrum

/-! The second derivative's exceptional negative-real radius, contrasted with higher-order point spectra. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalSquarePointLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalSquarePointChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalSquarePointChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalSquarePointChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalSquarePointEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalSquarePointEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalSquarePointEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalSquarePointEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalSquarePointEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


private theorem left_square_root_strict (z : ℂ) (hz : 0 < z.re ∨ z.im ≠ 0) :
    (causalLeftPowerRoot 0 z).re < 0 := by
  let r := causalLeftPowerRoot 0 z
  have hr : r.re ≤ 0 := causalLeftPowerRoot_re_nonpos 0 z
  have hp : r^(2 : ℕ) = z := causalLeftPowerRoot_pow 0 z
  by_contra hn
  have he : r.re = 0 := le_antisymm hr (le_of_not_gt hn)
  have hre := congrArg Complex.re hp
  have him := congrArg Complex.im hp
  simp only [pow_two, Complex.mul_re, Complex.mul_im, he, zero_mul, mul_zero,
    zero_add, zero_sub] at hre him
  rcases hz with hz | hz
  · nlinarith only [hre, hz, sq_nonneg r.im]
  · exact hz him.symm

private theorem strict_left_square_avoids_radius (r : causalBoundedDiskRate) :
    0 < (r.val^(2 : ℕ)).re ∨ (r.val^(2 : ℕ)).im ≠ 0 := by
  by_cases him : (r.val^(2 : ℕ)).im = 0
  · left
    have hmul : r.val.re * r.val.im = 0 := by
      have h := him
      simp only [pow_two, Complex.mul_im] at h
      nlinarith only [h]
    have hi : r.val.im = 0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_lt r.property.1)
    simp only [pow_two, Complex.mul_re, hi, mul_zero, sub_zero]
    exact mul_pos_of_neg_of_neg r.property.1 r.property.1
  · exact Or.inr him

/-- The unit disk with its nonpositive real radius removed. -/
abbrev causalSquarePointDisk := {z : ℂ // ‖z‖ ≤ 1 ∧ (0 < z.re ∨ z.im ≠ 0)}

/-- A genuine strictly-left disk root for every admissible second-derivative eigenvalue. -/
def causalBoundedSquareDiskRoot (z : causalSquarePointDisk) : causalBoundedDiskRate :=
  ⟨causalLeftPowerRoot 0 z, left_square_root_strict z z.property.2,
    norm_causalLeftPowerRoot_unitDisk 0 ⟨z.val, z.property.1⟩⟩

/-- An actual rational derivative chain for each second-derivative eigenvalue. -/
def causalBoundedSquareDiskEigenchain (z : causalSquarePointDisk) : causalBoundedChain :=
  causalBoundedDiskEigenchain (causalBoundedSquareDiskRoot z)

/-- These concrete second-derivative eigenchains have genuine unit norm. -/
theorem norm_causalBoundedSquareDiskEigenchain (z : causalSquarePointDisk) :
    ‖causalBoundedSquareDiskEigenchain z‖ = 1 :=
  norm_causalBoundedDiskEigenchain (causalBoundedSquareDiskRoot z)

/-- The actual squared generator has exactly the prescribed eigenvalue on its constructed chain. -/
theorem causalBoundedChainShift_square_diskEigenchain (z : causalSquarePointDisk) :
    (causalBoundedChainShift^(2 : ℕ)) (causalBoundedSquareDiskEigenchain z) =
      z.val • causalBoundedSquareDiskEigenchain z :=
  (causalBoundedChainShift_pow_diskEigenchain 2 (causalBoundedSquareDiskRoot z)).trans
    (congrArg (fun r : ℂ => r • causalBoundedSquareDiskEigenchain z) (causalLeftPowerRoot_pow 0 z))

private theorem square_eigen_root (z : ℂ) (u : causalBoundedChain) (hu : u ≠ 0)
    (he : (causalBoundedChainShift^(2 : ℕ)) u = z • u) :
    ∃ r : causalBoundedDiskRate, r.val^(2 : ℕ) = z := by
  let r := causalLeftPowerRoot 0 z
  have hr : r.re ≤ 0 := causalLeftPowerRoot_re_nonpos 0 z
  have hp : r^(2 : ℕ) = z := causalLeftPowerRoot_pow 0 z
  let v := causalBoundedChainShift u + r • u
  have hv : v ≠ 0 := by
    intro hv
    have he' : causalBoundedChainShift u = (-r) • u := by
      have h : causalBoundedChainShift u = -(r • u) := eq_neg_of_add_eq_zero_left hv
      exact h.trans (neg_smul r u).symm
    have hn := ((causalBoundedChainShift_mem_pointSpectrum_iff (-r)).mp ⟨u, hu, he'⟩).1
    change -r.re < 0 at hn
    linarith only [hn, hr]
  have hvEq : causalBoundedChainShift v = r • v := by
    have hmap : causalBoundedChainShift v =
        z • u + r • causalBoundedChainShift u :=
      (causalBoundedChainShift.map_add (causalBoundedChainShift u) (r • u)).trans
        (congrArg₂ (fun a b : causalBoundedChain => a+b) he (causalBoundedChainShift.map_smul r u))
    have hscalar : r • (r • u) = z • u :=
      (smul_smul r r u).trans (congrArg (fun c : ℂ => c • u) ((pow_two r).symm.trans hp))
    have hright : r • v = r • causalBoundedChainShift u + z • u :=
      (smul_add r (causalBoundedChainShift u) (r • u)).trans
        (congrArg (fun a : causalBoundedChain => r • causalBoundedChainShift u + a) hscalar)
    exact hmap.trans ((add_comm _ _).trans hright.symm)
  exact ⟨⟨r, (causalBoundedChainShift_mem_pointSpectrum_iff r).mp ⟨v, hv, hvEq⟩⟩, hp⟩

/-- The second derivative has exactly the unit-disk eigenvalues off the nonpositive real radius. -/
theorem causalBoundedChainShift_square_mem_pointSpectrum_iff (z : ℂ) :
    z ∈ causalBoundedChainPowerPointSpectrum 2 ↔ ‖z‖ ≤ 1 ∧ (0 < z.re ∨ z.im ≠ 0) := by
  constructor
  · rintro ⟨u, hu, he⟩
    let r := Classical.choose (square_eigen_root z u hu he)
    have hp : r.val^(2 : ℕ) = z := Classical.choose_spec (square_eigen_root z u hu he)
    have hn : ‖z‖ ≤ 1 :=
      ((congrArg (fun w : ℂ => ‖w‖) hp).symm.trans (norm_pow _ _)).trans_le
        (pow_le_one₀ (norm_nonneg _) r.property.2)
    exact ⟨hn, (congrArg (fun w : ℂ => 0 < w.re ∨ w.im ≠ 0) hp).mp
      (strict_left_square_avoids_radius r)⟩
  · intro hz
    exact ⟨causalBoundedSquareDiskEigenchain ⟨z, hz⟩, causalBoundedDiskEigenchain_ne_zero _,
      causalBoundedChainShift_square_diskEigenchain ⟨z, hz⟩⟩

/-- Exact set form of the second derivative's exceptional point-spectrum radius. -/
theorem causalBoundedChainPowerPointSpectrum_square :
    causalBoundedChainPowerPointSpectrum 2 = {z : ℂ | ‖z‖ ≤ 1 ∧ (0 < z.re ∨ z.im ≠ 0)} :=
  Set.ext causalBoundedChainShift_square_mem_pointSpectrum_iff

end
end RHTower.FokasLenells
