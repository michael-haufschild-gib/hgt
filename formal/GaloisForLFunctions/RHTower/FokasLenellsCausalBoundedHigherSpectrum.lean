import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPowerSpectrum
import GaloisForLFunctions.RHTower.FokasLenellsCausalLeftHigherRoots

/-! Exact spectra and genuine derivative coordinates of every higher power of the bounded Cauchy generator. -/
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


/-- An actual left-disk spectral root of every order at least two. -/
def causalClosedDiskPowerRoot (n : ℕ) (z : {z : ℂ // ‖z‖ ≤ 1}) : causalClosedLeftDisk :=
  ⟨causalLeftPowerRoot n z, causalLeftPowerRoot_re_nonpos n z,
    norm_causalLeftPowerRoot_unitDisk n z⟩

/-- The selected actual spectral root has exactly the prescribed power. -/
theorem causalClosedDiskPowerRoot_pow (n : ℕ) (z : {z : ℂ // ‖z‖ ≤ 1}) :
    (causalClosedDiskPowerRoot n z).val^(n+2) = z.val := causalLeftPowerRoot_pow n z

/-- Every power literally advances the hierarchy of genuine derivatives by its order. -/
theorem causalBoundedChainShift_pow_coordinate (m j : ℕ) (u : causalBoundedChain) :
    causalBoundedChainCoordinate j ((causalBoundedChainShift^m) u) =
      causalBoundedChainCoordinate (j+m) u := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih =>
    have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain =>
      causalBoundedChainCoordinate j (A u)) (pow_succ' causalBoundedChainShift m)
    have hc := (causalBoundedChainShift_coordinate j ((causalBoundedChainShift^m) u)).trans (ih (j+1))
    simpa only [Nat.add_assoc, Nat.add_comm 1 m] using he.trans hc

/-- All actual derivative powers remain injective, including the identity at order zero. -/
theorem causalBoundedChainShift_pow_injective (m : ℕ) :
    Function.Injective (causalBoundedChainShift^m : causalBoundedChain →L[ℂ] causalBoundedChain) := by
  induction m with
  | zero => intro u v h; exact h
  | succ m ih =>
    intro u v h
    have hp := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u = A v)
      (pow_succ' causalBoundedChainShift m)
    exact ih (causalBoundedChainShift_injective (hp.mp h))

/-- Every positive genuine derivative order fails to map the bounded-chain space onto itself. -/
theorem causalBoundedChainShift_pow_not_surjective (m : ℕ) :
    ¬ Function.Surjective (causalBoundedChainShift^(m+1) : causalBoundedChain →L[ℂ] causalBoundedChain) := by
  intro hs
  apply causalBoundedChainShift_not_surjective
  intro v
  obtain ⟨u, hu⟩ := hs v
  refine ⟨(causalBoundedChainShift^m) u, ?_⟩
  have hp := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
    (pow_succ' causalBoundedChainShift m)
  exact hp.symm.trans hu

/-- From order two onward, the genuine derivative spectrum is the entire closed unit disk. -/
theorem causalBoundedChainShift_higher_spectrum (n : ℕ) :
    spectrum ℂ (causalBoundedChainShift^(n+2)) = {z : ℂ | ‖z‖ ≤ 1} := by
  apply Set.ext
  intro z
  change (z ∈ spectrum ℂ (causalBoundedChainShift^(n+2))) ↔ ‖z‖ ≤ 1
  constructor
  · intro hz
    exact (spectrum.norm_le_norm_of_mem hz).trans_eq (norm_causalBoundedChainShift_pow (n+2))
  · intro hz
    let w : causalClosedLeftDisk := causalClosedDiskPowerRoot n ⟨z, hz⟩
    have hw : w.val^(n+2) = z := causalClosedDiskPowerRoot_pow n ⟨z, hz⟩
    have hs := spectrum.pow_mem_pow causalBoundedChainShift (n+2) (causalClosedLeftDisk_mem_spectrum w)
    have he := congrArg (fun q : ℂ => q ∈ spectrum ℂ (causalBoundedChainShift^(n+2))) hw
    exact he.mp hs

/-- Exact spectral membership at every genuine derivative order at least two. -/
theorem causalBoundedChainShift_higher_mem_spectrum_iff (n : ℕ) (z : ℂ) :
    z ∈ spectrum ℂ (causalBoundedChainShift^(n+2)) ↔ ‖z‖ ≤ 1 := by
  rw [causalBoundedChainShift_higher_spectrum]
  rfl

/-- Every higher derivative has an invertible scalar shift precisely outside the unit disk. -/
theorem causalBoundedChainShift_higher_isUnit_iff (n : ℕ) (z : ℂ) :
    IsUnit (algebraMap ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) z - causalBoundedChainShift^(n+2)) ↔
      1 < ‖z‖ := by
  have h := not_congr (causalBoundedChainShift_higher_mem_spectrum_iff n z)
  simpa only [spectrum.mem_iff, not_not, not_le] using h

/-- The original rational eigenchains remain exact eigenvectors under every derivative power. -/
theorem causalBoundedChainShift_pow_diskEigenchain (m : ℕ) (z : causalBoundedDiskRate) :
    (causalBoundedChainShift^m) (causalBoundedDiskEigenchain z) =
      z.val^m • causalBoundedDiskEigenchain z := by
  induction m with
  | zero => simp only [pow_zero, one_smul]; rfl
  | succ m ih =>
    have hp := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain =>
      A (causalBoundedDiskEigenchain z)) (pow_succ' causalBoundedChainShift m)
    have hi := congrArg (fun v : causalBoundedChain => causalBoundedChainShift v) ih
    have hs := causalBoundedChainShift.map_smul (z.val^m) (causalBoundedDiskEigenchain z)
    have hu := congrArg (fun v : causalBoundedChain => z.val^m • v)
      (causalBoundedChainShift_diskEigenchain z)
    have hm := smul_smul (z.val^m) z.val (causalBoundedDiskEigenchain z)
    have hn := congrArg (fun c : ℂ => c • causalBoundedDiskEigenchain z) (pow_succ z.val m).symm
    exact hp.trans (hi.trans (hs.trans (hu.trans (hm.trans hn))))

end
end RHTower.FokasLenells
