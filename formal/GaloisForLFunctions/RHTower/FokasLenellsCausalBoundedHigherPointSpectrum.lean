import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedHigherSpectrum

/-! Explicit unit eigenchains and complete point spectra for all derivative orders at least three. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalHigherPointLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalHigherPointChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalHigherPointChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalHigherPointChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalHigherPointEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalHigherPointEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalHigherPointEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalHigherPointEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalHigherPointEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


/-- Nonzero points of the actual closed complex unit disk. -/
abbrev causalPuncturedUnitDisk := {z : ℂ // z ≠ 0 ∧ ‖z‖ ≤ 1}

/-- Every nonzero disk point has an actual strictly-left disk root of order `n+3`. -/
def causalBoundedHigherDiskRoot (n : ℕ) (z : causalPuncturedUnitDisk) : causalBoundedDiskRate :=
  ⟨causalLeftPowerRoot (n+1) z,
    causalLeftPowerRoot_re_neg n (Units.mk0 z.val z.property.1),
    norm_causalLeftPowerRoot_unitDisk (n+1) ⟨z.val, z.property.2⟩⟩

/-- A concrete genuine derivative eigenchain for every nonzero disk value and every order `n+3`. -/
def causalBoundedHigherEigenchain (n : ℕ) (z : causalPuncturedUnitDisk) : causalBoundedChain :=
  causalBoundedDiskEigenchain (causalBoundedHigherDiskRoot n z)

/-- The explicit higher-order eigenchain has genuine unit norm. -/
theorem norm_causalBoundedHigherEigenchain (n : ℕ) (z : causalPuncturedUnitDisk) :
    ‖causalBoundedHigherEigenchain n z‖ = 1 :=
  norm_causalBoundedDiskEigenchain (causalBoundedHigherDiskRoot n z)

/-- The actual derivative power has the prescribed eigenvalue on the constructed unit chain. -/
theorem causalBoundedChainShift_higher_eigenchain (n : ℕ) (z : causalPuncturedUnitDisk) :
    (causalBoundedChainShift^(n+3)) (causalBoundedHigherEigenchain n z) =
      z.val • causalBoundedHigherEigenchain n z := by
  have hr : (causalBoundedHigherDiskRoot n z).val^(n+3) = z.val := by
    change (causalLeftPowerRoot (n+1) z.val)^(n+3) = z.val
    simpa only [show n+1+2 = n+3 by omega] using causalLeftPowerRoot_pow (n+1) z.val
  exact (causalBoundedChainShift_pow_diskEigenchain (n+3) (causalBoundedHigherDiskRoot n z)).trans
    (congrArg (fun r : ℂ => r • causalBoundedHigherEigenchain n z) hr)

/-- Point spectrum defined by nonzero eigenvectors of the actual derivative power. -/
def causalBoundedChainPowerPointSpectrum (m : ℕ) : Set ℂ :=
  {z | ∃ u : causalBoundedChain, u ≠ 0 ∧ (causalBoundedChainShift^m) u = z • u}

/-- From order three onward, the point spectrum is precisely the punctured closed unit disk. -/
theorem causalBoundedChainShift_higher_mem_pointSpectrum_iff (n : ℕ) (z : ℂ) :
    z ∈ causalBoundedChainPowerPointSpectrum (n+3) ↔ z ≠ 0 ∧ ‖z‖ ≤ 1 := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hz : z ≠ 0 := by
      intro hz
      have hzero : (causalBoundedChainShift^(n+3)) u = 0 := by
        simpa only [hz, zero_smul] using he
      exact hu (causalBoundedChainShift_pow_injective (n+3) (hzero.trans (map_zero _).symm))
    have hn : ‖z‖*‖u‖ ≤ ‖u‖ := by
      have hb := (causalBoundedChainShift^(n+3)).le_opNorm u
      have hunit := congrArg (fun r : ℝ => r*‖u‖) (norm_causalBoundedChainShift_pow (n+3))
      exact (norm_smul z u).symm.trans_le
        ((congrArg (fun v : causalBoundedChain => ‖v‖) he).symm.trans_le
          (hb.trans_eq (hunit.trans (one_mul _))))
    exact ⟨hz, (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hu)).mp
      (hn.trans_eq (one_mul ‖u‖).symm)⟩
  · intro hz
    let u := causalBoundedHigherEigenchain n ⟨z, hz⟩
    have hu : u ≠ 0 := causalBoundedDiskEigenchain_ne_zero _
    exact ⟨u, hu, causalBoundedChainShift_higher_eigenchain n ⟨z, hz⟩⟩

/-- Exact set classification of all genuine higher-order eigenvalues. -/
theorem causalBoundedChainPowerPointSpectrum_higher (n : ℕ) :
    causalBoundedChainPowerPointSpectrum (n+3) = {z : ℂ | z ≠ 0 ∧ ‖z‖ ≤ 1} :=
  Set.ext (causalBoundedChainShift_higher_mem_pointSpectrum_iff n)

/-- Every nonzero point of the closed disk is realized by an actual unit eigenvector. -/
theorem causalBoundedHigher_has_unit_eigenvector (n : ℕ) (z : causalPuncturedUnitDisk) :
    ∃ u : causalBoundedChain, ‖u‖ = 1 ∧ (causalBoundedChainShift^(n+3)) u = z.val • u :=
  ⟨causalBoundedHigherEigenchain n z, norm_causalBoundedHigherEigenchain n z,
    causalBoundedChainShift_higher_eigenchain n z⟩

/-- Zero is the only spectral value without a genuine eigenvector at orders at least three. -/
theorem causalBoundedChainShift_higher_spectrum_diff_pointSpectrum (n : ℕ) :
    spectrum ℂ (causalBoundedChainShift^(n+3)) \ causalBoundedChainPowerPointSpectrum (n+3) = {0} := by
  have hs : spectrum ℂ (causalBoundedChainShift^(n+3)) = {z : ℂ | ‖z‖ ≤ 1} := by
    simpa only [Nat.add_assoc] using causalBoundedChainShift_higher_spectrum (n+1)
  rw [hs, causalBoundedChainPowerPointSpectrum_higher]
  ext z
  simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hb, hn⟩
    by_contra hz
    exact hn ⟨hz, hb⟩
  · intro hz
    subst z
    simp

end
end RHTower.FokasLenells
