import GaloisForLFunctions.HTGeometry.SiteFactorLocalReindexLaw
import GaloisForLFunctions.RHTower.NearestNeighborPolynomialCircuitPermanentHaarSeparationLaw

open Set
open scoped Matrix.Norms.L2Operator
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace RHTower

noncomputable section

/-- The numbered-register projective seed as a literal self-adjoint matrix. -/
def pairQubitProjectivePauliSeedSelfAdjoint (L : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    selfAdjoint (Matrix (FiniteQubitConfiguration (Fin (L * 2)))
      (FiniteQubitConfiguration (Fin (L * 2))) ℂ) :=
  ⟨pairQubitProjectivePauliSeed L p,
    Matrix.isHermitian_iff_isSelfAdjoint.mp
      (pairQubitProjectivePauliSeed_isHermitian L p)⟩

/-- Physical site numbering preserves literal Pauli weight at most two. -/
theorem pairQubitProjectivePauliSeed_hasPauliWeightAtMost_two
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    HasPauliWeightAtMost (Fin (L * 2)) 2
      (pairQubitProjectivePauliSeedSelfAdjoint L p) := by
  have h := hasPauliWeightAtMost_two_reindex_of_mem_siteFactorLocalSubmodule
    (pairQubitPathEquiv L) (nestedQubitPathGraph L)
    (nearestNeighborPathSelfAdjointHamiltonian L p)
    (nearestNeighborPathSelfAdjointHamiltonian_mem_localSubmodule L p)
  let K : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin (L * 2)))
      (FiniteQubitConfiguration (Fin (L * 2))) ℂ) :=
    ⟨Matrix.reindexAlgEquiv ℂ ℂ
        (qubitConfigurationEquiv (pairQubitPathEquiv L))
        (nearestNeighborPathSelfAdjointHamiltonian L p),
      isSelfAdjoint_reindexAlgEquiv
        (qubitConfigurationEquiv (pairQubitPathEquiv L))
        (nearestNeighborPathSelfAdjointHamiltonian L p).property⟩
  have hK : HasPauliWeightAtMost (Fin (L * 2)) 2 K := by
    simpa [K] using h
  have heq : pairQubitProjectivePauliSeedSelfAdjoint L p = K := by
    apply Subtype.ext
    rfl
  rw [heq]
  exact hK

/-- The controlled Gaussian ball gives a linear operator-norm cap after
physical site numbering. -/
theorem norm_pairQubitProjectivePauliSeed_le_length_add_two
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ Metric.closedBall (inverseSquarePathLocalCenter L)
      (1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1)))) :
    ‖(pairQubitProjectivePauliSeedSelfAdjoint L p :
        Matrix (FiniteQubitConfiguration (Fin (L * 2)))
          (FiniteQubitConfiguration (Fin (L * 2))) ℂ)‖ ≤ (L : ℝ) + 2 := by
  rw [show (pairQubitProjectivePauliSeedSelfAdjoint L p :
      Matrix (FiniteQubitConfiguration (Fin (L * 2)))
        (FiniteQubitConfiguration (Fin (L * 2))) ℂ) =
      Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
        (nearestNeighborPathLocalHamiltonian L p) by rfl]
  rw [l2_opNorm_reindexAlgEquiv_eq]
  exact norm_nearestNeighborPathLocalHamiltonian_le_length_add_two hL hp

/-- The controlled coefficient ball places the numbered physical seed within
`1 / L` in operator norm of the explicit inverse-square path. -/
theorem norm_pairQubitProjectivePauliSeed_sub_inverseSquare_le_inv_length
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ Metric.closedBall (inverseSquarePathLocalCenter L)
      (1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1)))) :
    ‖pairQubitProjectivePauliSeed L p - pairQubitInverseSquarePauliSeed L‖ ≤
      1 / (L : ℝ) := by
  rw [pairQubitProjectivePauliSeed, pairQubitInverseSquarePauliSeed,
    ← map_sub, l2_opNorm_reindexAlgEquiv_eq]
  have hdev := norm_nearestNeighborPathLocalHamiltonian_sub_center_le L p hp
  let M := nearestNeighborPathLocalGeneratorMass L
  have hM : 0 ≤ M := by
    dsimp [M, nearestNeighborPathLocalGeneratorMass]
    exact Finset.sum_nonneg fun i _ => norm_nonneg _
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hM1 : 0 < M + 1 := by linarith
  calc
    ‖nearestNeighborPathLocalHamiltonian L p - inverseSquareChainHamiltonian L‖ ≤
        (1 / ((L : ℝ) * (M + 1))) * M := by simpa [M] using hdev
    _ = (1 / (L : ℝ)) * (M / (M + 1)) := by field_simp
    _ ≤ (1 / (L : ℝ)) * 1 := by
      gcongr
      exact (div_le_one hM1).2 (by linarith)
    _ = 1 / (L : ℝ) := by ring

end

end RHTower
