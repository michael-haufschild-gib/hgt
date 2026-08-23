import GaloisForLFunctions.HTGeometry.GaussianAffinePauliProjectiveGenericityLaw
import GaloisForLFunctions.HTGeometry.NearestNeighborGaussianSameDrawGrowthLaw
import GaloisForLFunctions.HTGeometry.WeakTwoLocalPauliPerturbationGrowthLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal
open Matrix MeasureTheory ProbabilityTheory Metric

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Maximally projective nearest-neighbour seeds occur arbitrarily close to
the inverse-square growth seed. -/
theorem exists_maximallyProjective_nearestNeighborSeed_close
    {L : ℕ} (hL : 0 < L) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ,
      p ∈ nearestNeighborPathLocalMaximalSet L ∧
      ‖nearestNeighborPathLocalHamiltonian L p - inverseSquareChainHamiltonian L‖ ≤
        ρ * nearestNeighborPathLocalGeneratorMass L := by
  have hdense :=
    (nearestNeighborPathLocalMaximalSet_dense_residual_fullMeasure hL).1
  obtain ⟨p, hp, hpdist⟩ :=
    hdense.exists_dist_lt (inverseSquarePathLocalCenter L) hρ
  have hpball : p ∈ closedBall (inverseSquarePathLocalCenter L) ρ := by
    rw [mem_closedBall]
    exact le_of_lt (by simpa [dist_comm] using hpdist)
  exact ⟨p, hp, norm_nearestNeighborPathLocalHamiltonian_sub_center_le L p hpball⟩

/-- A maximally projective local seed plus one complete two-local Pauli draw. -/
def projectiveSeedWeakTwoLocalHamiltonian (L : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  nearestNeighborPathLocalHamiltonian L p +
    (scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x

theorem projectiveSeedWeakTwoLocalHamiltonian_isSelfAdjoint
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    IsSelfAdjoint (projectiveSeedWeakTwoLocalHamiltonian L p scale x) := by
  rw [projectiveSeedWeakTwoLocalHamiltonian]
  apply IsSelfAdjoint.add
    (nearestNeighborPathLocalHamiltonian_isSelfAdjoint L p)
  rw [IsSelfAdjoint, star_smul,
    (pairQubitReindexedTwoLocalPauliHamiltonian_isSelfAdjoint L x).star_eq]
  simp

theorem reindex_projectiveSeedWeakTwoLocalHamiltonian
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
        (projectiveSeedWeakTwoLocalHamiltonian L p scale x) =
      Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
          (nearestNeighborPathLocalHamiltonian L p) +
        (scale : ℂ) • realActivePauliHamiltonian x := by
  ext i j
  simp [projectiveSeedWeakTwoLocalHamiltonian,
    pairQubitReindexedTwoLocalPauliHamiltonian,
    realActivePauliHamiltonian, activePauliHamiltonian,
    Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply]

/-- The maximally projective seed reserves part of the robust growth tube;
the complete Pauli perturbation uses the remaining part. -/
theorem projectiveSeedWeakTwoLocal_uniform_laboratory_growth
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {ρ T ε scale : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      ρ * nearestNeighborPathLocalGeneratorMass L)
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hbudget : T * (ρ * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) ≤ ε)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L) :
    ∀ t : ℝ,
      2048 * Real.pi * ε ≤ t →
      t ≤ ε * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L ε
          (unitaryEvolution
            (projectiveSeedWeakTwoLocalHamiltonian L p scale x) t) := by
  have hperturb :
      ‖projectiveSeedWeakTwoLocalHamiltonian L p scale x -
          inverseSquareChainHamiltonian L‖ ≤
        ρ * nearestNeighborPathLocalGeneratorMass L +
          |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3) := by
    have heq : projectiveSeedWeakTwoLocalHamiltonian L p scale x -
          inverseSquareChainHamiltonian L =
        (nearestNeighborPathLocalHamiltonian L p -
          inverseSquareChainHamiltonian L) +
          (scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x := by
      rw [projectiveSeedWeakTwoLocalHamiltonian]
      abel
    rw [heq]
    calc
      ‖(nearestNeighborPathLocalHamiltonian L p - inverseSquareChainHamiltonian L) +
          (scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x‖ ≤
          ‖nearestNeighborPathLocalHamiltonian L p - inverseSquareChainHamiltonian L‖ +
            ‖(scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x‖ :=
        norm_add_le _ _
      _ ≤ ρ * nearestNeighborPathLocalGeneratorMass L +
          |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3) := by
        apply add_le_add hseed
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        exact norm_pairQubitReindexedTwoLocalPauliHamiltonian_le_eighteen_mul_cube_of_mem_box
          hL hx
  apply perturbed_inverseSquareChain_uniform_laboratory_growth
    (projectiveSeedWeakTwoLocalHamiltonian_isSelfAdjoint L p scale x)
    hε hεmax
  exact (mul_le_mul_of_nonneg_left hperturb hT).trans hbudget

end

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
