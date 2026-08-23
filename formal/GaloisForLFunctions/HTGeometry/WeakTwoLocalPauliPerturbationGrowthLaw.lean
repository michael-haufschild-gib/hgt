import GaloisForLFunctions.HTGeometry.RobustStaticLocalLaboratoryComplexityGrowthLaw
import GaloisForLFunctions.HTGeometry.TwoLocalPauliGaussianEnergyCap
import GaloisForLFunctions.HTGeometry.NestedPathCutWitness
import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarReindex

/-!
# High-probability weak-noise two-local complexity growth

The inverse-square path seed and the complete ordinary two-local Pauli
Gaussian pencil are placed on the same `2L`-qubit register.  On the standard
Gaussian coefficient box, an arbitrarily weak fixed perturbation remains in
the robust laboratory-time growth tube.  The complement of that certified
growth set has the exact coordinate-union Gaussian tail.

Combined with scale-free observer anti-concentration, this separates the two
roles of fluctuation strength: it protects laboratory growth while leaving the
dimension-linear non-scalar carrier exponent unchanged.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal
open Matrix MeasureTheory ProbabilityTheory Metric

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Site relabelling from the paired growth register to `2L` ordinary qubits. -/
def pairQubitPathConfigurationEquiv (L : ℕ) :
    Config (PairQubit L) ≃ FiniteQubitConfiguration (Fin (L * 2)) :=
  Equiv.arrowCongr (pairQubitPathEquiv L) (Equiv.refl Bool)

/-- Complete traceless two-local Pauli Hamiltonian pulled back to the paired
growth register. -/
def pairQubitReindexedTwoLocalPauliHamiltonian (L : ℕ)
    (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  ∑ Q : PauliTracelessLabel (L * 2) 2,
    ((WithLp.ofLp x Q : ℝ) : ℂ) •
      Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L).symm
        (finitePauliMatrix Q.1)

/-- Pulling the physical perturbation back to numbered site coordinates
recovers the ordinary two-local Pauli pencil exactly. -/
theorem reindex_pairQubitReindexedTwoLocalPauliHamiltonian
    (L : ℕ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
        (pairQubitReindexedTwoLocalPauliHamiltonian L x) =
      realActivePauliHamiltonian x := by
  ext i j
  simp [pairQubitReindexedTwoLocalPauliHamiltonian,
    realActivePauliHamiltonian, activePauliHamiltonian,
    Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply]

theorem norm_pairQubit_reindexed_finitePauliMatrix
    {L : ℕ} (P : Fin (L * 2) → Option (Fin 3)) :
    ‖Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L).symm
        (finitePauliMatrix P)‖ = 1 := by
  let U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin (L * 2))) ℂ :=
    ⟨finitePauliMatrix P, finitePauliMatrix_mem_unitary P⟩
  simpa [U, unitaryGroupReindex, Matrix.coe_reindexAlgEquiv] using
    (CStarRing.norm_coe_unitary
      (unitaryGroupReindex (pairQubitPathConfigurationEquiv L).symm U))

theorem pairQubitReindexedTwoLocalPauliHamiltonian_isSelfAdjoint
    (L : ℕ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    IsSelfAdjoint (pairQubitReindexedTwoLocalPauliHamiltonian L x) := by
  rw [pairQubitReindexedTwoLocalPauliHamiltonian]
  exact isSelfAdjoint_sum Finset.univ fun Q _ => by
    have hP : IsSelfAdjoint
        (Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L).symm
          (finitePauliMatrix Q.1)) :=
      Matrix.isHermitian_iff_isSelfAdjoint.mp
        ((finitePauliMatrix_isHermitian Q.1).reindex
          (pairQubitPathConfigurationEquiv L).symm)
    rw [IsSelfAdjoint, star_smul, hP.star_eq]
    simp

theorem norm_pairQubitReindexedTwoLocalPauliHamiltonian_le_sum
    {L : ℕ} (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    ‖pairQubitReindexedTwoLocalPauliHamiltonian L x‖ ≤
      ∑ Q : PauliTracelessLabel (L * 2) 2, |WithLp.ofLp x Q| := by
  rw [pairQubitReindexedTwoLocalPauliHamiltonian]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro Q _
  rw [norm_smul, norm_pairQubit_reindexed_finitePauliMatrix, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- Polynomial operator-norm cap on the same high-probability coefficient
box used by the ordinary two-local ensemble. -/
theorem norm_pairQubitReindexedTwoLocalPauliHamiltonian_le_eighteen_mul_cube_of_mem_box
    {L : ℕ} (hL : 1 ≤ L) {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ twoLocalPauliCoefficientBox (L * 2)) :
    ‖pairQubitReindexedTwoLocalPauliHamiltonian L x‖ ≤
      18 * ((L * 2 : ℕ) : ℝ) ^ 3 := by
  have hn : 1 ≤ L * 2 := by omega
  have hcard : Fintype.card (PauliTracelessLabel (L * 2) 2) ≤
      18 * (L * 2) ^ 2 := by
    rw [card_pauliTracelessLabel]
    simpa using Quantum.nonidentityPauliWeightCount_le (L * 2) 2 hn
  calc
    ‖pairQubitReindexedTwoLocalPauliHamiltonian L x‖ ≤
        ∑ Q : PauliTracelessLabel (L * 2) 2, |WithLp.ofLp x Q| :=
      norm_pairQubitReindexedTwoLocalPauliHamiltonian_le_sum x
    _ ≤ ∑ _Q : PauliTracelessLabel (L * 2) 2, ((L * 2 : ℕ) : ℝ) :=
      Finset.sum_le_sum fun Q _ => hx Q
    _ = (Fintype.card (PauliTracelessLabel (L * 2) 2) : ℝ) *
        ((L * 2 : ℕ) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((18 * (L * 2) ^ 2 : ℕ) : ℝ) * ((L * 2 : ℕ) : ℝ) := by
      gcongr
    _ = 18 * ((L * 2 : ℕ) : ℝ) ^ 3 := by
      push_cast
      ring

/-- One fixed ordinary two-local Hamiltonian: deterministic growth seed plus
one scaled Gaussian draw, held fixed for all times. -/
def weakTwoLocalPauliPerturbedInverseSquareHamiltonian (L : ℕ) (scale : ℝ)
    (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  inverseSquareChainHamiltonian L +
    (scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x

/-- Exact same-draw transport: physical weak-noise Hamiltonian becomes the
affine ordinary Pauli pencil used by the spectral carrier theorem. -/
theorem reindex_weakTwoLocalPauliPerturbedInverseSquareHamiltonian
    (L : ℕ) (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
        (weakTwoLocalPauliPerturbedInverseSquareHamiltonian L scale x) =
      Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
          (inverseSquareChainHamiltonian L) +
        (scale : ℂ) • realActivePauliHamiltonian x := by
  ext i j
  simp [weakTwoLocalPauliPerturbedInverseSquareHamiltonian,
    pairQubitReindexedTwoLocalPauliHamiltonian,
    realActivePauliHamiltonian, activePauliHamiltonian,
    Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply]

theorem weakTwoLocalPauliPerturbedInverseSquareHamiltonian_isSelfAdjoint
    (L : ℕ) (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    IsSelfAdjoint (weakTwoLocalPauliPerturbedInverseSquareHamiltonian L scale x) := by
  rw [weakTwoLocalPauliPerturbedInverseSquareHamiltonian]
  apply IsSelfAdjoint.add (inverseSquareChainHamiltonian_isSelfAdjoint L)
  rw [IsSelfAdjoint, star_smul,
    (pairQubitReindexedTwoLocalPauliHamiltonian_isSelfAdjoint L x).star_eq]
  simp

/-- Certified high-probability growth carrier. -/
def weakTwoLocalPauliCertifiedGrowthSet (L : ℕ) :
    Set (TwoLocalPauliCoefficientSpace (L * 2)) :=
  twoLocalPauliCoefficientBox (L * 2)

/-- **Weak-noise high-probability laboratory growth law.**  Every draw in the
certified box obeys the complete robust linear two-gate floor throughout the
laboratory interval. -/
theorem weakTwoLocalPauliPerturbedInverseSquare_uniform_laboratory_growth
    {L : ℕ} (hL : 1 ≤ L) {T ε scale : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hbudget : T * (|scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) ≤ ε)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L) :
    ∀ t : ℝ,
      2048 * Real.pi * ε ≤ t →
      t ≤ ε * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L ε
          (unitaryEvolution
            (weakTwoLocalPauliPerturbedInverseSquareHamiltonian L scale x) t) := by
  apply perturbed_inverseSquareChain_uniform_laboratory_growth
    (weakTwoLocalPauliPerturbedInverseSquareHamiltonian_isSelfAdjoint L scale x)
    hε hεmax
  rw [weakTwoLocalPauliPerturbedInverseSquareHamiltonian, add_sub_cancel_left,
    norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc
    T * (|scale| * ‖pairQubitReindexedTwoLocalPauliHamiltonian L x‖) ≤
        T * (|scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) := by
      gcongr
      exact norm_pairQubitReindexedTwoLocalPauliHamiltonian_le_eighteen_mul_cube_of_mem_box
        hL hx
    _ ≤ ε := hbudget

/-- Exact high-probability failure bound for the certified growth carrier. -/
theorem stdGaussian_weakTwoLocalPauliCertifiedGrowthSet_compl_le (L : ℕ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace (L * 2))).real
        (weakTwoLocalPauliCertifiedGrowthSet L)ᶜ ≤
      (Fintype.card (PauliTracelessLabel (L * 2) 2) : ℝ) *
        (2 * Real.exp (-((L * 2 : ℕ) : ℝ) ^ 2 / 2)) := by
  exact stdGaussian_twoLocalPauli_measure_coefficientBox_compl_le (L * 2)

end

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
