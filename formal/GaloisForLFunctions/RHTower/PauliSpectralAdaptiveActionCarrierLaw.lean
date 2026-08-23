import GaloisForLFunctions.RHTower.StaticChoiPhysicalActionTransportLaw
import GaloisForLFunctions.HTGeometry.PauliWeightedCommutatorCarrierLaw
import GaloisForLFunctions.HTGeometry.TwoLocalPauliGaussianEnergyCap
import GaloisForLFunctions.HTGeometry.ChainPauliFinFamily
import GaloisForLFunctions.RHTower.PauliOptimalDesignCommutatorCarrierLaw

/-!
# Quenched spectral action--carrier law for static two-local Hamiltonians

Growing-replica spectral near-action is split, for the same Hamiltonian draw,
into exact endpoint-adaptive transverse decay and literal optimal-design mass
inside Gaussian commutator tubes.  Exact physical-to-spectral transport makes
the carrier indicators identical; determinant-optimal weights are selected
before the draw.  No minimum spectral gap, worst-spectrum minimax, eigenbasis
reselection, or circuit-cardinality union remains.
-/

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
open Matrix Set MeasureTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

attribute [local instance] Classical.propDecidable

theorem finiteMatrixHilbertSchmidtEnergy_eq_frobSq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy A = frobSq A := by
  rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq]
  unfold frobSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (Complex.sq_norm (A i j)).symm

theorem finiteMatrixHilbertSchmidtEnergy_reindex_qubitConfigFin
    {n : ℕ}
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    finiteMatrixHilbertSchmidtEnergy
        (Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) A) =
      finiteMatrixHilbertSchmidtEnergy A := by
  rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq,
    finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hinner (i : Fin (2 ^ n)) :
      (∑ j : Fin (2 ^ n),
          Complex.normSq
            (A ((qubitConfigFin n).symm j) ((qubitConfigFin n).symm i))) =
        ∑ j : FiniteQubitConfiguration (Fin n),
          Complex.normSq (A j ((qubitConfigFin n).symm i)) := by
    exact Equiv.sum_comp (qubitConfigFin n).symm
      (fun j : FiniteQubitConfiguration (Fin n) =>
        Complex.normSq (A j ((qubitConfigFin n).symm i)))
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  exact Equiv.sum_comp (qubitConfigFin n).symm
    (fun i : FiniteQubitConfiguration (Fin n) =>
      ∑ j, Complex.normSq (A j i))

def reindexedTwoLocalPauliHamiltonian
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindex (qubitConfigFin n) (qubitConfigFin n)
    (realActivePauliHamiltonian x)

theorem reindexedTwoLocalPauliHamiltonian_isHermitian
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    (reindexedTwoLocalPauliHamiltonian x).IsHermitian := by
  exact (Matrix.isHermitian_iff_isSelfAdjoint.mpr
    (isSelfAdjoint_realActivePauliHamiltonian x)).reindex (qubitConfigFin n)

def reindexedTwoLocalPauliEndpoint
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  unitaryGroupReindex (qubitConfigFin n) U

def twoLocalPauliSpectralEndpoint
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  hermitianSpectralEndpoint
    (reindexedTwoLocalPauliHamiltonian_isHermitian x)
    (reindexedTwoLocalPauliEndpoint U)

def twoLocalPauliSpectralEnergy
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) : Fin (2 ^ n) → ℝ :=
  (reindexedTwoLocalPauliHamiltonian_isHermitian x).eigenvalues

def twoLocalPauliCommutatorActivation
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) : ℝ :=
  (gaussianIntervalActivationMass / 2) *
    ∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
      (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ 2

theorem finiteMatrixHilbertSchmidtEnergy_reindexedPauliCommutator
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    finiteMatrixHilbertSchmidtEnergy
        (reindexedTwoLocalPauliHamiltonian x *
            (reindexedTwoLocalPauliEndpoint U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) -
          (reindexedTwoLocalPauliEndpoint U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) *
            reindexedTwoLocalPauliHamiltonian x) =
      ‖twoLocalPauliUnitaryCommutatorMap U x‖ ^ 2 := by
  have hmatrix :
      reindexedTwoLocalPauliHamiltonian x *
            (reindexedTwoLocalPauliEndpoint U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) -
          (reindexedTwoLocalPauliEndpoint U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) *
            reindexedTwoLocalPauliHamiltonian x =
        Matrix.reindex (qubitConfigFin n) (qubitConfigFin n)
          (realActivePauliHamiltonian x *
              (U : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ) -
            (U : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ) *
              realActivePauliHamiltonian x) := by
    have hU :
        (reindexedTwoLocalPauliEndpoint U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) =
          Matrix.reindex (qubitConfigFin n) (qubitConfigFin n)
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) := rfl
    rw [reindexedTwoLocalPauliHamiltonian, hU]
    rw [reindex_qubitConfigFin_mul, reindex_qubitConfigFin_mul]
    rfl
  rw [hmatrix, finiteMatrixHilbertSchmidtEnergy_reindex_qubitConfigFin,
    finiteMatrixHilbertSchmidtEnergy_eq_frobSq,
    ← norm_twoLocalPauliUnitaryCommutatorMap_sq]

theorem mem_gaussianHalfActivationTube_twoLocalPauliCommutator_iff
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    x ∈ gaussianHalfActivationTube
        (n := Fintype.card (PauliTracelessLabel n 2))
        (twoLocalPauliUnitaryCommutatorMap U) ↔
      ‖twoLocalPauliUnitaryCommutatorMap U x‖ ^ 2 ≤
        twoLocalPauliCommutatorActivation U := by
  rfl

/-- **Same-draw Pauli action--carrier law.**  For every ordinary two-local
Hamiltonian draw and every unitary endpoint, replica near-action either pays
the exact endpoint-adaptive transverse factor or the draw lies in that
endpoint's Gaussian half-activation commutator tube. -/
theorem directStaticChoiTargetNearActionMass_twoLocalPauliSpectralEndpoint_le
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n)
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (choiVector
          (twoLocalPauliSpectralEndpoint x U :
            Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
        (twoLocalPauliSpectralEnergy x) r δ ≤
      staticChoiAdaptiveReplicaBase (twoLocalPauliSpectralEnergy x)
          (((2 : ℝ) ^ n)⁻¹ * twoLocalPauliCommutatorActivation U) ^ r +
        if x ∈ gaussianHalfActivationTube
            (n := Fintype.card (PauliTracelessLabel n 2))
            (twoLocalPauliUnitaryCommutatorMap U)
          then 1 else 0 := by
  classical
  have h :=
    directStaticChoiTargetNearActionMass_hermitianSpectralEndpoint_le_adaptivePhysicalAction
      (d := 2 ^ n) (by positivity)
      (reindexedTwoLocalPauliHamiltonian_isHermitian x)
      (reindexedTwoLocalPauliEndpoint U) r δ
      (twoLocalPauliCommutatorActivation U)
  change _ ≤ _ at h ⊢
  rw [finiteMatrixHilbertSchmidtEnergy_reindexedPauliCommutator] at h
  by_cases hc : ‖twoLocalPauliUnitaryCommutatorMap U x‖ ^ 2 ≤
      twoLocalPauliCommutatorActivation U
  · rw [if_pos hc] at h
    rw [if_pos]
    · simpa [twoLocalPauliSpectralEndpoint, twoLocalPauliSpectralEnergy,
        Nat.cast_pow] using h
    · exact (mem_gaussianHalfActivationTube_twoLocalPauliCommutator_iff x U).2 hc
  · rw [if_neg hc] at h
    rw [if_neg]
    · simpa [twoLocalPauliSpectralEndpoint, twoLocalPauliSpectralEnergy,
        Nat.cast_pow] using h
    · exact fun hx => hc
        ((mem_gaussianHalfActivationTube_twoLocalPauliCommutator_iff x U).1 hx)

/-- Probability-design version of the same-draw action--carrier law.  Target
count is absent pointwise, before taking any probability over Hamiltonians. -/
theorem weighted_twoLocalPauliSpectralNearActionMass_le_transverse_add_tubeMass
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (x : TwoLocalPauliCoefficientSpace n) (r : ℕ) (δ : ℝ) :
    (∑ c, w c * directStaticChoiTargetNearActionMass
        (choiVector
          (twoLocalPauliSpectralEndpoint x (U c) :
            Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
        (twoLocalPauliSpectralEnergy x) r δ) ≤
      (∑ c, w c *
        staticChoiAdaptiveReplicaBase (twoLocalPauliSpectralEnergy x)
          (((2 : ℝ) ^ n)⁻¹ * twoLocalPauliCommutatorActivation (U c)) ^ r) +
        GaloisForLFunctions.HTGeometry.twoLocalPauliWeightedCommutatorTubeMass U w x := by
  calc
    (∑ c, w c * directStaticChoiTargetNearActionMass
        (choiVector
          (twoLocalPauliSpectralEndpoint x (U c) :
            Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
        (twoLocalPauliSpectralEnergy x) r δ) ≤
      ∑ c, w c *
        (staticChoiAdaptiveReplicaBase (twoLocalPauliSpectralEnergy x)
            (((2 : ℝ) ^ n)⁻¹ * twoLocalPauliCommutatorActivation (U c)) ^ r +
          if x ∈ gaussianHalfActivationTube
              (n := Fintype.card (PauliTracelessLabel n 2))
              (twoLocalPauliUnitaryCommutatorMap (U c))
            then 1 else 0) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (directStaticChoiTargetNearActionMass_twoLocalPauliSpectralEndpoint_le
          x (U c) r δ) (hw.1 c)
    _ = (∑ c, w c *
        staticChoiAdaptiveReplicaBase (twoLocalPauliSpectralEnergy x)
          (((2 : ℝ) ^ n)⁻¹ * twoLocalPauliCommutatorActivation (U c)) ^ r) +
        GaloisForLFunctions.HTGeometry.twoLocalPauliWeightedCommutatorTubeMass U w x := by
      unfold GaloisForLFunctions.HTGeometry.twoLocalPauliWeightedCommutatorTubeMass
      unfold gaussianWeightedHalfActivationTubeMass
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1

/-- **Quenched growing-replica bound.**  For one ordinary two-local
Hamiltonian drawn once, failure of the exact endpoint-adaptive transverse
replica budget forces positive optimal-design mass into the Gaussian
commutator carrier.  The probability bound retains the design-averaged exact
stable ranks and has no circuit-cardinality factor. -/
theorem stdGaussian_measure_weightedTwoLocalPauliSpectralNearAction_gap_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x |
          (∑ c, w c *
            staticChoiAdaptiveReplicaBase (twoLocalPauliSpectralEnergy x)
              (((2 : ℝ) ^ n)⁻¹ * twoLocalPauliCommutatorActivation (U c)) ^ r) + κ ≤
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (choiVector
              (twoLocalPauliSpectralEndpoint x (U c) :
                Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
            (twoLocalPauliSpectralEnergy x) r δ} ≤
      (∑ c, w c * Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) *
          twoLocalPauliUnitaryCommutatorGramStableRatio (U c))) / κ := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_twoLocalPauli_measure_weightedCommutatorTubeMass_ge_le
      U w hw hκ)
  intro x hx
  have hdet :=
    weighted_twoLocalPauliSpectralNearActionMass_le_transverse_add_tubeMass
      U w hw x r δ
  change κ ≤ GaloisForLFunctions.HTGeometry.twoLocalPauliWeightedCommutatorTubeMass U w x
  change _ + κ ≤ _ at hx
  linarith

/-- **Pre-draw optimal-design quenched replica law.**  Determinant-optimal
physical Choi weights are fixed before the Hamiltonian draw.  For every
replica order, the probability that same-draw spectral near-action exceeds
its exact endpoint-adaptive transverse budget by `κ` is controlled by the
design average of exact commutator stable ranks, with neither eigenbasis
reselection nor circuit union. -/
theorem stdGaussian_measure_physicalOptimalDesignTwoLocalPauliSpectralNearAction_gap_le
    {n : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ)
    (U : C → Matrix.unitaryGroup (QubitRegister n) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x |
          (∑ c, physicalPauliChoiOptimalDesignWeight r U c *
            staticChoiAdaptiveReplicaBase (twoLocalPauliSpectralEnergy x)
              (((2 : ℝ) ^ n)⁻¹ * twoLocalPauliCommutatorActivation (U c)) ^ r) + κ ≤
          ∑ c, physicalPauliChoiOptimalDesignWeight r U c *
            directStaticChoiTargetNearActionMass
              (choiVector
                (twoLocalPauliSpectralEndpoint x (U c) :
                  Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
              (twoLocalPauliSpectralEnergy x) r δ} ≤
      (∑ c, physicalPauliChoiOptimalDesignWeight r U c *
        Real.exp
          (-(gaussianIntervalActivationMass ^ 2 / 2) *
            twoLocalPauliUnitaryCommutatorGramStableRatio (U c))) / κ := by
  exact stdGaussian_measure_weightedTwoLocalPauliSpectralNearAction_gap_le
    U (physicalPauliChoiOptimalDesignWeight r U)
      (physicalPauliChoiOptimalDesignWeight_mem_stdSimplex r U) r δ hκ

end
end RHTower
