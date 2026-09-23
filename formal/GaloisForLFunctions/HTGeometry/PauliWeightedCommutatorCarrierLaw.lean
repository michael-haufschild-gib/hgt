import GaloisForLFunctions.HTGeometry.GaussianWeightedObserverTubeLaw
import GaloisForLFunctions.HTGeometry.PauliCommutatorGramStableRankFloor

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev TwoLocalPauliGeneratorNumber (n : ℕ) :=
  Fintype.card (PauliTracelessLabel n 2)

/-- Optimal-design weighted mass of circuit endpoints whose commutator response
to one two-local Gaussian Hamiltonian draw falls in the half-activation tube. -/
def twoLocalPauliWeightedCommutatorTubeMass
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (w : C → ℝ) (x : TwoLocalPauliCoefficientSpace n) : ℝ :=
  gaussianWeightedHalfActivationTubeMass
    (n := TwoLocalPauliGeneratorNumber n)
    (fun c => twoLocalPauliUnitaryCommutatorMap (U c)) w x

/-- Exact weighted commutator-carrier tail. Circuit labels enter only through
their probability-design weights; no target cardinality or word-count factor appears. -/
theorem stdGaussian_twoLocalPauli_measure_weightedCommutatorTubeMass_ge_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x | κ ≤ twoLocalPauliWeightedCommutatorTubeMass U w x} ≤
      (∑ c, w c * Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryCommutatorGramStableRatio (U c))) / κ := by
  simpa [twoLocalPauliWeightedCommutatorTubeMass,
    TwoLocalPauliGeneratorNumber,
    twoLocalPauliUnitaryCommutatorGramStableRatio] using
    stdGaussian_measure_weightedHalfActivationTubeMass_ge_le
      (n := Fintype.card (PauliTracelessLabel n 2))
      (fun c => twoLocalPauliUnitaryCommutatorMap (U c))
      (by exact finrank_euclideanSpace) w hw hκ

/-- Return-excised weighted carrier law. If every occupied endpoint has normalized-trace
deficit at least `δ`, the complete probability design pays the single-target exponent
`(n-1)δ`, independently of circuit-dictionary size. -/
theorem stdGaussian_twoLocalPauli_measure_weightedCommutatorTubeMass_ge_le_traceDeficit
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (δ : ℝ)
    (hδ : ∀ c, δ ≤
      1 - ‖Matrix.trace
        (U c : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
        ((2 : ℝ) ^ n) ^ (2 : ℕ))
    {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x | κ ≤ twoLocalPauliWeightedCommutatorTubeMass U w x} ≤
      Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((n - 1 : ℕ) : ℝ) * δ)) / κ := by
  unfold twoLocalPauliWeightedCommutatorTubeMass
  apply stdGaussian_measure_weightedHalfActivationTubeMass_ge_le_stableFloor
    (fun c => twoLocalPauliUnitaryCommutatorMap (U c))
    (by exact finrank_euclideanSpace) w hw
    (((n - 1 : ℕ) : ℝ) * δ) _ hκ
  intro c
  rw [show
    ((∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
        (twoLocalPauliUnitaryCommutatorMap (U c)).singularValues i ^ (2 : ℕ)) ^ (2 : ℕ) /
      ∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
        (twoLocalPauliUnitaryCommutatorMap (U c)).singularValues i ^ (4 : ℕ)) =
      twoLocalPauliUnitaryCommutatorGramStableRatio (U c) by rfl]
  exact (mul_le_mul_of_nonneg_left (hδ c) (Nat.cast_nonneg _)).trans
    (twoLocalPauliUnitaryCommutatorGramStableRatio_ge_normalizedTraceDeficit (U c))

end

end GaloisForLFunctions.HTGeometry
