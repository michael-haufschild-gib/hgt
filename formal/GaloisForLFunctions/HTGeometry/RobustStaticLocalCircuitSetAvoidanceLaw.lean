import GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianOneDrawGrowthLaw

/-!
# Robust avoidance of the entire bounded-complexity circuit set

The robust laboratory-time complexity floor is converted here into a return-free statement for
the complete operator-norm circuit set, not merely for a neighbourhood of the initial state.  For
every two-gate cutoff `s`, once `t ≥ 256 π ε (s+1)` and the laboratory hypotheses hold, no circuit
with at most `s` counted two-qubit gates approximates the autonomous endpoint.  One fixed nearby
Hamiltonian avoids the complete cutoff set throughout the resulting time window.

The termwise two-local Gaussian ensemble inherits an explicit positive-probability avoidance
event.  This is a laboratory-scale first-return lower bound.  It does not establish the expected
exponential Brown first-return scale.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal
open Matrix MeasureTheory ProbabilityTheory Metric

open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

theorem operatorTwoGateComplexityTo_le_of_circuit {L : ℕ} {ε : ℝ}
    {W : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    {c : List (LocalGate (PairQubit L))}
    (hc : OperatorApproximatesTarget W ε c) :
    operatorTwoGateComplexityTo L ε W ≤ (twoGateCount c : ℕ∞) := by
  refine le_trans (iInf_le _ c) ?_
  exact iInf_le
    (fun _ : c ∈ {c : List (LocalGate (PairQubit L)) |
      OperatorApproximatesTarget W ε c} => (twoGateCount c : ℕ∞)) hc

/-- Membership in the entire operator-norm circuit set of two-gate cost at most `s`. -/
def InTwoGateCircuitSetAtMost {L : ℕ}
    (ε : ℝ) (W : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ)
    (s : ℕ) : Prop :=
  ∃ c : List (LocalGate (PairQubit L)),
    OperatorApproximatesTarget W ε c ∧ twoGateCount c ≤ s

/-- Pointwise avoidance of the complete cutoff circuit set. -/
theorem perturbed_inverseSquareChain_not_in_circuitSet
    {L s : ℕ} {t ε : ℝ}
    {H : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    (hH : IsSelfAdjoint H)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (htMin : 2048 * Real.pi * ε ≤ t)
    (htCircuit : 256 * Real.pi * ε * (s + 1) ≤ t)
    (htLab : t ≤ ε * L)
    (hclose : |t| * ‖H - inverseSquareChainHamiltonian L‖ ≤ ε) :
    ¬ InTwoGateCircuitSetAtMost ε (unitaryEvolution H t) s := by
  have hlow := perturbed_inverseSquareChain_floor_growth
    hH hε hεmax htMin htLab hclose
  have hden : 0 < 256 * Real.pi * ε := by positivity
  have hratio : ((s + 1 : ℕ) : ℝ) ≤ t / (256 * Real.pi * ε) := by
    rw [le_div_iff₀ hden]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htCircuit
  have hfloor : s + 1 ≤ ⌊t / (256 * Real.pi * ε)⌋₊ := Nat.le_floor hratio
  intro hmem
  rcases hmem with ⟨c, hc, hcost⟩
  have hupper := operatorTwoGateComplexityTo_le_of_circuit hc
  have hchain : (((s + 1 : ℕ) : ℕ∞)) ≤ (s : ℕ∞) := by
    exact (by exact_mod_cast hfloor : ((s + 1 : ℕ) : ℕ∞) ≤
      ((⌊t / (256 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞)).trans
        (hlow.trans (hupper.trans (by exact_mod_cast hcost)))
  have hnat : s + 1 ≤ s := by exact_mod_cast hchain
  omega

/-- One fixed Hamiltonian avoids the complete cutoff circuit set throughout the laboratory
window. -/
theorem perturbed_inverseSquareChain_uniform_circuitSet_avoidance
    {L s : ℕ} {T ε : ℝ}
    {H : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    (hH : IsSelfAdjoint H)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (htube : T * ‖H - inverseSquareChainHamiltonian L‖ ≤ ε) :
    ∀ t : ℝ,
      2048 * Real.pi * ε ≤ t →
      256 * Real.pi * ε * (s + 1) ≤ t →
      t ≤ ε * L →
      t ≤ T →
      ¬ InTwoGateCircuitSetAtMost ε (unitaryEvolution H t) s := by
  intro t htMin htCircuit htLab htT
  have hmin0 : 0 < 2048 * Real.pi * ε := by positivity
  have ht0 : 0 ≤ t := by linarith
  have hclose : |t| * ‖H - inverseSquareChainHamiltonian L‖ ≤ ε := by
    rw [abs_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_right htT (norm_nonneg _)).trans htube
  exact perturbed_inverseSquareChain_not_in_circuitSet
    hH hε hεmax htMin htCircuit htLab hclose

/-- Equivalent first-return formulation: the cutoff circuit set has no hit in the certified
window. -/
theorem perturbed_inverseSquareChain_no_circuitSet_return_window
    {L s : ℕ} {T ε : ℝ}
    {H : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    (hH : IsSelfAdjoint H)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (htube : T * ‖H - inverseSquareChainHamiltonian L‖ ≤ ε) :
    ¬ ∃ t : ℝ,
      2048 * Real.pi * ε ≤ t ∧
      256 * Real.pi * ε * (s + 1) ≤ t ∧
      t ≤ ε * L ∧ t ≤ T ∧
      InTwoGateCircuitSetAtMost ε (unitaryEvolution H t) s := by
  rintro ⟨t, htMin, htCircuit, htLab, htT, hmem⟩
  exact perturbed_inverseSquareChain_uniform_circuitSet_avoidance
    hH hε hεmax htube t htMin htCircuit htLab htT hmem

def ordinaryTwoLocalGaussianCircuitSetAvoidanceEvent
    (L s : ℕ) (T ε : ℝ) : Set (OrdinaryTwoLocalGaussianCoordinate L → ℝ) :=
  {J | ∀ t : ℝ,
    2048 * Real.pi * ε ≤ t →
    256 * Real.pi * ε * (s + 1) ≤ t →
    t ≤ ε * L →
    t ≤ T →
    ¬ InTwoGateCircuitSetAtMost ε
      (unitaryEvolution (ordinaryTwoLocalGaussianHamiltonian L J) t) s}

/-- Explicit Gaussian lower bound for complete circuit-set avoidance. -/
theorem measure_ordinaryTwoLocalGaussianCircuitSetAvoidanceEvent_lower
    (L s : ℕ) {T ε ρ : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hscale : T * (ρ * ordinaryTwoLocalGeneratorMass L) ≤ ε) :
    ENNReal.ofReal ((2 * gaussianFloorTwo * ρ) ^
        Fintype.card (OrdinaryTwoLocalRawCoordinate L)) ≤
      (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
        (ordinaryTwoLocalGaussianCircuitSetAvoidanceEvent L s T ε) := by
  have hball := measure_pi_gaussian_shifted_ball_lower
    (Fintype.card (OrdinaryTwoLocalRawCoordinate L))
    (ordinaryTwoLocalCenter_norm_le_one L) hρ0 hρ1
  refine hball.trans (measure_mono ?_)
  intro J hJ t htMin htCircuit htLab htT
  have hnorm := norm_ordinaryTwoLocalGaussianHamiltonian_sub_center_le L J hJ
  have htube : T * ‖ordinaryTwoLocalGaussianHamiltonian L J -
      inverseSquareChainHamiltonian L‖ ≤ ε := by
    exact (mul_le_mul_of_nonneg_left hnorm hT).trans hscale
  exact perturbed_inverseSquareChain_uniform_circuitSet_avoidance
    (ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint L J)
    hε hεmax htube t htMin htCircuit htLab htT

/-- Complete circuit-set avoidance has strictly positive probability. -/
theorem measure_ordinaryTwoLocalGaussianCircuitSetAvoidanceEvent_pos
    (L s : ℕ) {T ε ρ : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hscale : T * (ρ * ordinaryTwoLocalGeneratorMass L) ≤ ε) :
    0 < (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
      (ordinaryTwoLocalGaussianCircuitSetAvoidanceEvent L s T ε) := by
  have hlower := measure_ordinaryTwoLocalGaussianCircuitSetAvoidanceEvent_lower
    L s hT hε hεmax hρ.le hρ1 hscale
  exact (ENNReal.ofReal_pos.mpr (by positivity [gaussianFloorTwo_pos])).trans_le hlower

end

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
