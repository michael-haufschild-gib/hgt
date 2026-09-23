import GaloisForLFunctions.HTGeometry.PauliWeightedCommutatorCarrierLaw
import GaloisForLFunctions.RHTower.AutonomousReturnReflection
import GaloisForLFunctions.RHTower.StaticChoiOptimalDesignWeightedCrowdingFirstReturnLaw
import GaloisForLFunctions.RHTower.UnitaryReplicaOptimalDesignTransportLaw

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

abbrev QubitRegister (n : ℕ) := FiniteQubitConfiguration (Fin n)

/-- Physical unitary endpoint represented by its normalized Choi vector. -/
noncomputable def physicalPauliChoiTarget
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (QubitRegister n) ℂ) :
    C → (QubitRegister n × QubitRegister n) → ℂ :=
  fun c =>
    (GaloisForLFunctions.RHTower.choiVector
      (U c : Matrix (QubitRegister n) (QubitRegister n) ℂ)).ofLp

theorem physicalPauliChoiTarget_normalized
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (QubitRegister n) ℂ) :
    ∀ c, finiteComplexInner
      (physicalPauliChoiTarget U c) (physicalPauliChoiTarget U c) = 1 :=
  fun c => finiteComplexInner_ofLp_self_eq_one_of_norm_eq_one
    (GaloisForLFunctions.RHTower.choiVector
      (U c : Matrix (QubitRegister n) (QubitRegister n) ℂ))
    (GaloisForLFunctions.RHTower.norm_choiVector_eq_one Fintype.card_pos
      (Unitary.coe_star_mul_self (U c)))

/-- Determinant-optimal weights selected once from physical unitary Choi
endpoints, before any Hamiltonian draw. -/
noncomputable def physicalPauliChoiOptimalDesignWeight
    {n : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (QubitRegister n) ℂ) : C → ℝ :=
  replicaTargetOptimalDesignWeight r
    (physicalPauliChoiTarget U) (physicalPauliChoiTarget_normalized U)

theorem physicalPauliChoiOptimalDesignWeight_mem_stdSimplex
    {n : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (QubitRegister n) ℂ) :
    physicalPauliChoiOptimalDesignWeight r U ∈ stdSimplex ℝ C := by
  exact replicaTargetOptimalDesignWeight_mem_stdSimplex r
    (physicalPauliChoiTarget U) (physicalPauliChoiTarget_normalized U)

/-- Physical unitary Choi endpoints expressed after conjugation by an
arbitrary basis unitary. -/
def physicalPauliChoiBasisTarget
    {n : ℕ} {C : Type*} [Fintype C]
    (V : Matrix.unitaryGroup (QubitRegister n) ℂ)
    (U : C → Matrix.unitaryGroup (QubitRegister n) ℂ) :
    C → (QubitRegister n × QubitRegister n) → ℂ :=
  unitaryTransportTarget (pureConjugationUnitary V)
    (physicalPauliChoiTarget U)

/-- **Pre-draw circuit design survives every eigenbasis.** Physical
determinant-optimal Choi weights selected without a Hamiltonian remain an
exact occupied-rank optimal design after conjugation by every unitary basis.
No basis-dependent reselection occurs. -/
theorem physicalPauliChoiOptimalDesignWeight_pointwise_afterBasisConjugation
    {n : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (QubitRegister n) ℂ)
    (V : Matrix.unitaryGroup (QubitRegister n) ℂ)
    (ψ : (QubitRegister n × QubitRegister n) → ℂ) (c : C) :
    finitePureStateFidelity ψ (physicalPauliChoiBasisTarget V U c) ^ r ≤
      (Module.finrank ℂ
        (replicaTargetSpan r (physicalPauliChoiBasisTarget V U)) : ℝ) *
        ∑ j, physicalPauliChoiOptimalDesignWeight r U j *
          finitePureStateFidelity ψ
            (physicalPauliChoiBasisTarget V U j) ^ r := by
  have h :=
    replicaTargetOptimalDesignWeight_pointwise_unitaryTransport
      r (physicalPauliChoiTarget U) (physicalPauliChoiTarget_normalized U)
      (pureConjugationUnitary V) ψ c
  simp only [physicalPauliChoiBasisTarget]
  unfold physicalPauliChoiOptimalDesignWeight
  exact h

/-- Physical optimal-design weighted anomalous-commutator mass. -/
def physicalPauliOptimalDesignCommutatorTubeMass
    {n : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (QubitRegister n) ℂ)
    (x : TwoLocalPauliCoefficientSpace n) : ℝ :=
  twoLocalPauliWeightedCommutatorTubeMass U
    (physicalPauliChoiOptimalDesignWeight r U) x

/-- **Count-free physical-circuit carrier law.** For any finite nonempty
circuit image, determinant-optimal physical Choi weights eliminate its
cardinality completely. Every endpoint pays its own exact projective trace
deficit, and the anomalous weighted mass threshold is any positive `exp τ`. -/
theorem stdGaussian_twoLocalPauli_measure_physicalOptimalDesignCommutatorMass_ge_exp_le
    {n : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (QubitRegister n) ℂ)
    (τ : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x | Real.exp τ ≤
          physicalPauliOptimalDesignCommutatorTubeMass r U x} ≤
      Real.exp (-τ) *
        ∑ c, physicalPauliChoiOptimalDesignWeight r U c *
          Real.exp
            (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
              (((n - 1 : ℕ) : ℝ) *
                (1 - ‖Matrix.trace
                  (U c : Matrix (QubitRegister n) (QubitRegister n) ℂ)‖ ^ (2 : ℕ) /
                  ((2 : ℝ) ^ n) ^ (2 : ℕ)))) := by
  let w := physicalPauliChoiOptimalDesignWeight r U
  have hw : w ∈ stdSimplex ℝ C :=
    physicalPauliChoiOptimalDesignWeight_mem_stdSimplex r U
  have hbase :=
    stdGaussian_twoLocalPauli_measure_weightedCommutatorTubeMass_ge_le
      U w hw (Real.exp_pos τ)
  change (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
      {x | Real.exp τ ≤ twoLocalPauliWeightedCommutatorTubeMass U w x} ≤ _
  refine hbase.trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  rw [mul_comm _ (Real.exp (-τ))]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply Finset.sum_le_sum
  intro c hc
  apply mul_le_mul_of_nonneg_left _ (hw.1 c)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (twoLocalPauliUnitaryCommutatorGramStableRatio_ge_normalizedTraceDeficit
      (U c))
    (neg_nonpos.mpr (by positivity))

end

end RHTower
