import GaloisForLFunctions.HTGeometry.NoncommutativeQubitResponsePolarization
import GaloisForLFunctions.HTGeometry.DecoupledEvolutionFactorization
import GaloisForLFunctions.HTGeometry.KroneckerSumSpectrum

/-!
# Neutral ancillary recovery for the noncommutative qubit formation

Tensoring the qubit family with an arbitrary fixed faithful finite density matrix preserves
normalization, faithfulness, reflection, quantum relative entropy, and quantum Jeffreys work.
-/

open Matrix
open Filter
open scoped ComplexOrder Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator
  Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Qubit density with a fixed finite ancillary density matrix. -/
def qubitAncillaDensity (τ : Matrix κ κ ℂ) (b t : ℝ) :
    Matrix (Fin 2 × κ) (Fin 2 × κ) ℂ :=
  qubitDensity b t ⊗ₖ τ

/-- Literal quantum relative entropy after adjoining a common ancilla. -/
def qubitAncillaRelativeEntropy (τ : Matrix κ κ ℂ) (b s t : ℝ) : ℝ :=
  (Matrix.trace (qubitAncillaDensity τ b s *
    (CFC.log (qubitAncillaDensity τ b s) -
      CFC.log (qubitAncillaDensity τ b t)))).re

/-- Symmetrized quantum relative entropy after adjoining a common ancilla. -/
def qubitAncillaJeffreys (τ : Matrix κ κ ℂ) (b s t : ℝ) : ℝ :=
  qubitAncillaRelativeEntropy τ b s t +
    qubitAncillaRelativeEntropy τ b t s

/-- Reflected complete work after adjoining a common ancilla. -/
def qubitAncillaReflectedQuantumWork (τ : Matrix κ κ ℂ) (b t : ℝ) : ℝ :=
  qubitAncillaJeffreys τ b t (-t)

/-- Diagonal-observer deficit after adjoining an ignored common ancilla. -/
def qubitAncillaMeasurementDeficit (τ : Matrix κ κ ℂ) (b t : ℝ) : ℝ :=
  qubitAncillaReflectedQuantumWork τ b t - qubitObservedWork b t

theorem cfcLog_ancilla_isHermitian (τ : Matrix κ κ ℂ) :
    (CFC.log τ).IsHermitian := by
  change IsSelfAdjoint (CFC.log τ)
  cfc_tac

theorem cfcLog_qubitAncillaDensity (τ : Matrix κ κ ℂ) (hτ : τ.PosDef)
    (b t : ℝ) :
    CFC.log (qubitAncillaDensity τ b t) =
      kroneckerSum (qubitLogDensity b t) (CFC.log τ) := by
  have hsum := isHermitian_kroneckerSum
    (qubitLogDensity_isHermitian b t) (cfcLog_ancilla_isHermitian τ)
  have hexp : NormedSpace.exp
      (kroneckerSum (qubitLogDensity b t) (CFC.log τ)) =
        qubitAncillaDensity τ b t := by
    rw [exp_kroneckerSum, ← qubitDensity,
      CFC.exp_log (ha := hτ.isStrictlyPositive)]
    rfl
  rw [← hexp]
  exact CFC.log_exp _ hsum.isSelfAdjoint

omit [DecidableEq κ] in
theorem qubitAncillaDensity_posDef (τ : Matrix κ κ ℂ) (hτ : τ.PosDef)
    (b t : ℝ) :
    (qubitAncillaDensity τ b t).PosDef := by
  exact (qubitDensity_posDef b t).kronecker hτ

omit [DecidableEq κ] in
theorem qubitAncillaDensity_trace_one {b : ℝ} (hb : 0 < b)
    (τ : Matrix κ κ ℂ) (hτtrace : Matrix.trace τ = 1) (t : ℝ) :
    Matrix.trace (qubitAncillaDensity τ b t) = 1 := by
  rw [qubitAncillaDensity, Matrix.trace_kronecker,
    qubitDensity_trace_one hb, hτtrace, one_mul]

theorem qubitAncillaDensity_reflection {b : ℝ} (hb : 0 < b)
    (τ : Matrix κ κ ℂ) (t : ℝ) :
    (QuantumAlg.pauliX ⊗ₖ (1 : Matrix κ κ ℂ)) *
          qubitAncillaDensity τ b t *
          (QuantumAlg.pauliX ⊗ₖ (1 : Matrix κ κ ℂ)) =
      qubitAncillaDensity τ b (-t) := by
  rw [qubitAncillaDensity, qubitAncillaDensity,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, qubitDensity_reflection hb]

theorem cfcLog_qubitAncillaDensity_sub (τ : Matrix κ κ ℂ) (hτ : τ.PosDef)
    (b s t : ℝ) :
    CFC.log (qubitAncillaDensity τ b s) -
        CFC.log (qubitAncillaDensity τ b t) =
      (qubitLogDensity b s - qubitLogDensity b t) ⊗ₖ
        (1 : Matrix κ κ ℂ) := by
  rw [cfcLog_qubitAncillaDensity τ hτ,
    cfcLog_qubitAncillaDensity τ hτ]
  ext i j
  simp [kroneckerSum]
  ring

/-- NQP.22: a common faithful normalized ancilla adds zero quantum relative entropy. -/
theorem qubitAncillaRelativeEntropy_eq {b : ℝ}
    (τ : Matrix κ κ ℂ) (hτ : τ.PosDef)
    (hτtrace : Matrix.trace τ = 1) (s t : ℝ) :
    qubitAncillaRelativeEntropy τ b s t =
      qubitQuantumRelativeEntropy b s t := by
  rw [qubitAncillaRelativeEntropy, qubitQuantumRelativeEntropy,
    cfcLog_qubitAncillaDensity_sub τ hτ,
    qubitAncillaDensity, cfcLog_qubitDensity, cfcLog_qubitDensity,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.trace_kronecker, hτtrace, mul_one]

/-- A common faithful normalized ancilla preserves quantum Jeffreys work exactly. -/
theorem qubitAncillaJeffreys_eq {b : ℝ}
    (τ : Matrix κ κ ℂ) (hτ : τ.PosDef)
    (hτtrace : Matrix.trace τ = 1) (s t : ℝ) :
    qubitAncillaJeffreys τ b s t = qubitQuantumJeffreys b s t := by
  rw [qubitAncillaJeffreys, qubitQuantumJeffreys,
    qubitAncillaRelativeEntropy_eq τ hτ hτtrace,
    qubitAncillaRelativeEntropy_eq τ hτ hτtrace]

theorem qubitAncillaReflectedQuantumWork_eq
    (τ : Matrix κ κ ℂ) (hτ : τ.PosDef)
    (hτtrace : Matrix.trace τ = 1) (b t : ℝ) :
    qubitAncillaReflectedQuantumWork τ b t =
      qubitReflectedQuantumWork b t := by
  rw [qubitAncillaReflectedQuantumWork, qubitReflectedQuantumWork,
    qubitAncillaJeffreys_eq τ hτ hτtrace]

theorem qubitAncillaMeasurementDeficit_eq
    (τ : Matrix κ κ ℂ) (hτ : τ.PosDef)
    (hτtrace : Matrix.trace τ = 1) (b t : ℝ) :
    qubitAncillaMeasurementDeficit τ b t =
      qubitMeasurementDeficit b t := by
  rw [qubitAncillaMeasurementDeficit, qubitMeasurementDeficit,
    qubitAncillaReflectedQuantumWork_eq τ hτ hτtrace]

theorem qubitAncillaMeasurementDeficit_nonneg {b : ℝ} (hb : 0 < b)
    (τ : Matrix κ κ ℂ) (hτ : τ.PosDef)
    (hτtrace : Matrix.trace τ = 1) (t : ℝ) :
    0 ≤ qubitAncillaMeasurementDeficit τ b t := by
  rw [qubitAncillaMeasurementDeficit_eq τ hτ hτtrace]
  exact qubitMeasurementDeficit_nonneg hb t

theorem tendsto_qubitAncillaMeasurementDeficit_div_four_mul
    {b : ℝ} (hb : 0 < b) (τ : Matrix κ κ ℂ) (hτ : τ.PosDef)
    (hτtrace : Matrix.trace τ = 1) :
    Tendsto (fun t : ℝ =>
      qubitAncillaMeasurementDeficit τ b t / (4 * t))
      atTop (𝓝 1) := by
  simpa only [qubitAncillaMeasurementDeficit_eq τ hτ hτtrace] using
    tendsto_qubitMeasurementDeficit_div_four_mul hb

end

end GaloisForLFunctions.HTGeometry
