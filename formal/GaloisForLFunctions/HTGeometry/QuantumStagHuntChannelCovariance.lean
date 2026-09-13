import GaloisForLFunctions.HTGeometry.FinitePauliDepolarizing
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinInstrumentPinching
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinAmplitudeDamping

/-!
# Channel covariance in the decoherent quantum Stag Hunt

Channel-level realization of the covariance distinction in arXiv:2609.02957.
A dimension-generic depolarizing map commutes with every unitary conjugation. The
corpus's exact dephasing channel commutes with both Pauli game moves, while its
constructed amplitude-damping Kraus channel has an explicit Pauli-X counterexample.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate
open Matrix

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Dimension-generic trace-to-identity depolarizing map. -/
def finiteDepolarizingMap
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 - p) • X + (p / (Fintype.card n : ℂ) * X.trace) • 1

/-- Conjugation by a unitary matrix, encoded without a unitary premise. -/
def finiteUnitaryConjugate
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)ᴴ

theorem trace_finiteUnitaryConjugate
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    (finiteUnitaryConjugate U X).trace = X.trace := by
  have hU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  unfold finiteUnitaryConjugate
  calc
    ((U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)ᴴ).trace =
        ((U : Matrix n n ℂ)ᴴ * ((U : Matrix n n ℂ) * X)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (((U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ)) * X).trace := by
      rw [Matrix.mul_assoc]
    _ = X.trace := by rw [hU, Matrix.one_mul]

theorem finiteUnitaryConjugate_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) :
    finiteUnitaryConjugate U (1 : Matrix n n ℂ) = 1 := by
  have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := by
    change (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1
    exact Unitary.coe_mul_star_self U
  simp [finiteUnitaryConjugate, hU]

/-- Depolarization is covariant under every finite-dimensional unitary. -/
theorem finiteDepolarizingMap_unitary_covariant
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℂ) (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    finiteDepolarizingMap p (finiteUnitaryConjugate U X) =
      finiteUnitaryConjugate U (finiteDepolarizingMap p X) := by
  rw [finiteDepolarizingMap, finiteDepolarizingMap,
    trace_finiteUnitaryConjugate]
  unfold finiteUnitaryConjugate
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  rw [show (U : Matrix n n ℂ) * (1 : Matrix n n ℂ) *
      (U : Matrix n n ℂ)ᴴ = 1 by
        simpa [finiteUnitaryConjugate] using finiteUnitaryConjugate_one U]

/-- Corpus dephasing channel commutes with the Pauli-X game move. -/
theorem spinFilterChannel_covariant_pauliX
    (k : ℂ) (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    (SchafferExl.spinFilterChannel k).evolveMatrix
        (QuantumAlg.pauliX * rho * QuantumAlg.pauliX) =
      QuantumAlg.pauliX * (SchafferExl.spinFilterChannel k).evolveMatrix rho *
        QuantumAlg.pauliX := by
  rw [SchafferExl.spinFilterChannel_entries, SchafferExl.spinFilterChannel_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuantumAlg.pauliX, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

/-- Corpus dephasing channel commutes with the Pauli-Z game move. -/
theorem spinFilterChannel_covariant_pauliZ
    (k : ℂ) (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    (SchafferExl.spinFilterChannel k).evolveMatrix
        (QuantumAlg.pauliZ * rho * QuantumAlg.pauliZ) =
      QuantumAlg.pauliZ * (SchafferExl.spinFilterChannel k).evolveMatrix rho *
        QuantumAlg.pauliZ := by
  rw [SchafferExl.spinFilterChannel_entries, SchafferExl.spinFilterChannel_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuantumAlg.pauliZ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

/-- Basis-state witness for amplitude-damping noncovariance. -/
def spinUpperBasisDensity : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The corpus's physical amplitude-damping channel does not commute with Pauli X. -/
theorem spinAmplitudeChannel_not_covariant_pauliX :
    (SchafferExl.spinAmplitudeChannel 1 (1 : NNReal)).map
        (QuantumAlg.pauliX * spinUpperBasisDensity * QuantumAlg.pauliX) ≠
      QuantumAlg.pauliX *
        (SchafferExl.spinAmplitudeChannel 1 (1 : NNReal)).map spinUpperBasisDensity *
          QuantumAlg.pauliX := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  rw [SchafferExl.spinAmplitudeChannel_entries,
    SchafferExl.spinAmplitudeChannel_entries] at h00
  simp [QuantumAlg.pauliX, spinUpperBasisDensity, Matrix.mul_apply,
    Fin.sum_univ_two] at h00
  have h00re := congrArg Complex.re h00
  simp at h00re
  have hlt : SchafferExl.spinDecayMass 1 (1 : NNReal) < 1 := by
    rw [SchafferExl.spinDecayMass, Real.exp_lt_one_iff]
    norm_num
  linarith

end
end GaloisForLFunctions.HTGeometry
