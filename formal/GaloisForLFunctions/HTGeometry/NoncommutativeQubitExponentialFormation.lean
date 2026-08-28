import GaloisForLFunctions.HTGeometry.FiniteBuresObserverTiltLaw
import GaloisForLFunctions.QuantumAlg.Util.MatrixExpInvolution
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Algebras.SimpleDLA
import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Noncommutative qubit exponential formation

Literal Pauli `X/Z` Hamiltonians, their Banach-algebra exponential, normalized faithful density
matrices, reflection law, and exact quantum relative-entropy fusion.
-/

open Matrix
open scoped ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

def qubitRadius (b t : ℝ) : ℝ := Real.sqrt (t ^ 2 + b ^ 2)

def qubitHamiltonian (b t : ℝ) : QubitMatrix :=
  (t : ℂ) • QuantumAlg.pauliZ + (b : ℂ) • QuantumAlg.pauliX

theorem qubitRadius_pos {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 < qubitRadius b t := by
  rw [qubitRadius, Real.sqrt_pos]
  positivity

theorem qubitHamiltonian_isHermitian (b t : ℝ) :
    (qubitHamiltonian b t).IsHermitian := by
  change (qubitHamiltonian b t)ᴴ = qubitHamiltonian b t
  simp [qubitHamiltonian, QuantumAlg.pauliX_isHermitian,
    QuantumAlg.pauliZ_isHermitian]

theorem qubitHamiltonian_sq (b t : ℝ) :
    qubitHamiltonian b t * qubitHamiltonian b t =
      ((qubitRadius b t ^ 2 : ℝ) : ℂ) • (1 : QubitMatrix) := by
  have hr : qubitRadius b t ^ 2 = t ^ 2 + b ^ 2 := by
    rw [qubitRadius, Real.sq_sqrt]
    positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitHamiltonian, QuantumAlg.pauliX, QuantumAlg.pauliZ,
      Matrix.mul_apply, Fin.sum_univ_two, hr] <;> ring

theorem qubitHamiltonian_commutator (b s t : ℝ) :
    qubitHamiltonian b s * qubitHamiltonian b t -
        qubitHamiltonian b t * qubitHamiltonian b s =
      ((b * (s - t) : ℝ) : ℂ) •
        (QuantumAlg.pauliZ * QuantumAlg.pauliX -
          QuantumAlg.pauliX * QuantumAlg.pauliZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitHamiltonian, QuantumAlg.pauliX, QuantumAlg.pauliZ] <;> ring

theorem qubitHamiltonian_commutator_ne_zero {b s t : ℝ}
    (hb : 0 < b) (hst : s ≠ t) :
    qubitHamiltonian b s * qubitHamiltonian b t -
        qubitHamiltonian b t * qubitHamiltonian b s ≠ 0 := by
  rw [qubitHamiltonian_commutator]
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  simp [QuantumAlg.pauliX, QuantumAlg.pauliZ] at h01
  rcases h01 with hb0 | hst0
  · exact hb.ne' hb0
  · apply hst
    exact_mod_cast sub_eq_zero.mp hst0

theorem qubitHamiltonian_reflection (b t : ℝ) :
    QuantumAlg.pauliX * qubitHamiltonian b t * QuantumAlg.pauliX =
      qubitHamiltonian b (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitHamiltonian, QuantumAlg.pauliX, QuantumAlg.pauliZ]

theorem qubitHamiltonian_exp_closed {b : ℝ} (hb : 0 < b) (t : ℝ) :
    NormedSpace.exp (qubitHamiltonian b t) =
      ((Real.cosh (qubitRadius b t) : ℝ) : ℂ) • (1 : QubitMatrix) +
        ((Real.sinh (qubitRadius b t) / qubitRadius b t : ℝ) : ℂ) •
          qubitHamiltonian b t := by
  have hr : 0 < qubitRadius b t := qubitRadius_pos hb t
  let K : QubitMatrix := ((qubitRadius b t : ℂ)⁻¹) • qubitHamiltonian b t
  have hK : K * K = 1 := by
    simp only [K, smul_mul_smul_comm]
    rw [qubitHamiltonian_sq, smul_smul]
    have hrC : (qubitRadius b t : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [show ((qubitRadius b t ^ 2 : ℝ) : ℂ) = (qubitRadius b t : ℂ) ^ 2 by
      norm_cast]
    field_simp
    simp
  have hscale : (qubitRadius b t : ℂ) • K = qubitHamiltonian b t := by
    simp only [K, smul_smul]
    simp [hr.ne']
  have h := QuantumAlg.exp_smul_of_mul_self_eq_one (A := QubitMatrix)
    (qubitRadius b t : ℂ) hK
  rw [hscale] at h
  simpa [K, smul_smul, div_eq_mul_inv, Complex.ofReal_cosh,
    Complex.ofReal_sinh] using h

def qubitFreeEnergy (b t : ℝ) : ℝ :=
  Real.log (2 * Real.cosh (qubitRadius b t))

def qubitLogDensity (b t : ℝ) : QubitMatrix :=
  qubitHamiltonian b t - (qubitFreeEnergy b t : ℂ) • (1 : QubitMatrix)

def qubitDensity (b t : ℝ) : QubitMatrix :=
  NormedSpace.exp (qubitLogDensity b t)

def qubitMean (b t : ℝ) : ℝ :=
  t / qubitRadius b t * Real.tanh (qubitRadius b t)

theorem qubitLogDensity_isHermitian (b t : ℝ) :
    (qubitLogDensity b t).IsHermitian := by
  change (qubitLogDensity b t)ᴴ = qubitLogDensity b t
  rw [qubitLogDensity, Matrix.conjTranspose_sub,
    qubitHamiltonian_isHermitian]
  simp

theorem qubitDensity_posDef (b t : ℝ) :
    (qubitDensity b t).PosDef := by
  exact finiteBuresReporterExp_posDef (qubitLogDensity_isHermitian b t)

theorem cfcLog_qubitDensity (b t : ℝ) :
    CFC.log (qubitDensity b t) = qubitLogDensity b t := by
  exact CFC.log_exp _ (qubitLogDensity_isHermitian b t).isSelfAdjoint

theorem exp_neg_qubitFreeEnergy (b t : ℝ) :
    Real.exp (-qubitFreeEnergy b t) =
      1 / (2 * Real.cosh (qubitRadius b t)) := by
  rw [qubitFreeEnergy, Real.exp_neg,
    Real.exp_log (show 0 < 2 * Real.cosh (qubitRadius b t) by positivity)]
  simp [one_div]

theorem qubitDensity_eq_exp_neg_freeEnergy_smul_expHamiltonian (b t : ℝ) :
    qubitDensity b t =
      (Real.exp (-qubitFreeEnergy b t) : ℂ) •
        NormedSpace.exp (qubitHamiltonian b t) := by
  let z : ℂ := -(qubitFreeEnergy b t : ℂ)
  have hcomm : Commute (qubitHamiltonian b t) (z • (1 : QubitMatrix)) :=
    (Commute.one_right (qubitHamiltonian b t)).smul_right z
  have hone : (1 : QubitMatrix) * 1 = 1 := by simp
  have hexpOne : NormedSpace.exp (z • (1 : QubitMatrix)) =
      Complex.exp z • (1 : QubitMatrix) := by
    rw [QuantumAlg.exp_smul_of_mul_self_eq_one (A := QubitMatrix) z hone,
      ← add_smul, Complex.cosh_add_sinh]
  rw [qubitDensity, qubitLogDensity, sub_eq_add_neg, ← neg_smul]
  change NormedSpace.exp
      (qubitHamiltonian b t + z • (1 : QubitMatrix)) = _
  rw [QuantumAlg.exp_add_of_commute_ℂ hcomm, hexpOne]
  simp only [Matrix.mul_smul, Matrix.mul_one]
  rw [show Complex.exp z = (Real.exp (-qubitFreeEnergy b t) : ℂ) by
    rw [show z = ((-qubitFreeEnergy b t : ℝ) : ℂ) by simp [z],
      ← Complex.ofReal_exp]]

theorem qubitDensity_closed {b : ℝ} (hb : 0 < b) (t : ℝ) :
    qubitDensity b t =
      (1 / 2 : ℂ) • ((1 : QubitMatrix) +
        ((Real.tanh (qubitRadius b t) / qubitRadius b t : ℝ) : ℂ) •
          qubitHamiltonian b t) := by
  rw [qubitDensity_eq_exp_neg_freeEnergy_smul_expHamiltonian,
    exp_neg_qubitFreeEnergy, qubitHamiltonian_exp_closed hb]
  have hr : qubitRadius b t ≠ 0 := (qubitRadius_pos hb t).ne'
  have hc : Real.cosh (qubitRadius b t) ≠ 0 :=
    (Real.cosh_pos (qubitRadius b t)).ne'
  have hrC : (qubitRadius b t : ℂ) ≠ 0 := by exact_mod_cast hr
  have hcC : Complex.cosh (qubitRadius b t : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh]
    exact Complex.ofReal_ne_zero.mpr hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitHamiltonian, QuantumAlg.pauliX, QuantumAlg.pauliZ,
      Real.tanh_eq_sinh_div_cosh] <;>
    field_simp [hrC, hcC]

theorem qubitDensity_trace_one {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Matrix.trace (qubitDensity b t) = 1 := by
  rw [qubitDensity_closed hb]
  simp [Matrix.trace, qubitHamiltonian, QuantumAlg.pauliX,
    QuantumAlg.pauliZ, Fin.sum_univ_two]
  ring_nf

theorem qubitDensity_reflection {b : ℝ} (hb : 0 < b) (t : ℝ) :
    QuantumAlg.pauliX * qubitDensity b t * QuantumAlg.pauliX =
      qubitDensity b (-t) := by
  rw [qubitDensity_closed hb, qubitDensity_closed hb]
  have hr : qubitRadius b (-t) = qubitRadius b t := by
    simp [qubitRadius]
  rw [hr]
  have hXX : QuantumAlg.pauliX * QuantumAlg.pauliX = (1 : QubitMatrix) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [QuantumAlg.pauliX, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
  rw [hXX, qubitHamiltonian_reflection]

theorem qubitDensity_expectation_Z {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (Matrix.trace (qubitDensity b t * QuantumAlg.pauliZ)).re = qubitMean b t := by
  rw [qubitDensity_closed hb]
  simp [Matrix.trace, qubitHamiltonian, QuantumAlg.pauliX,
    QuantumAlg.pauliZ, Fin.sum_univ_two, Matrix.mul_apply, qubitMean]
  rw [← Complex.ofReal_tanh, Complex.ofReal_re]
  ring

/-- Quantum relative entropy of two states in the literal qubit exponential family. -/
def qubitQuantumRelativeEntropy (b s t : ℝ) : ℝ :=
  (Matrix.trace (qubitDensity b s *
    (CFC.log (qubitDensity b s) - CFC.log (qubitDensity b t)))).re

/-- Symmetrized quantum relative entropy (quantum Jeffreys work). -/
def qubitQuantumJeffreys (b s t : ℝ) : ℝ :=
  qubitQuantumRelativeEntropy b s t + qubitQuantumRelativeEntropy b t s

theorem qubitLogDensity_sub (b s t : ℝ) :
    qubitLogDensity b s - qubitLogDensity b t =
      ((s - t : ℝ) : ℂ) • QuantumAlg.pauliZ +
        ((qubitFreeEnergy b t - qubitFreeEnergy b s : ℝ) : ℂ) •
          (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitLogDensity, qubitHamiltonian, QuantumAlg.pauliX,
      QuantumAlg.pauliZ] <;> ring

theorem qubitQuantumRelativeEntropy_eq {b : ℝ} (hb : 0 < b) (s t : ℝ) :
    qubitQuantumRelativeEntropy b s t =
      (s - t) * qubitMean b s + qubitFreeEnergy b t - qubitFreeEnergy b s := by
  rw [qubitQuantumRelativeEntropy, cfcLog_qubitDensity,
    cfcLog_qubitDensity, qubitLogDensity_sub]
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_one]
  simp only [smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [qubitDensity_expectation_Z hb, qubitDensity_trace_one hb]
  norm_num
  ring

theorem qubitQuantumJeffreys_eq {b : ℝ} (hb : 0 < b) (s t : ℝ) :
    qubitQuantumJeffreys b s t =
      (s - t) * (qubitMean b s - qubitMean b t) := by
  rw [qubitQuantumJeffreys, qubitQuantumRelativeEntropy_eq hb,
    qubitQuantumRelativeEntropy_eq hb]
  ring

end

end GaloisForLFunctions.HTGeometry
