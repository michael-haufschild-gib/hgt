import GaloisForLFunctions.HTGeometry.GomesTwoBandAdjointMass

/-!
# Closing the qubit Gibbs family before transporting its internal frame

The internal-frame transport viewpoint of Gomes, arXiv:2404.10461,
requires transporting the actual qubit model through zero and negative coupling.
Its existing closed Gibbs and information identities assumed positive coupling.
This module supplies the missing all-real statements, including the zero-radius
Hamiltonian. The matrix exponential is proved by normalized involution away
from the origin and directly at the origin. No coupling or bias premise remains.
-/

set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The only zero-radius carrier is the zero Hamiltonian, including zero coupling. -/
theorem gomesQubitRadius_zero_iff (b t : ℝ) : qubitRadius b t = 0 ↔ b = 0 ∧ t = 0 := by
  have hr : qubitRadius b t ^ (2 : ℕ) = t^(2 : ℕ)+b^(2 : ℕ) :=
    Real.sq_sqrt (add_nonneg (sq_nonneg t) (sq_nonneg b))
  constructor
  · intro h
    rw [h] at hr
    constructor <;> nlinarith [sq_nonneg b,sq_nonneg t]
  · rintro ⟨rfl,rfl⟩
    simp [qubitRadius]

/-- The Hamiltonian exponential formula extends to every coupling and bias, including the origin. -/
theorem gomesQubitHamiltonian_exp (b t : ℝ) :
    NormedSpace.exp (qubitHamiltonian b t) =
      (Real.cosh (qubitRadius b t) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((Real.sinh (qubitRadius b t) / qubitRadius b t : ℝ) : ℂ) • qubitHamiltonian b t := by
  by_cases hr : qubitRadius b t = 0
  · obtain ⟨rfl,rfl⟩ := (gomesQubitRadius_zero_iff b t).mp hr
    simp [qubitHamiltonian,qubitRadius]
  · let K : Matrix (Fin 2) (Fin 2) ℂ := ((qubitRadius b t : ℂ)⁻¹) • qubitHamiltonian b t
    have hrC : (qubitRadius b t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    have hK : K*K = 1 := by
      rw [show K*K = ((qubitRadius b t : ℂ)⁻¹*(qubitRadius b t : ℂ)⁻¹) •
        (qubitHamiltonian b t * qubitHamiltonian b t) by simp [K,smul_smul]]
      rw [qubitHamiltonian_sq,smul_smul]
      rw [show ((qubitRadius b t ^ (2 : ℕ) : ℝ) : ℂ) = (qubitRadius b t : ℂ)^(2 : ℕ) by norm_cast]
      field_simp
      simp
    have hscale : (qubitRadius b t : ℂ) • K = qubitHamiltonian b t := by
      simp only [K,smul_smul]
      simp [hr]
    have h := QuantumAlg.exp_smul_of_mul_self_eq_one (A := Matrix (Fin 2) (Fin 2) ℂ)
      (qubitRadius b t : ℂ) hK
    rw [hscale] at h
    simpa [K,smul_smul,div_eq_mul_inv,Complex.ofReal_cosh,Complex.ofReal_sinh] using h

/-- The partition trace formula has no positive-coupling premise. -/
theorem gomesQubitHamiltonian_trace_exp (b t : ℝ) :
    Matrix.trace (NormedSpace.exp (qubitHamiltonian b t)) =
      ((2*Real.cosh (qubitRadius b t) : ℝ) : ℂ) := by
  rw [gomesQubitHamiltonian_exp,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul]
  simp [Matrix.trace,qubitHamiltonian,QuantumAlg.pauliX,QuantumAlg.pauliZ,Fin.sum_univ_two]
  ring

/-- The existing free energy is the logarithm of the actual partition trace everywhere. -/
theorem gomesQubitFreeEnergy_log_trace (b t : ℝ) :
    qubitFreeEnergy b t = Real.log (Matrix.trace (NormedSpace.exp (qubitHamiltonian b t))).re := by
  rw [gomesQubitHamiltonian_trace_exp]
  rfl

/-- Exact normalization by the partition trace, with the degenerate carrier included. -/
theorem gomesQubitDensity_normalized_exp (b t : ℝ) :
    qubitDensity b t = (Matrix.trace (NormedSpace.exp (qubitHamiltonian b t)))⁻¹ •
      NormedSpace.exp (qubitHamiltonian b t) := by
  rw [qubitDensity_eq_exp_neg_freeEnergy_smul_expHamiltonian,
    gomesQubitHamiltonian_trace_exp,exp_neg_qubitFreeEnergy]
  congr 1
  push_cast
  rw [one_div]

/-- The exact Gibbs carrier formula holds even at the maximally mixed origin. -/
theorem gomesQubitDensity_closed (b t : ℝ) :
    qubitDensity b t = (1/2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((Real.tanh (qubitRadius b t) / qubitRadius b t : ℝ) : ℂ) • qubitHamiltonian b t) := by
  rw [qubitDensity_eq_exp_neg_freeEnergy_smul_expHamiltonian,
    exp_neg_qubitFreeEnergy,gomesQubitHamiltonian_exp]
  have hc : Real.cosh (qubitRadius b t) ≠ 0 := (Real.cosh_pos (qubitRadius b t)).ne'
  have hcC : Complex.cosh (qubitRadius b t : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh]
    exact Complex.ofReal_ne_zero.mpr hc
  by_cases hr : qubitRadius b t = 0
  · obtain ⟨rfl,rfl⟩ := (gomesQubitRadius_zero_iff b t).mp hr
    simp [qubitRadius,qubitHamiltonian]
  · have hrC : (qubitRadius b t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qubitHamiltonian,QuantumAlg.pauliX,QuantumAlg.pauliZ,Real.tanh_eq_sinh_div_cosh] <;>
      field_simp [hrC,hcC]

/-- Every state in the literal all-real qubit family has unit trace. -/
theorem gomesQubitDensity_trace_one (b t : ℝ) : Matrix.trace (qubitDensity b t) = 1 := by
  rw [gomesQubitDensity_closed]
  simp [Matrix.trace,qubitHamiltonian,QuantumAlg.pauliX,QuantumAlg.pauliZ,Fin.sum_univ_two]
  ring

/-- Bias reflection remains unitary transport when coupling is zero or negative. -/
theorem gomesQubitDensity_reflection (b t : ℝ) :
    QuantumAlg.pauliX * qubitDensity b t * QuantumAlg.pauliX = qubitDensity b (-t) := by
  rw [gomesQubitDensity_closed,gomesQubitDensity_closed]
  have hr : qubitRadius b (-t) = qubitRadius b t := by simp [qubitRadius]
  rw [hr]
  have hXX : QuantumAlg.pauliX * QuantumAlg.pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [QuantumAlg.pauliX,Matrix.mul_apply,Fin.sum_univ_two]
  rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_add,Matrix.add_mul]
  simp only [Matrix.mul_one,Matrix.mul_smul,Matrix.smul_mul]
  rw [hXX,qubitHamiltonian_reflection]

/-- The literal Z expectation formula has no nondegeneracy premise. -/
theorem gomesQubitDensity_expectation_Z (b t : ℝ) :
    (Matrix.trace (qubitDensity b t * QuantumAlg.pauliZ)).re = qubitMean b t := by
  rw [gomesQubitDensity_closed]
  simp [Matrix.trace,qubitHamiltonian,QuantumAlg.pauliX,QuantumAlg.pauliZ,
    Fin.sum_univ_two,Matrix.mul_apply,qubitMean]
  rw [← Complex.ofReal_tanh,Complex.ofReal_re]
  ring

/-- The corpus's quantum relative-entropy identity extends to every real coupling. -/
theorem gomesQubitRelativeEntropy_closed (b s t : ℝ) :
    qubitQuantumRelativeEntropy b s t =
      (s-t)*qubitMean b s+qubitFreeEnergy b t-qubitFreeEnergy b s := by
  rw [qubitQuantumRelativeEntropy,cfcLog_qubitDensity,cfcLog_qubitDensity,qubitLogDensity_sub]
  rw [Matrix.mul_add,Matrix.trace_add,Matrix.mul_smul,Matrix.trace_smul,
    Matrix.mul_smul,Matrix.trace_smul,Matrix.mul_one]
  simp only [smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  rw [gomesQubitDensity_expectation_Z,gomesQubitDensity_trace_one]
  simp only [Complex.one_re,mul_one]
  ring

/-- The symmetrized information identity also includes the zero-coupling locus. -/
theorem gomesQubitJeffreys_closed (b s t : ℝ) :
    qubitQuantumJeffreys b s t = (s-t)*(qubitMean b s-qubitMean b t) := by
  rw [qubitQuantumJeffreys,gomesQubitRelativeEntropy_closed,gomesQubitRelativeEntropy_closed]
  ring

end GaloisForLFunctions.HTGeometry
