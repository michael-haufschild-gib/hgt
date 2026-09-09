import GaloisForLFunctions.HTGeometry.TwoReplicaPositiveGraphEdgeCasimir
import GaloisForLFunctions.HTGeometry.RydbergProjectorDephasing

set_option autoImplicit false

/-!
# Conservative–dissipative quantum laws

Applications of Schaffer–Exl, arXiv:2609.04530, to constructed operators
and the existing mathematical objects used below.
-/

open scoped Matrix InnerProductSpace
open Matrix QuantumAlg
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hermitian coefficient constructed without a self-adjointness premise. -/
def hermitianPart (A : Matrix n n ℂ) : Matrix n n ℂ := A + Aᴴ

omit [Fintype n] [DecidableEq n] in
theorem hermitianPart_star (A : Matrix n n ℂ) : (hermitianPart A)ᴴ = hermitianPart A := by
  simp [hermitianPart, add_comm]

/-- Quantum conservative–dissipative motion: Hamiltonian commutation and double-commutator damping. -/
def quantumField (A B X : Matrix n n ℂ) : Matrix n n ℂ :=
  Complex.I • ringCommutator (hermitianPart A) X -
    ringCommutator (hermitianPart B) (ringCommutator (hermitianPart B) X)

/-- Hamiltonian commutation has a real quadratic form before multiplication by `i`. -/
theorem commutator_expectation_im (A X : Matrix n n ℂ) :
    (hsInner X (ringCommutator (hermitianPart A) X)).im = 0 := by
  have hc := hsInner_conj_symm X (ringCommutator (hermitianPart A) X)
  rw [hsInner_ringCommutator_selfAdjoint _ X X (hermitianPart_star A)] at hc
  have h := congrArg Complex.im hc
  simp only [Complex.conj_im] at h
  change (hsInner X (ringCommutator (hermitianPart A) X)).im =
    -(hsInner X (ringCommutator (hermitianPart A) X)).im at h
  linarith

/-- Double-commutator damping loses exactly the Hilbert–Schmidt commutator energy. -/
theorem quantumField_power (A B X : Matrix n n ℂ) :
    (hsInner X (quantumField A B X)).re =
      -(hsInner (ringCommutator (hermitianPart B) X)
        (ringCommutator (hermitianPart B) X)).re := by
  rw [quantumField, hsInner_sub_right, hsInner_smul_right, Complex.sub_re,
    ← hsInner_ringCommutator_selfAdjoint _ X _ (hermitianPart_star B)]
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    commutator_expectation_im]
  ring

theorem quantumField_power_nonpos (A B X : Matrix n n ℂ) :
    (hsInner X (quantumField A B X)).re ≤ 0 := by
  rw [quantumField_power]
  exact neg_nonpos.mpr (hsInner_self_re_nonneg _)

/-- The lossless quantum observables are exactly the commutant of the damping coefficient. -/
theorem quantumField_lossless_iff (A B X : Matrix n n ℂ) :
    (hsInner X (quantumField A B X)).re = 0 ↔
      ringCommutator (hermitianPart B) X = 0 := by
  rw [quantumField_power, neg_eq_zero,
    ← inner_finiteMatrixHilbertEquiv_eq_hsInner]
  change RCLike.re ⟪finiteMatrixHilbertEquiv (ringCommutator (hermitianPart B) X),
    finiteMatrixHilbertEquiv (ringCommutator (hermitianPart B) X)⟫_ℂ = 0 ↔ _
  rw [inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero]
  exact finiteMatrixHilbertEquiv.map_eq_zero_iff

/-- Exact identification with the corpus Lindblad dissipator for every Hermitian jump. -/
theorem hermitian_lindblad_eq_doubleCommutator {d : ℕ} (A X : RHTower.QuantumMatrix d) :
    RHTower.finiteLindbladDissipator (hermitianPart A) X =
      (-((2 : ℂ)⁻¹)) • ringCommutator (hermitianPart A)
        (ringCommutator (hermitianPart A) X) := by
  simp only [RHTower.finiteLindbladDissipator, RHTower.finiteLindbladGain,
    RHTower.finiteLindbladDrain, hermitianPart_star, ringCommutator,
    mul_sub, sub_mul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.mul_assoc]
  ring

end
end GaloisForLFunctions.HTGeometry.SchafferExl
