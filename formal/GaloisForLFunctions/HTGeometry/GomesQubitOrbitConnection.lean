import GaloisForLFunctions.HTGeometry.GomesQubitOrbitTransport
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Differential internal-frame transport of the qubit Gibbs family

Applies the fundamental-vector-field and induced-connection laws of Gomes,
arXiv:2404.10461, Appendix A, to the corpus's actual Y gate and qubit Gibbs state.
The moving coupling and bias solve the rotation equations. The anti-Hermitian
gate generator induces the commutator tangent on both the Hamiltonian and its
normalized density. Their associated covariant derivatives vanish, and free
energy is constant along the orbit. Every statement includes the zero carrier.
-/

set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The moving coupling differentiates to the moving bias. -/
theorem gomesQubitOrbitCoupling_hasDerivAt (b t theta : ℝ) :
    HasDerivAt (gomesQubitOrbitCoupling b t) (gomesQubitOrbitBias b t theta) theta := by
  change HasDerivAt (fun x => Real.cos x*b+Real.sin x*t) _ theta
  simpa [gomesQubitOrbitBias,Pi.add_def] using
    ((Real.hasDerivAt_cos theta).mul_const b).add ((Real.hasDerivAt_sin theta).mul_const t)

/-- The moving bias differentiates to minus the moving coupling. -/
theorem gomesQubitOrbitBias_hasDerivAt (b t theta : ℝ) :
    HasDerivAt (gomesQubitOrbitBias b t) (-gomesQubitOrbitCoupling b t theta) theta := by
  change HasDerivAt (fun x => -Real.sin x*b+Real.cos x*t) _ theta
  simpa [gomesQubitOrbitCoupling,Pi.add_def,Pi.neg_def,neg_add_rev,add_comm] using
    (((Real.hasDerivAt_sin theta).neg).mul_const b).add ((Real.hasDerivAt_cos theta).mul_const t)

/-- Infinitesimal generator of the actual quantum Y gate. -/
def gomesQubitYGenerator : Matrix (Fin 2) (Fin 2) ℂ := (-Complex.I/2) • QuantumAlg.pauliY

/-- The internal-frame generator is anti-Hermitian. -/
theorem gomesQubitYGenerator_skew : gomesQubitYGeneratorᴴ = -gomesQubitYGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesQubitYGenerator,QuantumAlg.pauliY,Matrix.conjTranspose_apply] <;> ring

/-- Its adjoint fundamental vector field is the tangent to the Hamiltonian's parameter circle. -/
theorem gomesQubitYGenerator_hamiltonian (b t : ℝ) :
    gomesQubitYGenerator*qubitHamiltonian b t-qubitHamiltonian b t*gomesQubitYGenerator =
      qubitHamiltonian t (-b) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [gomesQubitYGenerator,qubitHamiltonian,QuantumAlg.pauliY,
      QuantumAlg.pauliX,QuantumAlg.pauliZ] <;> ring

/-- The actual Gibbs state's infinitesimal frame action is the same Hamiltonian tangent, thermally scaled. -/
theorem gomesQubitYGenerator_density (b t : ℝ) :
    gomesQubitYGenerator*qubitDensity b t-qubitDensity b t*gomesQubitYGenerator =
      ((Real.tanh (qubitRadius b t)/qubitRadius b t/2 : ℝ) : ℂ) • qubitHamiltonian t (-b) := by
  rw [gomesQubitDensity_closed]
  have h : gomesQubitYGenerator * ((1/2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((Real.tanh (qubitRadius b t)/qubitRadius b t : ℝ) : ℂ) • qubitHamiltonian b t)) -
      ((1/2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((Real.tanh (qubitRadius b t)/qubitRadius b t : ℝ) : ℂ) • qubitHamiltonian b t)) *
          gomesQubitYGenerator =
      ((Real.tanh (qubitRadius b t)/qubitRadius b t/2 : ℝ) : ℂ) •
        (gomesQubitYGenerator*qubitHamiltonian b t-qubitHamiltonian b t*gomesQubitYGenerator) := by
    simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_one,Matrix.one_mul,smul_add,smul_sub,smul_smul]
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    push_cast
    ring
  rw [h,gomesQubitYGenerator_hamiltonian]

/-- Differentiating the genuine Hamiltonian orbit gives the associated connection equation. -/
theorem gomesQubitOrbit_hamiltonian_hasDerivAt (b t theta : ℝ) :
    HasDerivAt (fun x => qubitHamiltonian (gomesQubitOrbitCoupling b t x) (gomesQubitOrbitBias b t x))
      (gomesQubitYGenerator * qubitHamiltonian (gomesQubitOrbitCoupling b t theta)
          (gomesQubitOrbitBias b t theta) -
        qubitHamiltonian (gomesQubitOrbitCoupling b t theta) (gomesQubitOrbitBias b t theta) *
          gomesQubitYGenerator) theta := by
  rw [gomesQubitYGenerator_hamiltonian]
  have hb := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt theta
    (gomesQubitOrbitCoupling_hasDerivAt b t theta)
  have ht := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt theta
    (gomesQubitOrbitBias_hasDerivAt b t theta)
  simpa [qubitHamiltonian,Pi.add_def,Function.comp_def,Complex.ofRealCLM_apply] using
    (ht.smul_const QuantumAlg.pauliZ).add (hb.smul_const QuantumAlg.pauliX)

/-- The normalized Gibbs orbit solves the same adjoint connection equation without a spectral-gap premise. -/
theorem gomesQubitOrbit_density_hasDerivAt (b t theta : ℝ) :
    HasDerivAt (fun x => qubitDensity (gomesQubitOrbitCoupling b t x) (gomesQubitOrbitBias b t x))
      (gomesQubitYGenerator * qubitDensity (gomesQubitOrbitCoupling b t theta)
          (gomesQubitOrbitBias b t theta) -
        qubitDensity (gomesQubitOrbitCoupling b t theta) (gomesQubitOrbitBias b t theta) *
          gomesQubitYGenerator) theta := by
  rw [gomesQubitYGenerator_density,gomesQubitOrbit_radius]
  have hh := gomesQubitOrbit_hamiltonian_hasDerivAt b t theta
  rw [gomesQubitYGenerator_hamiltonian] at hh
  have hd := (hasDerivAt_const theta (1 : Matrix (Fin 2) (Fin 2) ℂ)).add
    (hh.const_smul ((Real.tanh (qubitRadius b t)/qubitRadius b t : ℝ) : ℂ))
  have h := hd.const_smul (1/2 : ℂ)
  simpa [gomesQubitDensity_closed,gomesQubitOrbit_radius,Pi.add_def,Pi.smul_def,
    smul_smul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h

/-- The associated adjoint connection on actual qubit matrix-valued trajectories. -/
def gomesQubitOrbitDerivative (A : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (theta : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  deriv A theta - (gomesQubitYGenerator*A theta-A theta*gomesQubitYGenerator)

/-- The transported Hamiltonian is parallel for the actual gate's adjoint connection. -/
theorem gomesQubitOrbit_hamiltonian_parallel (b t theta : ℝ) :
    gomesQubitOrbitDerivative
      (fun x => qubitHamiltonian (gomesQubitOrbitCoupling b t x) (gomesQubitOrbitBias b t x)) theta = 0 := by
  unfold gomesQubitOrbitDerivative
  exact sub_eq_zero.mpr (gomesQubitOrbit_hamiltonian_hasDerivAt b t theta).deriv

/-- The normalized Gibbs state is parallel for that same connection. -/
theorem gomesQubitOrbit_density_parallel (b t theta : ℝ) :
    gomesQubitOrbitDerivative
      (fun x => qubitDensity (gomesQubitOrbitCoupling b t x) (gomesQubitOrbitBias b t x)) theta = 0 := by
  unfold gomesQubitOrbitDerivative
  exact sub_eq_zero.mpr (gomesQubitOrbit_density_hasDerivAt b t theta).deriv

/-- Its scalar free energy has zero ordinary derivative along the associated orbit. -/
theorem gomesQubitOrbit_freeEnergy_hasDerivAt (b t theta : ℝ) :
    HasDerivAt (fun x => qubitFreeEnergy (gomesQubitOrbitCoupling b t x) (gomesQubitOrbitBias b t x))
      0 theta := by
  simp only [gomesQubitOrbit_freeEnergy]
  exact hasDerivAt_const theta _

end GaloisForLFunctions.HTGeometry
