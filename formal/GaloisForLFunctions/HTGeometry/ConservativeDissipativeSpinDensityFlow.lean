import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinorLift
import GaloisForLFunctions.QuantumAlg.Util.Haar
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Exact nonlinear quantum spin evolution and spectral invariants

Schaffer–Exl's conservative–dissipative spin mechanism (arXiv:2609.04530) is
pushed through the existing Higgs/Lorentz Hermitian encoding. The actual pure
density trajectory solves a precession plus state-dependent double-commutator
ODE. The field has an exact Lax form and annihilates every infinitesimal trace
power, while its literal Z-energy derivative is minus squared spin torque.
All matrix and real-vector parameters are unrestricted.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Affine Hermitian encoding of a real spin; the second Pauli coordinate has Lorentz orientation. -/
def spinMatrix (m : EuclideanSpace ℝ (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • lorentzHermitianMatrix 1 (m 0) (m 1) (m 2)

/-- The real-linear tangent map of the affine spin encoding. -/
def spinMatrixLinear : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun v := (1 / 2 : ℂ) • lorentzHermitianMatrix 0 (v 0) (v 1) (v 2)
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lorentzHermitianMatrix, Matrix.smul_apply] <;> ring
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lorentzHermitianMatrix, Matrix.smul_apply, Complex.real_smul] <;> ring

/-- Continuous tangent map, supplied by finite-dimensional linear geometry. -/
def spinMatrixTangent : EuclideanSpace ℝ (Fin 3) →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  spinMatrixLinear.toContinuousLinearMap

/-- Exact affine decomposition of the spin encoding. -/
theorem spinMatrix_decompose (m : EuclideanSpace ℝ (Fin 3)) :
    spinMatrix m = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + spinMatrixTangent m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinMatrix, spinMatrixTangent, spinMatrixLinear, lorentzHermitianMatrix,
      Matrix.smul_apply] <;> ring

/-- Unconditional derivative of the affine spin encoding. -/
theorem hasFDerivAt_spinMatrix (m : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt spinMatrix spinMatrixTangent m := by
  have hc : HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin 3) =>
      (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ) m := hasFDerivAt_const _ m
  have hl : HasFDerivAt (fun x => spinMatrixTangent x) spinMatrixTangent m :=
    spinMatrixTangent.hasFDerivAt
  have h := hc.add hl
  have he : spinMatrix = (fun _ : EuclideanSpace ℝ (Fin 3) =>
      (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) + (fun x => spinMatrixTangent x) :=
    funext spinMatrix_decompose
  rw [he]
  simpa only [zero_add] using h

/-- The spin encoding is Hermitian for every real vector. -/
theorem spinMatrix_isHermitian (m : EuclideanSpace ℝ (Fin 3)) : (spinMatrix m).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [spinMatrix, lorentzHermitianMatrix, Matrix.smul_apply]
  ring

/-- Trace normalization is affine and does not need a unit-spin premise. -/
theorem spinMatrix_trace (m : EuclideanSpace ℝ (Fin 3)) : Matrix.trace (spinMatrix m) = 1 := by
  simp [spinMatrix, lorentzHermitianMatrix, Matrix.trace, Fin.sum_univ_two]
  ring

/-- The north-directed spin energy is exactly the actual quantum Z expectation. -/
theorem spinMatrix_expectation_Z (m : EuclideanSpace ℝ (Fin 3)) :
    (Matrix.trace (spinMatrix m * QuantumAlg.pauliZ)).re = m 2 := by
  simp [spinMatrix, lorentzHermitianMatrix, QuantumAlg.pauliZ, Matrix.trace,
    Fin.sum_univ_two, Complex.mul_re]
  ring

/-- Nonlinear conservative–dissipative quantum spin field: precession plus double-bracket damping. -/
def spinDensityField (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2) • (QuantumAlg.pauliZ * ρ - ρ * QuantumAlg.pauliZ) -
    ((a ^ (2 : ℕ) / 2 : ℝ) : ℂ) •
      (ρ * (ρ * QuantumAlg.pauliZ - QuantumAlg.pauliZ * ρ) -
        (ρ * QuantumAlg.pauliZ - QuantumAlg.pauliZ * ρ) * ρ)

/-- The classical spin field is exactly the nonlinear matrix field for every raw real spin. -/
theorem spinMatrixTangent_field (a : ℝ) (m : EuclideanSpace ℝ (Fin 3)) :
    spinMatrixTangent (spinSphereField a m) = spinDensityField a (spinMatrix m) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [spinMatrixTangent, spinMatrixLinear, spinDensityField, spinMatrix,
      spinSphereField_components, lorentzHermitianMatrix, QuantumAlg.pauliZ,
      Complex.mul_re, Complex.mul_im,
      -Complex.ofReal_pow, -Complex.ofReal_add, -Complex.ofReal_mul,
      -Complex.ofReal_div, -Complex.ofReal_sub]
  all_goals ring_nf
  all_goals simp

/-- The state-dependent Lax generator exposes the isospectral form of spin damping. -/
def spinDensityLax (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2) • QuantumAlg.pauliZ +
    ((a ^ (2 : ℕ) / 2 : ℝ) : ℂ) • (ρ * QuantumAlg.pauliZ - QuantumAlg.pauliZ * ρ)

/-- Exact Lax commutator form; no Hermiticity or positivity premise is needed. -/
theorem spinDensityField_lax (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinDensityField a ρ = spinDensityLax a ρ * ρ - ρ * spinDensityLax a ρ := by
  simp only [spinDensityField, spinDensityLax, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  module

/-- Every spectral power has zero infinitesimal trace change, even for an arbitrary raw matrix. -/
theorem spinDensityField_trace_power (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    Matrix.trace (ρ ^ n * spinDensityField a ρ) = 0 := by
  rw [spinDensityField_lax, Matrix.mul_sub, Matrix.trace_sub]
  apply sub_eq_zero.mpr
  calc
    Matrix.trace (ρ ^ n * (spinDensityLax a ρ * ρ)) =
        Matrix.trace ((ρ * ρ ^ n) * spinDensityLax a ρ) := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    _ = Matrix.trace (ρ ^ n * (ρ * spinDensityLax a ρ)) := by
      rw [← pow_succ', pow_succ, Matrix.mul_assoc]

/-- Trace preservation is a special case of the full infinitesimal spectral invariant law. -/
theorem spinDensityField_trace (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (spinDensityField a ρ) = 0 := by
  simpa only [pow_zero, Matrix.one_mul] using spinDensityField_trace_power a ρ 0

/-- The tangent encoding preserves the literal Z-energy coordinate. -/
theorem spinMatrixTangent_expectation_Z (v : EuclideanSpace ℝ (Fin 3)) :
    (Matrix.trace (spinMatrixTangent v * QuantumAlg.pauliZ)).re = v 2 := by
  simp [spinMatrixTangent, spinMatrixLinear, lorentzHermitianMatrix, QuantumAlg.pauliZ,
    Matrix.trace, Fin.sum_univ_two, Complex.mul_re]
  ring

/-- Quantum spin damping loses exactly the classical squared torque energy. -/
theorem spinDensityField_energy (a : ℝ) (m : EuclideanSpace ℝ (Fin 3)) :
    (Matrix.trace (spinDensityField a (spinMatrix m) * QuantumAlg.pauliZ)).re =
      -a ^ (2 : ℕ) * spinTorqueEnergy m := by
  rw [← spinMatrixTangent_field, spinMatrixTangent_expectation_Z,
    spinSphereField_components, spinTorqueEnergy_components]
  rfl

/-- Energy dissipation holds for every real spin, including mixed-state radii. -/
theorem spinDensityField_energy_nonpos (a : ℝ) (m : EuclideanSpace ℝ (Fin 3)) :
    (Matrix.trace (spinDensityField a (spinMatrix m) * QuantumAlg.pauliZ)).re ≤ 0 := by
  rw [spinDensityField_energy]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg a)) (spinTorqueEnergy_nonneg m)

/-- The actual pure density trajectory induced by the global spin solution. -/
def spinDensityFlow (a : ℝ) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  spinChartDensity (spinPlaneFlow a z t)

/-- The spinor density and affine real-spin encoding are exactly the same trajectory. -/
theorem spinDensityFlow_eq_spinMatrix (a : ℝ) (z : ℂ) (t : ℝ) :
    spinDensityFlow a z t = spinMatrix (spinSphereFlow a z t) :=
  spinChartDensity_lorentz _

/-- The pure density trajectory solves the nonlinear quantum ODE globally in real time. -/
theorem hasDerivAt_spinDensityFlow (a : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (spinDensityFlow a z) (spinDensityField a (spinDensityFlow a z t)) t := by
  have h : HasDerivAt (fun s => spinMatrix (spinSphereFlow a z s))
      (spinMatrixTangent (spinSphereField a (spinSphereFlow a z t))) t :=
    (hasFDerivAt_spinMatrix (spinSphereFlow a z t)).comp_hasDerivAt t
      (hasDerivAt_spinSphereFlow a z t)
  have he : spinDensityFlow a z = fun s => spinMatrix (spinSphereFlow a z s) :=
    funext (spinDensityFlow_eq_spinMatrix a z)
  rw [he]
  simpa only [Function.comp_def, spinMatrixTangent_field] using h

/-- Positivity, normalization and purity hold at every time along the actual quantum ODE. -/
theorem spinDensityFlow_state (a : ℝ) (z : ℂ) (t : ℝ) :
    (spinDensityFlow a z t).PosSemidef ∧ Matrix.trace (spinDensityFlow a z t) = 1 ∧
      spinDensityFlow a z t * spinDensityFlow a z t = spinDensityFlow a z t :=
  ⟨spinChartDensity_posSemidef _, spinChartDensity_trace _, spinChartDensity_sq _⟩

end
end GaloisForLFunctions.HTGeometry.SchafferExl
