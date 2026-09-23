import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinDensityFlow
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinGibbs
import GaloisForLFunctions.HTGeometry.TwoOutcomePinchingKadison

/-!
# Measurement, Gibbs populations, and exact reduced spin dynamics

Applications of Schaffer–Exl's spin mechanism (arXiv:2609.04530) to the corpus's
Higgs vacuum cutoff, two-outcome pinching channel, and full qubit Gibbs density.
Measured spin trajectories are exact Gibbs states with drifting bias. The
original nonlinear field vanishes on diagonal matrices, so measurement does
not commute with its evolution. The positive replacement is a closed Riccati
population ODE, proved along the actual measured trajectory. Every parameter
is unrestricted; noncommutation is witnessed using exponential constructions.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- The corpus's actual north Higgs vacuum record used as a two-outcome measurement cutoff. -/
def spinZCutoff : Matrix (Fin 2) (Fin 2) ℂ :=
  higgsSpinorEventMatrix abelianHiggsSpinorVacuum

/-- The Higgs vacuum record is the upper Z measurement projector. -/
theorem spinZCutoff_entries : spinZCutoff = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinZCutoff, higgsSpinorEventMatrix, abelianHiggsSpinorVacuum, Matrix.vecMulVec_apply]

/-- Actual existing two-outcome pinching, specialized to the Higgs vacuum cutoff. -/
def spinZPinch (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  _root_.HTGeometry.twoOutcomePinching spinZCutoff ρ

/-- The existing measurement channel deletes precisely the two coherence entries. -/
theorem spinZPinch_entries (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinZPinch ρ = !![ρ 0 0, 0; 0, ρ 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinZPinch, _root_.HTGeometry.twoOutcomePinching, spinZCutoff_entries,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Measurement preserves the literal quantum Z expectation for arbitrary input matrices. -/
theorem spinZPinch_expectation_Z (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (Matrix.trace (spinZPinch ρ * QuantumAlg.pauliZ)).re =
      (Matrix.trace (ρ * QuantumAlg.pauliZ)).re := by
  rw [spinZPinch_entries]
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, QuantumAlg.pauliZ]

/-- The measured real-spin density retains only its latitude. -/
theorem spinZPinch_spinMatrix (m : EuclideanSpace ℝ (Fin 3)) :
    spinZPinch (spinMatrix m) = (1 / 2 : ℂ) •
      (1 + (m 2 : ℂ) • QuantumAlg.pauliZ) := by
  rw [spinZPinch_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinMatrix, lorentzHermitianMatrix, QuantumAlg.pauliZ, Matrix.smul_apply]
  ring

/-- The measured tangent matrix is exactly its energy derivative times Z/2. -/
theorem spinZPinch_spinMatrixTangent (v : EuclideanSpace ℝ (Fin 3)) :
    spinZPinch (spinMatrixTangent v) = ((v 2 / 2 : ℝ) : ℂ) • QuantumAlg.pauliZ := by
  rw [spinZPinch_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinMatrixTangent, spinMatrixLinear, lorentzHermitianMatrix,
      QuantumAlg.pauliZ, Matrix.smul_apply] <;> ring

/-- The full matrix field vanishes after measurement: every diagonal state commutes with Z. -/
theorem spinDensityField_pinched (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinDensityField a (spinZPinch ρ) = 0 := by
  rw [spinZPinch_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinDensityField, QuantumAlg.pauliZ]

/-- Measuring the original spin field retains its nonzero torque-driven population transfer. -/
theorem spinZPinch_field (a : ℝ) (m : EuclideanSpace ℝ (Fin 3)) :
    spinZPinch (spinDensityField a (spinMatrix m)) =
      ((-a ^ (2 : ℕ) * spinTorqueEnergy m / 2 : ℝ) : ℂ) • QuantumAlg.pauliZ := by
  rw [← spinMatrixTangent_field, spinZPinch_spinMatrixTangent,
    spinSphereField_components, spinTorqueEnergy_components]
  rfl

/-- The existing zero-coupling Gibbs density has its full diagonal polarization formula. -/
theorem qubitDensity_zero_coupling (b : ℝ) :
    qubitDensity 0 b = (1 / 2 : ℂ) • (1 + (Real.tanh b : ℂ) • QuantumAlg.pauliZ) := by
  rw [gomesQubitDensity_closed, qubitHamiltonian]
  simp only [Complex.ofReal_zero, zero_smul, add_zero, smul_smul, ← Complex.ofReal_mul]
  have hc : Real.tanh (qubitRadius 0 b) / qubitRadius 0 b * b = Real.tanh b := by
    rw [← qubitMean_zero_coupling b]
    unfold qubitMean
    ring
  rw [hc]

/-- Dephasing the exact spin trajectory produces the full Gibbs density, not only its Z mean. -/
theorem spinZPinch_densityFlow_gibbs (a x phase t : ℝ) :
    spinZPinch (spinDensityFlow a (spinLogSeed x phase) t) =
      qubitDensity 0 (x - a ^ (2 : ℕ) * t) := by
  rw [spinDensityFlow_eq_spinMatrix, spinZPinch_spinMatrix, spinSphereFlow_log_latitude,
    qubitDensity_zero_coupling]

/-- Exact reduced population field on the measured density: a closed Riccati latitude law. -/
def spinDiagonalField (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((-a ^ (2 : ℕ) * (1 - (Matrix.trace (ρ * QuantumAlg.pauliZ)).re ^ (2 : ℕ)) / 2 : ℝ) : ℂ) •
    QuantumAlg.pauliZ

/-- Purity supplies the missing closure term in the measured spin dynamics. -/
theorem spinZPinch_pure_field (a : ℝ) (z : ℂ) :
    spinZPinch (spinDensityField a (spinChartDensity z)) =
      spinDiagonalField a (spinZPinch (spinChartDensity z)) := by
  have he : spinChartDensity z = spinMatrix (_root_.Bottcher.stereo z) := spinChartDensity_lorentz z
  rw [he, spinZPinch_field, spinDiagonalField, spinZPinch_expectation_Z, spinMatrix_expectation_Z]
  have hn := spinTorqueEnergy_add_latitude_sq (_root_.Bottcher.stereo z)
  rw [_root_.Bottcher.norm_stereo_eq_one] at hn
  have ht : spinTorqueEnergy (_root_.Bottcher.stereo z) = 1 - _root_.Bottcher.stereo z 2 ^ (2 : ℕ) := by
    linarith
  rw [ht]

/-- The measured density solves its exact closed population ODE globally. -/
theorem hasDerivAt_spinZPinchedDensity (a : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun v => spinZPinch (spinDensityFlow a z v))
      (spinDiagonalField a (spinZPinch (spinDensityFlow a z t))) t := by
  have h := hasDerivAt_spinDensityFlow a z t
  have hp := ((h.const_mul spinZCutoff).mul_const spinZCutoff).add
    ((h.const_mul (1 - spinZCutoff)).mul_const (1 - spinZCutoff))
  change HasDerivAt (fun v => spinZPinch (spinDensityFlow a z v))
    (spinZPinch (spinDensityField a (spinDensityFlow a z t))) t at hp
  apply hp.congr_deriv
  exact spinZPinch_pure_field a (spinPlaneFlow a z t)

/-- The Gibbs population ODE is exactly the reduced spin equation along a linearly drifting bias. -/
theorem hasDerivAt_qubitGibbs_spinPopulation (a x t : ℝ) :
    HasDerivAt (fun v => qubitDensity 0 (x - a ^ (2 : ℕ) * v))
      (spinDiagonalField a (qubitDensity 0 (x - a ^ (2 : ℕ) * t))) t := by
  simpa only [spinZPinch_densityFlow_gibbs] using
    hasDerivAt_spinZPinchedDensity a (spinLogSeed x 0) t

/-- Exact torque in chart coordinates identifies precisely when the measurement loses dynamics. -/
theorem spinTorqueEnergy_stereo (z : ℂ) :
    spinTorqueEnergy (_root_.Bottcher.stereo z) = 4 * ‖z‖ ^ (2 : ℕ) / (1 + ‖z‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hd : 1 + ‖z‖ ^ (2 : ℕ) ≠ 0 := by positivity
  rw [spinTorqueEnergy_components]
  simp [_root_.Bottcher.stereo]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  field_simp
  ring

/-- A closed family where measurement and spin evolution do not commute. -/
theorem spinZPinch_field_not_commute (s : ℝ) (c : ℂ) :
    spinZPinch (spinDensityField (Real.exp s) (spinChartDensity (Complex.exp c))) ≠
      spinDensityField (Real.exp s) (spinZPinch (spinChartDensity (Complex.exp c))) := by
  have hp : 0 < spinTorqueEnergy (_root_.Bottcher.stereo (Complex.exp c)) := by
    rw [spinTorqueEnergy_stereo, Complex.norm_exp]
    positivity
  intro h
  have he : spinChartDensity (Complex.exp c) = spinMatrix (_root_.Bottcher.stereo (Complex.exp c)) :=
    spinChartDensity_lorentz _
  rw [spinDensityField_pinched, he, spinZPinch_field] at h
  have hz := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
  simp [Matrix.smul_apply, QuantumAlg.pauliZ, -Complex.ofReal_div, -Complex.ofReal_mul,
    -Complex.ofReal_pow, -Complex.ofReal_neg] at hz
  have ha := sq_pos_of_pos (Real.exp_pos s)
  nlinarith

end
end GaloisForLFunctions.HTGeometry.SchafferExl
