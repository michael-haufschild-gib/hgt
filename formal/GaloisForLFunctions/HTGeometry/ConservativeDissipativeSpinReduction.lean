import GaloisForLFunctions.HTGeometry.ConservativeDissipativeMixedSpin
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinPinching

/-!
# Exact invariant closure and a measurement-only obstruction

The Schaffer–Exl spin mechanism (arXiv:2609.04530) exposes a precise reduction
boundary in the corpus's quantum measurement channel. An equatorial pure
state and the maximally mixed state have the same measured density but
unequal population derivatives, excluding a common field of that density
alone. The positive replacement is proved exactly: retaining squared Bloch
radius, equivalently twice initial quantum purity minus one, yields a closed
autonomous population ODE along every constructed mixed-state trajectory.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Exact reduced population field with one retained squared-radius invariant. -/
def spinReducedField (a q : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((-a ^ (2 : ℕ) * (q - (Matrix.trace (ρ * QuantumAlg.pauliZ)).re ^ (2 : ℕ)) / 2 : ℝ) : ℂ) • QuantumAlg.pauliZ

/-- One scalar invariant closes the measured field for every real spin, not only pure states. -/
theorem spinZPinch_field_reduced (a : ℝ) (m : EuclideanSpace ℝ (Fin 3)) :
    spinZPinch (spinDensityField a (spinMatrix m)) =
      spinReducedField a (‖m‖ ^ (2 : ℕ)) (spinZPinch (spinMatrix m)) := by
  rw [spinZPinch_field, spinReducedField, spinZPinch_expectation_Z, spinMatrix_expectation_Z]
  have h := spinTorqueEnergy_add_latitude_sq m
  have he : spinTorqueEnergy m = ‖m‖ ^ (2 : ℕ) - m 2 ^ (2 : ℕ) := by linarith
  rw [he]

/-- The pure-state Riccati equation is the unit-radius member of the exact invariant closure. -/
theorem spinReducedField_one (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinReducedField a 1 ρ = spinDiagonalField a ρ := rfl

/-- The retained squared radius is precisely twice quantum purity minus one. -/
theorem spinMixedDensity_radius_purity (a u : ℝ) (z : ℂ) (t : ℝ) :
    spinMixRadius u ^ (2 : ℕ) = 2 * (Matrix.trace (spinMixedDensity a u z t ^ (2 : ℕ))).re - 1 := by
  rw [spinMixedDensity_trace_pow]
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  unfold spinMixEigenPlus spinMixEigenMinus
  ring

/-- Measured mixed trajectories solve the augmented autonomous equation with their fixed invariant. -/
theorem hasDerivAt_spinZPinchedMixedDensity (a u : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun v => spinZPinch (spinMixedDensity a u z v))
      (spinReducedField a (spinMixRadius u ^ (2 : ℕ)) (spinZPinch (spinMixedDensity a u z t))) t := by
  have h := hasDerivAt_spinMixedDensity a u z t
  have hp := ((h.const_mul spinZCutoff).mul_const spinZCutoff).add
    ((h.const_mul (1 - spinZCutoff)).mul_const (1 - spinZCutoff))
  change HasDerivAt (fun v => spinZPinch (spinMixedDensity a u z v))
    (spinZPinch (spinDensityField a (spinMixedDensity a u z t))) t at hp
  apply hp.congr_deriv
  rw [spinMixedDensity, spinZPinch_field_reduced, spinMixedVector_norm]

/-- The augmented scalar can be read once from the initial full state's purity. -/
theorem hasDerivAt_spinZPinchedMixedDensity_initialPurity (a u : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun v => spinZPinch (spinMixedDensity a u z v))
      (spinReducedField a (2 * (Matrix.trace (spinMixedDensity a u z 0 ^ (2 : ℕ))).re - 1)
        (spinZPinch (spinMixedDensity a u z t))) t := by
  rw [← spinMixedDensity_radius_purity a u z 0]
  exact hasDerivAt_spinZPinchedMixedDensity a u z t

/-- The zero Bloch vector encodes the physical maximally mixed density. -/
theorem spinMatrix_zero : spinMatrix (0 : EuclideanSpace ℝ (Fin 3)) =
    (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [spinMatrix_decompose, map_zero, add_zero]

/-- The maximally mixed record is a positive trace-one state. -/
theorem spinMatrix_zero_state : (spinMatrix (0 : EuclideanSpace ℝ (Fin 3))).PosSemidef ∧
    Matrix.trace (spinMatrix (0 : EuclideanSpace ℝ (Fin 3))) = 1 := by
  constructor
  · rw [spinMatrix_zero]
    exact Matrix.PosSemidef.one.smul (by positivity : (0 : ℂ) ≤ 1 / 2)
  · exact spinMatrix_trace _

/-- The maximally mixed density is stationary for every raw damping amplitude. -/
theorem spinDensityField_zero_spin (a : ℝ) :
    spinDensityField a (spinMatrix (0 : EuclideanSpace ℝ (Fin 3))) = 0 := by
  rw [← spinMatrixTangent_field, spinSphereField_zero, map_zero]

/-- The finite equatorial pure spin and the maximally mixed state have the same measurement. -/
theorem spinZPinch_equator_eq_zero_spin :
    spinZPinch (spinChartDensity 1) = spinZPinch (spinMatrix (0 : EuclideanSpace ℝ (Fin 3))) := by
  have he : spinChartDensity 1 = spinMatrix (_root_.Bottcher.stereo 1) := spinChartDensity_lorentz 1
  rw [he, spinZPinch_spinMatrix, spinZPinch_spinMatrix]
  simp [_root_.Bottcher.stereo]

/-- The maximally mixed state's measured field vanishes. -/
theorem spinZPinch_field_zero_spin (a : ℝ) :
    spinZPinch (spinDensityField a (spinMatrix (0 : EuclideanSpace ℝ (Fin 3)))) = 0 := by
  rw [spinDensityField_zero_spin, spinZPinch_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Equal measured states can have different actual population derivatives under positive damping. -/
theorem spinZPinch_same_state_different_derivative (s : ℝ) :
    spinZPinch (spinChartDensity 1) = spinZPinch (spinMatrix (0 : EuclideanSpace ℝ (Fin 3))) ∧
      spinZPinch (spinDensityField (Real.exp s) (spinChartDensity 1)) ≠
        spinZPinch (spinDensityField (Real.exp s) (spinMatrix (0 : EuclideanSpace ℝ (Fin 3)))) := by
  refine ⟨spinZPinch_equator_eq_zero_spin, ?_⟩
  rw [spinZPinch_field_zero_spin]
  have h := spinZPinch_field_not_commute s 0
  simpa only [Complex.exp_zero, spinDensityField_pinched] using h

/-- No vector field of the measured density alone can reproduce both of these physical states. -/
theorem spinZPinch_no_state_only_closure (s : ℝ) :
    ¬ ∃ F : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ,
      F (spinZPinch (spinChartDensity 1)) =
        spinZPinch (spinDensityField (Real.exp s) (spinChartDensity 1)) ∧
      F (spinZPinch (spinMatrix (0 : EuclideanSpace ℝ (Fin 3)))) =
        spinZPinch (spinDensityField (Real.exp s) (spinMatrix (0 : EuclideanSpace ℝ (Fin 3)))) := by
  rintro ⟨F, h1, h0⟩
  exact (spinZPinch_same_state_different_derivative s).2
    (h1.symm.trans ((congrArg F spinZPinch_equator_eq_zero_spin).trans h0))

end
end GaloisForLFunctions.HTGeometry.SchafferExl
