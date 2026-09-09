import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalContraction

/-!
# Exact stationary-state classification and finite-temperature purity obstruction

The positive damping form exposed by the energy mechanism of arXiv:2609.04530
classifies the kernel of the constructed thermal Lindblad generator. A single
positive physical time has the same fixed trace ray. Exponential bath coordinates
produce full-rank Gibbs carriers, excluding all trace-one rank-deficient stationary
matrices, with no Hermiticity or positivity assumption. The positive survivor is
the explicit and complete stationary-ray classification.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Every scalar multiple of the constructed bath is stationary for the differential generator. -/
theorem spinThermalLindblad_bath_smul (a u : ℝ) (c : ℂ) :
    spinThermalLindblad a u (c • spinBathDensity u) = 0 := by
  rw [spinThermalLindblad_entries, Matrix.trace_smul, spinBathDensity_trace, spinBathDensity_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, mul_comm]

/-- The same full trace ray is fixed by every physical channel step. -/
theorem spinThermalChannel_bath_smul (a u : ℝ) (t : NNReal) (c : ℂ) :
    (spinThermalChannel a u t).map (c • spinBathDensity u) = c • spinBathDensity u := by
  rw [spinThermalChannel_entries, Matrix.trace_smul, spinBathDensity_trace, spinBathDensity_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> ring

/-- Exact kernel classification: positive damping leaves only the stationary trace ray. -/
theorem spinThermalLindblad_eq_zero_iff (s u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalLindblad (Real.exp s) u ρ = 0 ↔ ρ = Matrix.trace ρ • spinBathDensity u := by
  constructor
  · intro h
    apply (spinThermalDissipation_eq_zero_iff s u ρ).mp
    rw [spinThermalDissipation_trace, h]
    simp
  · intro h
    rw [h]
    exact spinThermalLindblad_bath_smul _ _ _

/-- A single positive physical time has exactly the same stationary trace ray. -/
theorem spinThermalChannel_fixed_iff (s u q : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinThermalChannel (Real.exp s) u (spinThermalPositiveTime q)).map ρ = ρ ↔
      ρ = Matrix.trace ρ • spinBathDensity u := by
  constructor
  · intro h
    have hb := (spinThermalEnergy_channel_bounds (Real.exp s) u (spinThermalPositiveTime q) ρ).2
    rw [h] at hb
    have hE : 0 ≤ spinThermalEnergy u ρ := finiteMatrixHilbertSchmidtEnergy_nonneg _
    have hz : spinThermalEnergy u ρ = 0 := by
      by_contra hn
      have hp : 0 < spinThermalEnergy u ρ := lt_of_le_of_ne hE (Ne.symm hn)
      have hh := mul_lt_mul_of_pos_right (spinThermalPositiveTime_mass_lt_one s q) hp
      simp only [one_mul] at hh
      exact (not_lt_of_ge hb) hh
    exact (spinThermalEnergy_eq_zero_iff u ρ).mp hz
  · intro h
    conv_lhs => rw [h]
    rw [spinThermalChannel_bath_smul]
    exact h.symm

/-- Discrete-time stationarity and infinitesimal stationarity coincide under constructed positive damping. -/
theorem spinThermalChannel_fixed_iff_generator_zero (s u q : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinThermalChannel (Real.exp s) u (spinThermalPositiveTime q)).map ρ = ρ ↔
      spinThermalLindblad (Real.exp s) u ρ = 0 := by
  rw [spinThermalChannel_fixed_iff, spinThermalLindblad_eq_zero_iff]

/-- Exponentially parametrized bath coordinates put positive mass in the lower level as well. -/
theorem spinBathLower_exp_pos (v : ℝ) : 0 < spinBathLower (Real.exp v) := by
  rw [← (spinBath_weights (Real.exp v)).1]
  exact pow_pos (mul_pos (Real.exp_pos v) (spinChartScale_pos _)) 2

/-- Every finite Gibbs bath is full rank, witnessed by a strictly positive real determinant. -/
theorem spinBathDensity_exp_det_pos (v : ℝ) : 0 < (Matrix.det (spinBathDensity (Real.exp v))).re := by
  rw [spinBathDensity_entries, Matrix.det_fin_two]
  simpa using mul_pos (spinBathUpper_pos (Real.exp v)) (spinBathLower_exp_pos v)

/-- No normalized pure chart state equals a finite Gibbs bath. -/
theorem spinChartDensity_ne_thermalBath (v : ℝ) (z : ℂ) : spinChartDensity z ≠ spinBathDensity (Real.exp v) := by
  intro h
  have hd := congrArg (fun ρ : Matrix (Fin 2) (Fin 2) ℂ => (Matrix.det ρ).re) h
  rw [spinChartDensity_det] at hd
  have hp := spinBathDensity_exp_det_pos v
  simp only [Complex.zero_re] at hd
  linarith

/-- Every constructed pure state experiences nonzero thermal Lindblad motion at finite bath bias. -/
theorem spinThermalLindblad_pure_ne_zero (s v : ℝ) (z : ℂ) :
    spinThermalLindblad (Real.exp s) (Real.exp v) (spinChartDensity z) ≠ 0 := by
  intro h
  have heq := (spinThermalLindblad_eq_zero_iff s (Real.exp v) (spinChartDensity z)).mp h
  rw [spinChartDensity_trace, one_smul] at heq
  exact spinChartDensity_ne_thermalBath v z heq

/-- Consequently no positive channel time fixes any normalized pure chart input at finite bath bias. -/
theorem spinThermalChannel_pure_ne_self (s v q : ℝ) (z : ℂ) :
    (spinThermalChannel (Real.exp s) (Real.exp v) (spinThermalPositiveTime q)).map (spinChartDensity z) ≠
      spinChartDensity z := by
  intro h
  exact spinThermalLindblad_pure_ne_zero s v z
    ((spinThermalChannel_fixed_iff_generator_zero s (Real.exp v) q (spinChartDensity z)).mp h)

/-- Finite Gibbs baths exclude every trace-one rank-deficient stationary matrix, even without Hermiticity. -/
theorem spinThermalLindblad_no_rankOne_stationary (s v : ℝ) :
    ¬ ∃ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.trace ρ = 1 ∧ Matrix.det ρ = 0 ∧ spinThermalLindblad (Real.exp s) (Real.exp v) ρ = 0 := by
  rintro ⟨ρ, ht, hd, hL⟩
  have heq := (spinThermalLindblad_eq_zero_iff s (Real.exp v) ρ).mp hL
  rw [ht, one_smul] at heq
  have hzero : Matrix.det (spinBathDensity (Real.exp v)) = 0 := by
    rw [← heq]
    exact hd
  have hp := spinBathDensity_exp_det_pos v
  rw [hzero] at hp
  exact (lt_irrefl (0 : ℝ)) hp

/-- No positive-time channel step has a trace-one rank-deficient fixed matrix. -/
theorem spinThermalChannel_no_rankOne_fixed (s v q : ℝ) :
    ¬ ∃ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.trace ρ = 1 ∧ Matrix.det ρ = 0 ∧
        (spinThermalChannel (Real.exp s) (Real.exp v) (spinThermalPositiveTime q)).map ρ = ρ := by
  rintro ⟨ρ, ht, hd, hf⟩
  exact spinThermalLindblad_no_rankOne_stationary s v ⟨ρ, ht, hd,
    (spinThermalChannel_fixed_iff_generator_zero s (Real.exp v) q ρ).mp hf⟩

end
end GaloisForLFunctions.HTGeometry.SchafferExl
