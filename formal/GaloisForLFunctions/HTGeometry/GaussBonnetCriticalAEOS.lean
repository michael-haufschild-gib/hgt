import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalAParameters

/-!
# Actual model-A pressure inflection and reduced equation of state

Verify equation (21) of arXiv:2609.00025 using the first and second actual
radial derivatives of its model-A pressure function. Dimensionless scaling
retains a genuine coupling parameter, unlike the effective-charge-only
model-B reduction. Its critical compressibility ratio is (3-2b)/8.
-/
noncomputable section
open Real Filter
namespace GaloisForLFunctions.HTGeometry

def egbPressureAD1 (T Q a r : ℝ) : ℝ :=
  -T / (2 * r ^ 2) - 3 * a ^ 2 * T / r ^ 4 + 1 / (4 * Real.pi * r ^ 3) - (Q ^ 2 + a ^ 2) / (2 * Real.pi * r ^ 5)
def egbPressureAD2 (T Q a r : ℝ) : ℝ :=
  T / r ^ 3 + 12 * a ^ 2 * T / r ^ 5 - 3 / (4 * Real.pi * r ^ 4) + 5 * (Q ^ 2 + a ^ 2) / (2 * Real.pi * r ^ 6)

theorem egbPressureA_hasDerivAt (T Q a x : ℝ) :
    HasDerivAt (egbPressureA T Q a) (egbPressureAD1 T Q a (exp x)) (exp x) := by
  have hi := hasDerivAt_id (exp x)
  have h₁ := (hasDerivAt_const (exp x) T).div (hi.const_mul 2) (by simp only [id_eq]; positivity)
  have h₂ := (hasDerivAt_const (exp x) (a ^ 2 * T)).div (hi.pow 3) (by simp only [Pi.pow_apply, id_eq]; positivity)
  have h₃ := (hasDerivAt_const (exp x) (1 : ℝ)).div ((hi.pow 2).const_mul (8 * Real.pi)) (by simp only [Pi.pow_apply, id_eq]; positivity)
  have h₄ := (hasDerivAt_const (exp x) (Q ^ 2 + a ^ 2)).div ((hi.pow 4).const_mul (8 * Real.pi)) (by simp only [Pi.pow_apply, id_eq]; positivity)
  have h := ((h₁.add h₂).sub h₃).add h₄
  apply h.congr_deriv
  unfold egbPressureAD1
  norm_num only [Nat.cast_ofNat, pow_one, Pi.pow_apply, id_eq]
  field_simp
  ring

theorem egbPressureAD1_hasDerivAt (T Q a x : ℝ) :
    HasDerivAt (egbPressureAD1 T Q a) (egbPressureAD2 T Q a (exp x)) (exp x) := by
  have hi := hasDerivAt_id (exp x)
  have h₁ := (hasDerivAt_const (exp x) (-T)).div ((hi.pow 2).const_mul 2) (by simp only [Pi.pow_apply, id_eq]; positivity)
  have h₂ := (hasDerivAt_const (exp x) (3 * a ^ 2 * T)).div (hi.pow 4) (by simp only [Pi.pow_apply, id_eq]; positivity)
  have h₃ := (hasDerivAt_const (exp x) (1 : ℝ)).div ((hi.pow 3).const_mul (4 * Real.pi)) (by simp only [Pi.pow_apply, id_eq]; positivity)
  have h₄ := (hasDerivAt_const (exp x) (Q ^ 2 + a ^ 2)).div ((hi.pow 5).const_mul (2 * Real.pi)) (by simp only [Pi.pow_apply, id_eq]; positivity)
  have h := ((h₁.sub h₂).add h₃).sub h₄
  apply h.congr_deriv
  unfold egbPressureAD2
  norm_num only [Nat.cast_ofNat, pow_one, Pi.pow_apply, id_eq]
  field_simp
  ring

/-- The symbolic second expression is the actual iterated radial derivative. -/
theorem egbPressureA_second_derivative (T Q a x : ℝ) :
    deriv (deriv (egbPressureA T Q a)) (exp x) = egbPressureAD2 T Q a (exp x) := by
  have he : deriv (egbPressureA T Q a) =ᶠ[nhds (exp x)] egbPressureAD1 T Q a := by
    have hp : ∀ᶠ r : ℝ in nhds (exp x), 0 < r := isOpen_Ioi.mem_nhds (exp_pos x)
    filter_upwards [hp] with r hr
    have h := (egbPressureA_hasDerivAt T Q a (log r)).deriv
    simpa only [exp_log hr] using h
  rw [he.deriv_eq]
  exact (egbPressureAD1_hasDerivAt T Q a x).deriv

theorem egbCriticalA_pressure_D1_zero (x θ : ℝ) :
    egbPressureAD1 (egbCriticalATemperature x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) (exp x) = 0 := by
  unfold egbPressureAD1
  rw [egbCriticalA_effective_charge, egbCriticalA_coupling_square]
  unfold egbCriticalATemperature
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp
  ring

theorem egbCriticalA_pressure_D2_zero (x θ : ℝ) :
    egbPressureAD2 (egbCriticalATemperature x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) (exp x) = 0 := by
  unfold egbPressureAD2
  rw [egbCriticalA_effective_charge, egbCriticalA_coupling_square]
  unfold egbCriticalATemperature
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp
  ring

/-- Both literal derivatives required by the paper's critical-point definition vanish. -/
theorem egbCriticalA_pressure_inflection (x θ : ℝ) :
    deriv (egbPressureA (egbCriticalATemperature x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ)) (exp x) = 0 ∧
      deriv (deriv (egbPressureA (egbCriticalATemperature x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ))) (exp x) = 0 := by
  rw [(egbPressureA_hasDerivAt _ _ _ x).deriv, egbPressureA_second_derivative,
    egbCriticalA_pressure_D1_zero, egbCriticalA_pressure_D2_zero]
  exact ⟨rfl, rfl⟩

/-- Reduced external temperature t and positive reduced radius exp v. -/
def egbReducedPressureA (θ t v : ℝ) : ℝ :=
  (8 * t / exp v + 16 * egbCriticalAShape θ * t / exp v ^ 3 -
      6 * (1 + 2 * egbCriticalAShape θ) / exp v ^ 2 +
        (1 - 6 * egbCriticalAShape θ) / exp v ^ 4) / (3 - 2 * egbCriticalAShape θ)

theorem egbPressureA_reduced_equation (x θ t v : ℝ) :
    egbPressureA (t * egbCriticalATemperature x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) (exp x * exp v) /
      egbCriticalAPressure x θ = egbReducedPressureA θ t v := by
  unfold egbPressureA
  rw [egbCriticalA_effective_charge, egbCriticalA_coupling_square]
  unfold egbCriticalATemperature egbCriticalAPressure egbReducedPressureA
  have hb := (egbCriticalAShape_bounds θ).1
  have hp : 0 < 3 - 2 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  field_simp
  ring

/-- Model A retains a coupling-dependent critical compressibility ratio. -/
theorem egbCriticalA_compressibility_ratio (x θ : ℝ) :
    egbCriticalAPressure x θ * (2 * exp x) / egbCriticalATemperature x θ = (3 - 2 * egbCriticalAShape θ) / 8 := by
  unfold egbCriticalAPressure egbCriticalATemperature
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp
  ring

/-- Unlike model B's 3/8 ratio, this ratio changes strictly with dimensionless coupling. -/
theorem egbCriticalA_compressibility_comparison (x θ φ : ℝ) :
    egbCriticalAPressure x θ * (2 * exp x) / egbCriticalATemperature x θ <
      egbCriticalAPressure x φ * (2 * exp x) / egbCriticalATemperature x φ ↔ egbCriticalAShape φ < egbCriticalAShape θ := by
  rw [egbCriticalA_compressibility_ratio, egbCriticalA_compressibility_ratio]
  constructor <;> intro h <;> linarith

end GaloisForLFunctions.HTGeometry
