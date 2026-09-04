import GaloisForLFunctions.HTGeometry.RydbergProjectorDephasing
import GaloisForLFunctions.RHTower.DQPTProbeDensityMatrix

open scoped BigOperators Matrix

noncomputable section

namespace RHTower

open DQPT

/-- Ground-state projector for the two-level Rydberg atom. -/
def rydbergGroundProjector : QuantumMatrix 2 := !![1, 0; 0, 0]

/-- Excited-state occupation projector `|r><r|`. -/
def rydbergOccupation : QuantumMatrix 2 := !![0, 0; 0, 1]

/-- Amplitude-decay jump `|g><r|`. -/
def rydbergDecayJump : QuantumMatrix 2 := !![0, 1; 0, 0]

@[simp] theorem rydbergOccupation_conjTranspose : rydbergOccupationᴴ = rydbergOccupation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rydbergOccupation, Matrix.conjTranspose_apply]

@[simp] theorem rydbergOccupation_mul_self : rydbergOccupation * rydbergOccupation = rydbergOccupation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rydbergOccupation, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem rydbergDecayJump_effect :
    rydbergDecayJumpᴴ * rydbergDecayJump = rydbergOccupation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rydbergDecayJump, rydbergOccupation, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem rydbergOccupation_effect :
    rydbergOccupationᴴ * rydbergOccupation = rydbergOccupation := by
  rw [rydbergOccupation_conjTranspose, rydbergOccupation_mul_self]

/-- Decay and dephasing have the same anticommutator drain. -/
theorem rydberg_decay_dephasing_same_drain (X : QuantumMatrix 2) :
    finiteLindbladDrain rydbergDecayJump X = finiteLindbladDrain rydbergOccupation X := by
  exact finiteLindbladDrain_eq_of_effect_eq _ _ _
    (rydbergDecayJump_effect.trans rydbergOccupation_effect.symm)

/-- Decay and dephasing differ only in their gain terms. -/
theorem rydberg_decay_dephasing_difference_is_gain (X : QuantumMatrix 2) :
    finiteLindbladDissipator rydbergDecayJump X -
        finiteLindbladDissipator rydbergOccupation X =
      finiteLindbladGain rydbergDecayJump X - finiteLindbladGain rydbergOccupation X := by
  exact finiteLindbladDissipator_sub_eq_gain_sub_of_effect_eq _ _ _
    (rydbergDecayJump_effect.trans rydbergOccupation_effect.symm)

theorem rydbergDecayJump_gain (X : QuantumMatrix 2) :
    finiteLindbladGain rydbergDecayJump X = X 1 1 • rydbergGroundProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteLindbladGain, rydbergDecayJump, rydbergGroundProjector,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

theorem rydbergOccupation_gain (X : QuantumMatrix 2) :
    finiteLindbladGain rydbergOccupation X = X 1 1 • rydbergOccupation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteLindbladGain, rydbergOccupation, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Exact anisotropy: decay moves excited population to ground while dephasing returns it to
the excited block. -/
theorem rydberg_decay_dephasing_exact_anisotropy (X : QuantumMatrix 2) :
    finiteLindbladDissipator rydbergDecayJump X -
        finiteLindbladDissipator rydbergOccupation X =
      X 1 1 • (rydbergGroundProjector - rydbergOccupation) := by
  rw [rydberg_decay_dephasing_difference_is_gain,
    rydbergDecayJump_gain, rydbergOccupation_gain, smul_sub]

/-- The non-Hermitian effect sees only the sum of decay and dephasing rates. -/
theorem rydberg_weighted_effect_eq_total_rate
    (decayRate dephasingRate : ℝ) :
    (decayRate : ℂ) • (rydbergDecayJumpᴴ * rydbergDecayJump) +
        (dephasingRate : ℂ) • (rydbergOccupationᴴ * rydbergOccupation) =
      ((decayRate + dephasingRate : ℝ) : ℂ) • rydbergOccupation := by
  rw [rydbergDecayJump_effect, rydbergOccupation_effect]
  push_cast
  exact (add_smul _ _ _).symm

/-- Centering the occupation jump by `I/2` is a dissipator gauge symmetry. -/
theorem rydberg_centered_dephasing_gauge (X : QuantumMatrix 2) :
    finiteLindbladDissipator
        (rydbergOccupation - ((1 / 2 : ℝ) : ℂ) • 1) X =
      finiteLindbladDissipator rydbergOccupation X := by
  exact finiteLindbladDissipator_sub_real_smul_one
    rydbergOccupation X (1 / 2) rydbergOccupation_conjTranspose

theorem rydbergOccupation_commutes_diagonal (score : Fin 2 → ℂ) :
    rydbergOccupation * Matrix.diagonal score =
      Matrix.diagonal score * rydbergOccupation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rydbergOccupation, Matrix.diagonal, Matrix.mul_apply]

/-- Every diagonal score is immune to terminal Rydberg dephasing. -/
theorem rydberg_diagonal_score_dephasing_damage_eq_zero
    (score : Fin 2 → ℂ) (ρ : QuantumMatrix 2) :
    finiteLindbladObservableDamage rydbergOccupation (Matrix.diagonal score) ρ = 0 := by
  exact finiteLindbladObservableDamage_projector_eq_zero_of_commute
    rydbergOccupation (Matrix.diagonal score) ρ
    rydbergOccupation_mul_self rydbergOccupation_conjTranspose
    (rydbergOccupation_commutes_diagonal score)

/-- Terminal decay damage to the occupation score is exactly the excited population. -/
theorem rydberg_decay_occupation_damage (ρ : QuantumMatrix 2) :
    finiteLindbladObservableDamage rydbergDecayJump rydbergOccupation ρ = (ρ 1 1).re := by
  simp only [finiteLindbladObservableDamage, finiteLindbladObservableResponse,
    finiteLindbladDissipator, finiteLindbladGain, finiteLindbladDrain]
  simp [rydbergDecayJump, rydbergOccupation, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_two]
  ring

/-- Terminal dephasing has no direct occupation-score damage. -/
theorem rydberg_dephasing_occupation_damage (ρ : QuantumMatrix 2) :
    finiteLindbladObservableDamage rydbergOccupation rydbergOccupation ρ = 0 := by
  exact rydberg_diagonal_score_dephasing_damage_eq_zero ![0, 1] ρ

/-- For the occupation score, a weighted decay/dephasing mixture has only the decay contribution. -/
theorem rydberg_weighted_occupation_damage
    (decayRate dephasingRate : ℝ) (ρ : QuantumMatrix 2) :
    decayRate * finiteLindbladObservableDamage rydbergDecayJump rydbergOccupation ρ +
        dephasingRate * finiteLindbladObservableDamage rydbergOccupation rydbergOccupation ρ =
      decayRate * (ρ 1 1).re := by
  rw [rydberg_decay_occupation_damage, rydberg_dephasing_occupation_damage]
  ring

/-- Projector dephasing damps the transverse `σ_x` mode at half rate. -/
theorem rydberg_dephasing_sigmaX :
    finiteLindbladDissipator rydbergOccupation dqptSigmaX =
      -(2 : ℂ)⁻¹ • dqptSigmaX := by
  rw [finiteLindbladDissipator, finiteLindbladGain, finiteLindbladDrain,
    rydbergOccupation_conjTranspose, rydbergOccupation_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rydbergOccupation, dqptSigmaX]

/-- Projector dephasing damps the transverse `σ_y` mode at half rate. -/
theorem rydberg_dephasing_sigmaY :
    finiteLindbladDissipator rydbergOccupation dqptSigmaY =
      -(2 : ℂ)⁻¹ • dqptSigmaY := by
  rw [finiteLindbladDissipator, finiteLindbladGain, finiteLindbladDrain,
    rydbergOccupation_conjTranspose, rydbergOccupation_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rydbergOccupation, dqptSigmaY]

/-- Projector dephasing preserves the longitudinal `σ_z` mode. -/
theorem rydberg_dephasing_sigmaZ :
    finiteLindbladDissipator rydbergOccupation dqptSigmaZ = 0 := by
  rw [finiteLindbladDissipator, finiteLindbladGain, finiteLindbladDrain,
    rydbergOccupation_conjTranspose, rydbergOccupation_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rydbergOccupation, dqptSigmaZ]

/-- Decay damps the longitudinal `σ_z` mode at full rate. -/
theorem rydberg_decay_sigmaZ :
    finiteLindbladDissipator rydbergDecayJump dqptSigmaZ = -dqptSigmaZ := by
  rw [finiteLindbladDissipator, finiteLindbladGain, finiteLindbladDrain,
    rydbergDecayJump_effect]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rydbergDecayJump, rydbergOccupation, dqptSigmaZ,
      Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

end RHTower
