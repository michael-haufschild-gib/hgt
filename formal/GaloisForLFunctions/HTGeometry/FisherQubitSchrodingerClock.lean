import GaloisForLFunctions.HTGeometry.FisherQubitClock

/-!
# Schrödinger evolution in an explicitly calibrated Fisher parameter

Equations (22)--(27) of arXiv:2605.03958 in units `hbar = 1`, for the
actual two-level clock. Its Hamiltonian is `frequency * sigma_y / 2`.
Hermiticity, the Schrödinger equation, zero mean energy, energy variance,
and the unit-speed informational reparameterization are all proved directly.
-/
open scoped InnerProductSpace Matrix
noncomputable section
namespace HTGeometry

/-- Hermitian two-level generator of the real-amplitude qubit rotation. -/
def fisherQubitHamiltonian (frequency : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I * frequency / 2; Complex.I * frequency / 2, 0]

/-- Hamiltonian action in the actual Euclidean Hilbert space. -/
def fisherQubitHamiltonianAction (frequency : ℝ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fisherQubitHamiltonian frequency *ᵥ WithLp.ofLp psi)

theorem fisherQubitHamiltonian_hermitian (frequency : ℝ) :
    (fisherQubitHamiltonian frequency).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fisherQubitHamiltonian, Matrix.conjTranspose_apply]

theorem fisherQubitHamiltonian_tangent (frequency phase t : ℝ) :
    fisherQubitHamiltonianAction frequency (fisherQubitClockState frequency phase t) =
      Complex.I • fisherQubitClockTangent frequency phase t := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [fisherQubitHamiltonianAction, fisherQubitHamiltonian,
      fisherQubitClockState, fisherQubitClockTangent, qgtQubitState, qgtQubitTangent] <;> ring

/-- The trajectory satisfies the actual Schrödinger differential equation. -/
theorem fisherQubitClock_schrodinger (frequency phase t : ℝ) :
    Complex.I • deriv (fisherQubitClockState frequency phase) t =
      fisherQubitHamiltonianAction frequency (fisherQubitClockState frequency phase t) := by
  rw [(fisherQubitClock_hasDerivAt frequency phase t).deriv,
    fisherQubitHamiltonian_tangent]

theorem fisherQubitClock_energy_mean (frequency phase t : ℝ) :
    inner ℂ (fisherQubitClockState frequency phase t)
      (fisherQubitHamiltonianAction frequency (fisherQubitClockState frequency phase t)) = 0 := by
  rw [fisherQubitHamiltonian_tangent, inner_smul_right]
  simp [fisherQubitClockState, fisherQubitClockTangent, qgtQubitState_inner_tangent]

/-- The Hamiltonian second moment, hence its variance, is exactly one quarter squared frequency. -/
theorem fisherQubitClock_energy_variance (frequency phase t : ℝ) :
    ‖fisherQubitHamiltonianAction frequency (fisherQubitClockState frequency phase t)‖ ^ 2 =
      frequency ^ 2 / 4 := by
  rw [fisherQubitHamiltonian_tangent, norm_smul, Complex.norm_I, one_mul]
  unfold fisherQubitClockTangent
  rw [qgtQubitTangent_norm_sq]
  ring

/-- The paper's speed--energy relation holds for both signs and the stationary frequency. -/
theorem fisherQubitClock_speed_energy (frequency phase t : ℝ) :
    Real.sqrt (fisherQubitClockInformation frequency phase t) =
      2 * ‖fisherQubitHamiltonianAction frequency (fisherQubitClockState frequency phase t)‖ := by
  rw [fisherQubitClock_speed]
  have h := congrArg Real.sqrt (fisherQubitClock_energy_variance frequency phase t)
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs] at h
  norm_num at h
  linarith

/-- Positive frequency disappears from the trajectory after exact Fisher calibration. -/
theorem fisherQubitClock_informational_trajectory (logFrequency phase : ℝ) :
    (fun s => fisherQubitClockState (Real.exp logFrequency) phase (s / Real.exp logFrequency)) =
      fisherQubitClockState 1 phase := by
  funext s
  unfold fisherQubitClockState
  congr 1
  field_simp

/-- Schrödinger evolution expressed in the accumulated informational parameter. -/
theorem fisherQubitClock_informational_schrodinger (logFrequency phase s : ℝ) :
    Complex.I • deriv
      (fun l => fisherQubitClockState (Real.exp logFrequency) phase (l / Real.exp logFrequency)) s =
      fisherQubitHamiltonianAction 1
        (fisherQubitClockState (Real.exp logFrequency) phase (s / Real.exp logFrequency)) := by
  have he := fisherQubitClock_informational_trajectory logFrequency phase
  rw [he, congrFun he s]
  exact fisherQubitClock_schrodinger 1 phase s

end HTGeometry
