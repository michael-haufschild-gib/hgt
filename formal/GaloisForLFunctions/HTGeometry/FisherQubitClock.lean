import GaloisForLFunctions.HTGeometry.QuantumBilinearNullActivation

/-!
# Accumulated Fisher time of an actual qubit trajectory

The Fisher line element of arXiv:2605.03958, equations (14), (18), and (41),
applied to the corpus's normalized two-level state. The actual derivative,
integrated length, inverse calibration, and periodic ambiguity are proved for
all real frequencies, including the stationary and reversed-frequency cases.
-/

open scoped InnerProductSpace
noncomputable section
namespace HTGeometry

def fisherQubitClockState (frequency phase t : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  qgtQubitState (phase + frequency * t / 2)

def fisherQubitClockTangent (frequency phase t : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  qgtQubitTangent (phase + frequency * t / 2) (frequency / 2)

/-- Quantum Fisher information of the actual normalized state and its tangent. -/
def fisherQubitClockInformation (frequency phase t : ℝ) : ℝ :=
  pureStateQuantumFisherValue (‖fisherQubitClockState frequency phase t‖ ^ (2 : ℕ))
    ‖inner ℂ (fisherQubitClockState frequency phase t)
      (fisherQubitClockTangent frequency phase t)‖
    (‖fisherQubitClockTangent frequency phase t‖ ^ (2 : ℕ))

theorem fisherQubitClock_hasDerivAt (frequency phase t : ℝ) :
    HasDerivAt (fisherQubitClockState frequency phase)
      (fisherQubitClockTangent frequency phase t) t := by
  have hp : HasDerivAt (fun s : ℝ => phase + frequency * s / 2) (frequency / 2) t := by
    simpa using (((hasDerivAt_id t).const_mul frequency).div_const 2).const_add phase
  have hc := hp.cos.ofReal_comp
  have hs := hp.sin.ofReal_comp
  have hv : HasDerivAt
      (fun s : ℝ => ![(Real.cos (phase + frequency * s / 2) : ℂ),
        (Real.sin (phase + frequency * s / 2) : ℂ)])
      ![((-(frequency / 2) * Real.sin (phase + frequency * t / 2) : ℝ) : ℂ),
        ((frequency / 2 * Real.cos (phase + frequency * t / 2) : ℝ) : ℂ)] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hc.congr_deriv (by simp; ring)
    · exact hs.congr_deriv (by simp; ring)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hv

theorem fisherQubitClock_information (frequency phase t : ℝ) :
    fisherQubitClockInformation frequency phase t = frequency ^ (2 : ℕ) := by
  unfold fisherQubitClockInformation fisherQubitClockState fisherQubitClockTangent
  rw [qgtQubit_fisher]
  ring

/-- The nonnegative distinguishability rate retains the absolute value of frequency. -/
theorem fisherQubitClock_speed (frequency phase t : ℝ) :
    Real.sqrt (fisherQubitClockInformation frequency phase t) = |frequency| := by
  rw [fisherQubitClock_information, Real.sqrt_sq_eq_abs]

/-- The oriented integral records causal orientation separately from nonnegative speed. -/
theorem fisherQubitClock_integral (frequency phase a b : ℝ) :
    (∫ t : ℝ in a..b, Real.sqrt (fisherQubitClockInformation frequency phase t)) =
      |frequency| * (b - a) := by
  simp only [fisherQubitClock_speed, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem fisherQubitClock_length (frequency phase a b : ℝ) :
    |∫ t : ℝ in a..b, Real.sqrt (fisherQubitClockInformation frequency phase t)| =
      |frequency| * |b - a| := by
  rw [fisherQubitClock_integral, abs_mul, abs_abs]

/-- Positive calibration supplies a closed inverse, with no nonzero-frequency premise. -/
theorem fisherQubitClock_calibration (logFrequency phase t : ℝ) :
    (∫ s : ℝ in 0..t,
      Real.sqrt (fisherQubitClockInformation (Real.exp logFrequency) phase s)) /
        Real.exp logFrequency = t := by
  rw [fisherQubitClock_integral, abs_of_pos (Real.exp_pos _), sub_zero]
  field_simp

theorem fisherQubitClock_zero_information_iff (frequency phase t : ℝ) :
    fisherQubitClockInformation frequency phase t = 0 ↔ frequency = 0 := by
  rw [fisherQubitClock_information, sq_eq_zero_iff]

/-- Exact finite overlap along the trajectory; accumulated length and endpoint overlap differ. -/
theorem fisherQubitClock_overlap (frequency phase a b : ℝ) :
    inner ℂ (fisherQubitClockState frequency phase a)
      (fisherQubitClockState frequency phase b) =
      (Real.cos (frequency * (b - a) / 2) : ℂ) := by
  unfold fisherQubitClockState qgtQubitState
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    RCLike.inner_apply, Complex.conj_ofReal]
  have h := Real.cos_sub (phase + frequency * b / 2) (phase + frequency * a / 2)
  have he : phase + frequency * b / 2 - (phase + frequency * a / 2) =
      frequency * (b - a) / 2 := by ring
  rw [he] at h
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  exact congrArg Complex.ofReal h.symm

/-- Every complete state cycle returns exactly, while Fisher time retains the cycle count. -/
theorem fisherQubitClock_cycle (logFrequency phase : ℝ) (n : ℕ) :
    fisherQubitClockState (Real.exp logFrequency) phase
        (4 * Real.pi * n / Real.exp logFrequency) =
      fisherQubitClockState (Real.exp logFrequency) phase 0 ∧
    (∫ t : ℝ in 0..(4 * Real.pi * n / Real.exp logFrequency),
      Real.sqrt (fisherQubitClockInformation (Real.exp logFrequency) phase t)) =
        4 * Real.pi * n := by
  constructor
  · have he : phase + Real.exp logFrequency *
        (4 * Real.pi * n / Real.exp logFrequency) / 2 = phase + n * (2 * Real.pi) := by
      field_simp
      ring
    simp [fisherQubitClockState, he, qgtQubitState,
      Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
  · rw [fisherQubitClock_integral, abs_of_pos (Real.exp_pos _), sub_zero]
    field_simp

/-- A positive Fisher rate does not make a periodic state an injective clock reading. -/
theorem fisherQubitClock_not_injective (logFrequency phase : ℝ) :
    ¬ Function.Injective (fisherQubitClockState (Real.exp logFrequency) phase) := by
  intro h
  have he := h (fisherQubitClock_cycle logFrequency phase 1).1
  have hp : 0 < 4 * Real.pi * (1 : ℕ) / Real.exp logFrequency := by
    positivity
  linarith

end HTGeometry
