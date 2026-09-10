import GaloisForLFunctions.HTGeometry.QuantumBilinearNullActivation

/-!
# Measurement-realized Fisher speed for the two-level clock

The measurement dependence distinguished in arXiv:2605.03958, §5.1, is
explicit for every real projective qubit measurement. The classical Fisher
value is bounded by quantum Fisher information and an adapted orthogonal
basis attains that bound. At zero-probability outcomes the totalized discrete
Fisher expression has a sharp singular boundary.
-/
open scoped BigOperators InnerProductSpace
noncomputable section
namespace HTGeometry

/-- Born probabilities in a real orthonormal measurement frame. -/
def qubitClockBornProbability (angle : ℝ) : Fin 2 → ℝ :=
  ![Real.cos angle ^ 2, Real.sin angle ^ 2]

/-- Derivatives of the Born probabilities at angular velocity `v`. -/
def qubitClockBornVelocity (angle v : ℝ) : Fin 2 → ℝ :=
  ![-2 * v * Real.sin angle * Real.cos angle, 2 * v * Real.sin angle * Real.cos angle]

/-- Classical discrete Fisher value, with Lean's zero-denominator convention at empty outcomes. -/
def qubitClockClassicalFisher (angle v : ℝ) : ℝ :=
  ∑ i, qubitClockBornVelocity angle v i ^ 2 / qubitClockBornProbability angle i

theorem qubitClockBornProbability_sum (angle : ℝ) :
    ∑ i, qubitClockBornProbability angle i = 1 := by
  simp only [qubitClockBornProbability, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact Real.cos_sq_add_sin_sq angle

/-- Differentiation uses a fixed measurement frame as the physical state moves. -/
theorem qubitClockBorn_hasDerivAt (angle v : ℝ) (i : Fin 2) :
    HasDerivAt (fun t : ℝ => qubitClockBornProbability (angle + v * t) i)
      (qubitClockBornVelocity angle v i) 0 := by
  have hp : HasDerivAt (fun t : ℝ => angle + v * t) v 0 := by
    simpa using ((hasDerivAt_id 0).const_mul v).const_add angle
  fin_cases i
  · have h := hp.cos.pow 2
    apply h.congr_deriv
    change 2 * Real.cos (angle + v * 0) ^ (2 - 1) *
      (-Real.sin (angle + v * 0) * v) = -2 * v * Real.sin angle * Real.cos angle
    simp
    ring
  · have h := hp.sin.pow 2
    apply h.congr_deriv
    change 2 * Real.sin (angle + v * 0) ^ (2 - 1) *
      (Real.cos (angle + v * 0) * v) = 2 * v * Real.sin angle * Real.cos angle
    simp
    ring

/-- Exact classification, including the singular measurement frames. -/
theorem qubitClockClassicalFisher_formula (angle v : ℝ) :
    qubitClockClassicalFisher angle v =
      if Real.sin angle = 0 ∨ Real.cos angle = 0 then 0 else 4 * v ^ 2 := by
  unfold qubitClockClassicalFisher qubitClockBornVelocity qubitClockBornProbability
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hs : Real.sin angle = 0
  · simp [hs]
  by_cases hc : Real.cos angle = 0
  · simp [hc]
  simp only [hs, hc, or_self, ite_false]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq angle,
    congrArg (fun z : ℝ => 4 * v ^ 2 * Real.sin angle ^ 2 * Real.cos angle ^ 2 * z)
      (Real.sin_sq_add_cos_sq angle)]

/-- Every measurement frame has at most the source's quantum Fisher information. -/
theorem qubitClockClassicalFisher_le_quantum (stateAngle measurementAngle v : ℝ) :
    qubitClockClassicalFisher (stateAngle - measurementAngle) v ≤
      pureStateQuantumFisherValue (‖qgtQubitState stateAngle‖ ^ 2)
        ‖inner ℂ (qgtQubitState stateAngle) (qgtQubitTangent stateAngle v)‖
        (‖qgtQubitTangent stateAngle v‖ ^ 2) := by
  rw [qgtQubit_fisher, qubitClockClassicalFisher_formula]
  split
  · positivity
  · exact le_rfl

/-- A frame offset by `π/4` from the state direction attains quantum Fisher information. -/
theorem qubitClockClassicalFisher_optimal (stateAngle v : ℝ) :
    qubitClockClassicalFisher (stateAngle - (stateAngle - Real.pi / 4)) v =
      pureStateQuantumFisherValue (‖qgtQubitState stateAngle‖ ^ 2)
        ‖inner ℂ (qgtQubitState stateAngle) (qgtQubitTangent stateAngle v)‖
        (‖qgtQubitTangent stateAngle v‖ ^ 2) := by
  rw [show stateAngle - (stateAngle - Real.pi / 4) = Real.pi / 4 by ring,
    qgtQubit_fisher, qubitClockClassicalFisher_formula,
    Real.sin_pi_div_four, Real.cos_pi_div_four]
  have h : Real.sqrt 2 / 2 ≠ 0 := by positivity
  simp [h]

/-- An aligned measurement has zero totalized classical Fisher value despite nonzero source motion. -/
theorem qubitClockClassicalFisher_aligned (v : ℝ) :
    qubitClockClassicalFisher 0 v = 0 := by
  simp [qubitClockClassicalFisher_formula]

end HTGeometry
