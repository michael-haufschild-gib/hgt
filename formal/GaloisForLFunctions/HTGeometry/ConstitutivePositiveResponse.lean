import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Constitutive positive-response coframes

This module formalizes an unconditional native theorem of Constitutive Process Mathematics.
The passive positive doctrine `z ↦ Complex.normSq z` identifies opposite complex laws.  A fixed
additive intervention has a first response which descends through that doctrine exactly when the
intervention is zero, while the two marked responses in the real and imaginary directions recover
the complete complex law.

The response is defined algebraically.  Consequently the theorem has no differentiability,
nonvanishing, choice, convergence, or external source hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ComplexConjugate

/-- Passive positive observation of a complex constitutive law. -/
def constitutivePositiveDoctrine (z : ℂ) : ℝ :=
  Complex.normSq z

/-- Algebraic first response of positivity to the fixed additive intervention `h`. -/
def constitutiveAdditiveResponse (h z : ℂ) : ℝ :=
  2 * (conj z * h).re

/-- The two marked responses in the real and imaginary intervention directions. -/
def constitutiveResponseCoframe (z : ℂ) : ℝ × ℝ :=
  (constitutiveAdditiveResponse 1 z, constitutiveAdditiveResponse Complex.I z)

/-- Basepoint-zero real lift of the phase history. -/
def constitutivePhaseHistoryLift (t : ℝ) : ℝ :=
  t

/-- Positivity identifies a law with its opposite. -/
theorem constitutivePositiveDoctrine_neg (z : ℂ) :
    constitutivePositiveDoctrine (-z) = constitutivePositiveDoctrine z := by
  simp [constitutivePositiveDoctrine, Complex.normSq]

/-- A fixed additive response changes sign on the positive fibre `{z, -z}`. -/
theorem constitutiveAdditiveResponse_neg (h z : ℂ) :
    constitutiveAdditiveResponse h (-z) = -constitutiveAdditiveResponse h z := by
  simp [constitutiveAdditiveResponse, Complex.mul_re]
  ring

/-- Self-response is twice the positive norm square. -/
theorem constitutiveAdditiveResponse_self (h : ℂ) :
    constitutiveAdditiveResponse h h = 2 * Complex.normSq h := by
  simp [constitutiveAdditiveResponse, Complex.normSq_apply, Complex.mul_re]

/-- Exact second-order intervention expansion. -/
theorem constitutivePositiveDoctrine_add_intervention (h z : ℂ) (ε : ℝ) :
    constitutivePositiveDoctrine (z + (ε : ℂ) * h) =
      constitutivePositiveDoctrine z + ε * constitutiveAdditiveResponse h z +
        ε ^ (2 : ℕ) * constitutivePositiveDoctrine h := by
  simp [constitutivePositiveDoctrine, constitutiveAdditiveResponse, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

/-- The algebraic response is the actual real derivative of the positive doctrine along the
additive intervention. -/
theorem constitutivePositiveDoctrine_hasDerivAt_intervention (h z : ℂ) :
    HasDerivAt (fun ε : ℝ ↦ constitutivePositiveDoctrine (z + (ε : ℂ) * h))
      (constitutiveAdditiveResponse h z) 0 := by
  have hfun :
      (fun ε : ℝ ↦ constitutivePositiveDoctrine (z + (ε : ℂ) * h)) =
        fun ε : ℝ ↦ constitutivePositiveDoctrine z +
          ε * constitutiveAdditiveResponse h z + ε ^ (2 : ℕ) * constitutivePositiveDoctrine h := by
    funext ε
    exact constitutivePositiveDoctrine_add_intervention h z ε
  rw [hfun]
  convert! ((hasDerivAt_const (0 : ℝ) (constitutivePositiveDoctrine z)).add
      ((hasDerivAt_id 0).mul_const (constitutiveAdditiveResponse h z))).add
        (((hasDerivAt_id 0).pow 2).mul_const (constitutivePositiveDoctrine h)) using 1
  all_goals norm_num

/-- **Exact nondescendence classification.** A fixed additive response factors through passive
positivity on every complex law if and only if the intervention is zero.  The statement is closed:
the factorization function is existentially quantified rather than assumed. -/
theorem constitutiveAdditiveResponse_factors_iff_zero :
    ∀ h : ℂ,
      (∃ r : ℝ → ℝ, ∀ z : ℂ,
          constitutiveAdditiveResponse h z = r (constitutivePositiveDoctrine z)) ↔ h = 0 := by
  intro h
  constructor
  · rintro ⟨r, hr⟩
    have hsame : constitutiveAdditiveResponse h h = constitutiveAdditiveResponse h (-h) := by
      rw [hr h, hr (-h), constitutivePositiveDoctrine_neg]
    have hzero : constitutiveAdditiveResponse h h = 0 := by
      rw [constitutiveAdditiveResponse_neg] at hsame
      linarith
    rw [constitutiveAdditiveResponse_self] at hzero
    have : Complex.normSq h = 0 := by linarith
    exact Complex.normSq_eq_zero.mp this
  · rintro rfl
    refine ⟨fun _ ↦ 0, ?_⟩
    intro z
    simp [constitutiveAdditiveResponse]

/-- The response coframe is exactly twice the Cartesian coordinate map. -/
theorem constitutiveResponseCoframe_eq_coordinates (z : ℂ) :
    constitutiveResponseCoframe z = (2 * z.re, 2 * z.im) := by
  simp [constitutiveResponseCoframe, constitutiveAdditiveResponse, Complex.mul_re]

/-- **Response tomography.** Although passive positivity erases phase, the fixed two-response
coframe is faithful on the entire complex law space. -/
theorem constitutiveResponseCoframe_injective :
    Function.Injective constitutiveResponseCoframe := by
  intro z w hzw
  rw [constitutiveResponseCoframe_eq_coordinates,
    constitutiveResponseCoframe_eq_coordinates] at hzw
  have hre : z.re = w.re := by linarith [congrArg Prod.fst hzw]
  have him : z.im = w.im := by linarith [congrArg Prod.snd hzw]
  exact Complex.ext hre him

/-- Passive observation is constant on the unit phase orbit. -/
theorem constitutivePositiveDoctrine_unit_phase (t : ℝ) :
    constitutivePositiveDoctrine (Complex.exp (t * Complex.I)) = 1 := by
  rw [constitutivePositiveDoctrine, Complex.normSq_apply]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.cos_sq_add_sin_sq t]

/-- The marked response orbit is exactly the doubled unit circle. -/
theorem constitutiveResponseCoframe_unit_phase (t : ℝ) :
    constitutiveResponseCoframe (Complex.exp (t * Complex.I)) =
      (2 * Real.cos t, 2 * Real.sin t) := by
  rw [constitutiveResponseCoframe_eq_coordinates]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- The marked response on the phase orbit is recurrent with period `2π`. -/
theorem constitutiveResponseCoframe_unit_phase_periodic :
    Function.Periodic
      (fun t : ℝ ↦ constitutiveResponseCoframe (Complex.exp (t * Complex.I)))
      (2 * Real.pi) := by
  intro t
  change constitutiveResponseCoframe
      (Complex.exp (((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I)) =
    constitutiveResponseCoframe (Complex.exp ((t : ℂ) * Complex.I))
  rw [constitutiveResponseCoframe_unit_phase, constitutiveResponseCoframe_unit_phase,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- A closed observed response period advances the marked real history by `2π`. -/
theorem constitutivePhaseHistoryLift_period_increment (t : ℝ) :
    constitutivePhaseHistoryLift (t + 2 * Real.pi) =
      constitutivePhaseHistoryLift t + 2 * Real.pi := by
  rfl

/-- Every natural number of observed response periods closes exactly. -/
theorem constitutiveResponseCoframe_unit_phase_nperiods (N : ℕ) :
    Function.Periodic
      (fun t : ℝ ↦ constitutiveResponseCoframe (Complex.exp (t * Complex.I)))
      (N • (2 * Real.pi)) :=
  constitutiveResponseCoframe_unit_phase_periodic.nsmul N

/-- The same `N` closed response periods retain their full displacement in marked history. -/
theorem constitutivePhaseHistoryLift_nperiod_increment (N : ℕ) (t : ℝ) :
    constitutivePhaseHistoryLift (t + N • (2 * Real.pi)) =
      constitutivePhaseHistoryLift t + N • (2 * Real.pi) := by
  rfl

end GaloisForLFunctions.HTGeometry
