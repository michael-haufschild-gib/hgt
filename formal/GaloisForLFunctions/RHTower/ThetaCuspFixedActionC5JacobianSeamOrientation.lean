import GaloisForLFunctions.HTGeometry.PolynomialODEJetC5FixedActionSeamClosure
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureSixthSeamChamber
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthModularSeam
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthBellTransfer
import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5Jacobian
import GaloisForLFunctions.RHTower.ThetaCuspActionVelocitySeamLogMinorNoGo

/-!
# Direct fixed-action C5 orientation at the theta self-dual seam

The direct fixed-action C5 Jacobian has a cancellation absent from the previously obstructed
action-velocity transport.  Its first deciding self-dual displacement coefficient is the log-jet
polynomial

`A^2 D - 5 A B C + 4 B^3 - 18 A^3 C + 36 A^2 B^2`,

where `A=-L₂(0)`, `B=-L₄(0)`, `C=-L₆(0)`, and `D=-L₈(0)` for the completed theta-source
logarithm.  This file proves that coefficient strictly positive for the literal theta cusp by
transporting the source-positive modular ODE seam closure through the exact Bell transform.
-/

open Complex Real
open scoped BigOperators ContDiff

namespace RHTower

noncomputable section

/-- Literal source-positive theta state at the modular center is the algebraic seam state. -/
theorem thetaCuspModularSourcePositiveState_zero_eq_seam :
    (fun i => thetaCuspModularSourcePositiveState i 0) =
      HTGeometry.modularThetaSourcePositiveSeamState
        (thetaCuspSelfDualModularScale ^ 2) := by
  funext i
  cases i with
  | U =>
      simp [thetaCuspModularSourcePositiveState,
        thetaCuspModularQuasimodularDrift,
        thetaCuspModularTransverseShear,
        thetaCuspModularDrift_re_zero,
        thetaCuspModularODEState_Z_zero,
        HTGeometry.modularThetaSourcePositiveSeamState]
  | B =>
      simp [thetaCuspModularSourcePositiveState,
        thetaCuspModularDrift_re_zero,
        HTGeometry.modularThetaSourcePositiveSeamState]
  | Q =>
      simp [thetaCuspModularSourcePositiveState,
        thetaCuspModularDrift_re_zero,
        thetaCuspModularGapAmplitude_zero,
        HTGeometry.modularThetaSourcePositiveSeamState]

/-- Complex raw-source form of the direct fixed-action C5 seam coefficient. -/
def thetaCuspC5FixedActionSeamSourceValueC : ℂ :=
  let f : ℕ → ℂ := fun n =>
    iteratedDeriv n (fun x : ℝ => (thetaCuspFullSource x : ℂ)) 0
  let a := -f 2
  let b := 3 * f 2 ^ 2 - f 0 * f 4
  let c := -f 0 ^ 2 * f 6 + 15 * f 0 * f 2 * f 4 - 30 * f 2 ^ 3
  let d := -f 0 ^ 3 * f 8 + 28 * f 0 ^ 2 * f 2 * f 6 +
    35 * f 0 ^ 2 * f 4 ^ 2 - 420 * f 0 * f 2 ^ 2 * f 4 + 630 * f 2 ^ 4
  a ^ 2 * d - 5 * a * b * c + 4 * b ^ 3 - 18 * a ^ 3 * c +
    36 * a ^ 2 * b ^ 2

/-- Real raw-source form of the same seam coefficient. -/
def thetaCuspC5FixedActionSeamSourceValue : ℝ :=
  let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource 0
  let a := -f 2
  let b := 3 * f 2 ^ 2 - f 0 * f 4
  let c := -f 0 ^ 2 * f 6 + 15 * f 0 * f 2 * f 4 - 30 * f 2 ^ 3
  let d := -f 0 ^ 3 * f 8 + 28 * f 0 ^ 2 * f 2 * f 6 +
    35 * f 0 ^ 2 * f 4 ^ 2 - 420 * f 0 * f 2 ^ 2 * f 4 + 630 * f 2 ^ 4
  a ^ 2 * d - 5 * a * b * c + 4 * b ^ 3 - 18 * a ^ 3 * c +
    36 * a ^ 2 * b ^ 2

/-- Logarithmic direct fixed-action C5 seam coefficient. -/
def thetaCuspC5FixedActionSeamLogValue : ℝ :=
  let a := -iteratedDeriv 2 thetaCuspLogSource 0
  let b := -iteratedDeriv 4 thetaCuspLogSource 0
  let c := -iteratedDeriv 6 thetaCuspLogSource 0
  let d := -iteratedDeriv 8 thetaCuspLogSource 0
  a ^ 2 * d - 5 * a * b * c + 4 * b ^ 3 - 18 * a ^ 3 * c +
    36 * a ^ 2 * b ^ 2

/-- Complex and real degree-twelve modular seam polynomials agree under real embedding. -/
theorem ofReal_modularThetaC5FixedActionSeamPolynomialReal (X : ℝ) :
    (HTGeometry.modularThetaC5FixedActionSeamPolynomialReal X : ℂ) =
      HTGeometry.modularThetaC5FixedActionSeamPolynomial (X : ℂ) := by
  unfold HTGeometry.modularThetaC5FixedActionSeamPolynomialReal
    HTGeometry.modularThetaC5FixedActionSeamPolynomial
  push_cast
  ring

/-- Exact modular-ODE evaluation of the literal theta raw-source coefficient. -/
theorem thetaCuspC5FixedActionSeamSourceValueC_eq_modularPolynomial :
    thetaCuspC5FixedActionSeamSourceValueC =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H 0 ^ 6 *
        HTGeometry.modularThetaC5FixedActionSeamPolynomial
          ((thetaCuspSelfDualModularScale : ℂ) ^ 2) := by
  let H : ℝ → ℂ :=
    thetaCuspModularODEState HTGeometry.ModularThetaODEState.H
  let F : ℝ → ℂ := fun x => (thetaCuspFullSource x : ℂ)
  have hF : ∀ x, F x = H x *
      thetaCuspModularSourcePositiveState
        HTGeometry.ModularThetaSourcePositiveState.Q x := by
    intro x
    exact ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ x
  have hclosure :=
    HTGeometry.modularThetaSourcePositiveC5FixedActionClosure_of_ode
      thetaCuspModularSourcePositiveState
      hasDerivAt_thetaCuspModularSourcePositiveState H F
      hasDerivAt_thetaCuspModularMass_sourcePositive hF 0
  dsimp only at hclosure
  rw [thetaCuspModularSourcePositiveState_zero_eq_seam,
    HTGeometry.eval_modularThetaSourcePositiveC5FixedActionSeamPolynomial_seam]
    at hclosure
  simpa [thetaCuspC5FixedActionSeamSourceValueC, H, F] using hclosure

/-- The literal direct fixed-action raw-source seam coefficient is strictly positive. -/
theorem thetaCuspC5FixedActionSeamSourceValueC_re_pos :
    0 < thetaCuspC5FixedActionSeamSourceValueC.re := by
  have hpoly : 0 < HTGeometry.modularThetaC5FixedActionSeamPolynomialReal
      (thetaCuspSelfDualModularScale ^ 2) :=
    HTGeometry.modularThetaC5FixedActionSeamPolynomialReal_pos_of_mem_physicalChamber
      (le_of_lt thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one)
      thetaCuspSelfDualModularScale_sq_lt_twenty
  have hpolyC :
      HTGeometry.modularThetaC5FixedActionSeamPolynomial
          ((thetaCuspSelfDualModularScale : ℂ) ^ 2) =
        (HTGeometry.modularThetaC5FixedActionSeamPolynomialReal
          (thetaCuspSelfDualModularScale ^ 2) : ℂ) := by
    rw [← Complex.ofReal_pow]
    exact (ofReal_modularThetaC5FixedActionSeamPolynomialReal _).symm
  rw [thetaCuspC5FixedActionSeamSourceValueC_eq_modularPolynomial,
    thetaCuspModularODEState_H_eq_completedThetaProfile, hpolyC]
  simpa [pow_succ, Complex.mul_re] using
    mul_pos (pow_pos (thetaCuspCompletedThetaProfile_pos 0) 6) hpoly

/-- Complex raw-source value is exactly the embedding of its real form. -/
theorem thetaCuspC5FixedActionSeamSourceValueC_eq_ofReal :
    thetaCuspC5FixedActionSeamSourceValueC =
      (thetaCuspC5FixedActionSeamSourceValue : ℂ) := by
  unfold thetaCuspC5FixedActionSeamSourceValueC
    thetaCuspC5FixedActionSeamSourceValue
  simp_rw [SchwartzMap.iteratedDeriv_ofReal thetaCuspFullSource
    contDiff_thetaCuspFullSource]
  push_cast
  rfl

/-- Real raw-source seam coefficient is strictly positive. -/
theorem thetaCuspC5FixedActionSeamSourceValue_pos :
    0 < thetaCuspC5FixedActionSeamSourceValue := by
  have h := thetaCuspC5FixedActionSeamSourceValueC_re_pos
  rw [thetaCuspC5FixedActionSeamSourceValueC_eq_ofReal] at h
  simpa using h

/-- Exact Bell cancellation from raw source jets to the direct fixed-action log coefficient. -/
theorem thetaCuspC5FixedActionSeamSourceValue_eq_logValue :
    thetaCuspC5FixedActionSeamSourceValue =
      thetaCuspFullSource 0 ^ 6 * thetaCuspC5FixedActionSeamLogValue := by
  have h1 := iteratedDeriv_thetaCuspLogSource_zero_of_odd
    (show Odd 1 by norm_num)
  have h3 := iteratedDeriv_thetaCuspLogSource_zero_of_odd
    (show Odd 3 by norm_num)
  have h5 := iteratedDeriv_thetaCuspLogSource_zero_of_odd
    (show Odd 5 by norm_num)
  have h7 := iteratedDeriv_thetaCuspLogSource_zero_of_odd
    (show Odd 7 by norm_num)
  have hexp : Real.exp (thetaCuspLogSource 0) = thetaCuspFullSource 0 := by
    rw [thetaCuspLogSource, Real.exp_log (thetaCuspFullSource_pos_all 0)]
  unfold thetaCuspC5FixedActionSeamSourceValue
    thetaCuspC5FixedActionSeamLogValue
  dsimp only
  rw [iteratedDeriv_zero,
    iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_six_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_eight_thetaCuspFullSource_eq_logExponentialJet]
  unfold thetaCuspLogExponentialJetTwo thetaCuspLogExponentialJetFour
    thetaCuspLogExponentialJetSix thetaCuspLogExponentialJetEight
    thetaCuspLogExponentialJetZero
  rw [hexp, h1, h3, h5, h7]
  ring

/-- Unconditional strict orientation of the first deciding direct fixed-action C5 seam term. -/
theorem thetaCuspC5FixedActionSeamLogValue_pos :
    0 < thetaCuspC5FixedActionSeamLogValue := by
  have hraw := thetaCuspC5FixedActionSeamSourceValue_pos
  rw [thetaCuspC5FixedActionSeamSourceValue_eq_logValue] at hraw
  exact pos_of_mul_pos_right hraw
    (pow_nonneg (le_of_lt (thetaCuspFullSource_pos_all 0)) 6)

/-- Sharp seam classification: velocity-only fixed-action transport has reverse orientation,
while the first deciding coefficient of the direct C5 Jacobian has strict forward orientation. -/
theorem thetaCuspC5FixedAction_direct_survives_velocity_seam_noGo :
    thetaCuspActionVelocitySeamLogMinor < 0 ∧
      0 < thetaCuspC5FixedActionSeamLogValue :=
  ⟨thetaCuspActionVelocitySeamLogMinor_neg,
    thetaCuspC5FixedActionSeamLogValue_pos⟩

end

end RHTower
