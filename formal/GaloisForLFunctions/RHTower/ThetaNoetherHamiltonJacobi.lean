import GaloisForLFunctions.RHTower.ThetaNoetherExchangeSign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# A conservative mechanical action from the arithmetic current

The actual prime current supplies positive kinetic energy. Its exact
Gamma/pole exchange is the derivative of a potential with a unique
minimum. Taking the positive square root of twice the current constructs
a global Hamilton--Jacobi action at the conserved arithmetic energy.
The corresponding mechanical Lagrangian has exact time-translation
symmetry. No equation of motion is assumed in these identities.
-/

noncomputable section

open MeasureTheory Filter Set

namespace RHTower.ThetaSourceWard

def thetaNoetherCurrentReal (x : ℝ) : ℝ :=
  (fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x).re

def thetaNoetherForce (x : ℝ) : ℝ := (thetaNoetherExchange x).re

def thetaNoetherPotential (x : ℝ) : ℝ := thetaNoetherCurrentReal 0 - thetaNoetherCurrentReal x

def thetaNoetherSpeed (x : ℝ) : ℝ := Real.sqrt (2 * thetaNoetherCurrentReal x)

theorem thetaNoetherCurrentReal_pos (x : ℝ) : 0 < thetaNoetherCurrentReal x :=
  fullPrimeShiftNoetherCurrent_re_pos thetaCuspTiltSource thetaCuspTiltSource x

theorem thetaNoetherCurrentReal_le_center (x : ℝ) :
    thetaNoetherCurrentReal x ≤ thetaNoetherCurrentReal 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact le_rfl
  · exact ((thetaNoetherCurrent_re_lt_center_iff x).mpr hx).le

theorem hasDerivAt_thetaNoetherCurrentReal (x : ℝ) :
    HasDerivAt thetaNoetherCurrentReal (-thetaNoetherForce x) x := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x)
  convert! h using 1
  simp [thetaNoetherForce, thetaNoetherExchange_eq]

theorem continuous_thetaNoetherCurrentReal : Continuous thetaNoetherCurrentReal :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_thetaNoetherCurrentReal x).continuousAt

theorem hasDerivAt_thetaNoetherPotential (x : ℝ) :
    HasDerivAt thetaNoetherPotential (thetaNoetherForce x) x := by
  convert! (hasDerivAt_thetaNoetherCurrentReal x).const_sub (thetaNoetherCurrentReal 0) using 1
  simp

theorem thetaNoetherPotential_zero : thetaNoetherPotential 0 = 0 := sub_self _

theorem thetaNoetherPotential_nonneg (x : ℝ) : 0 ≤ thetaNoetherPotential x :=
  sub_nonneg.mpr (thetaNoetherCurrentReal_le_center x)

theorem thetaNoetherPotential_pos_iff (x : ℝ) : 0 < thetaNoetherPotential x ↔ x ≠ 0 := by
  exact sub_pos.trans (thetaNoetherCurrent_re_lt_center_iff x)

theorem thetaNoetherPotential_lt_ceiling (x : ℝ) :
    thetaNoetherPotential x < thetaNoetherCurrentReal 0 :=
  sub_lt_self _ (thetaNoetherCurrentReal_pos x)

theorem thetaNoetherSpeed_pos (x : ℝ) : 0 < thetaNoetherSpeed x :=
  Real.sqrt_pos.mpr (mul_pos zero_lt_two (thetaNoetherCurrentReal_pos x))

theorem thetaNoetherSpeed_sq (x : ℝ) :
    thetaNoetherSpeed x ^ 2 = 2 * thetaNoetherCurrentReal x :=
  Real.sq_sqrt (mul_nonneg zero_le_two (thetaNoetherCurrentReal_pos x).le)

theorem continuous_thetaNoetherSpeed : Continuous thetaNoetherSpeed :=
  Real.continuous_sqrt.comp (continuous_const.mul continuous_thetaNoetherCurrentReal)

theorem thetaNoetherSpeed_le_center (x : ℝ) : thetaNoetherSpeed x ≤ thetaNoetherSpeed 0 :=
  Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (thetaNoetherCurrentReal_le_center x) zero_le_two)

theorem hasDerivAt_thetaNoetherSpeed (x : ℝ) :
    HasDerivAt thetaNoetherSpeed (-thetaNoetherForce x / thetaNoetherSpeed x) x := by
  have h := ((hasDerivAt_thetaNoetherCurrentReal x).const_mul 2).sqrt
    (ne_of_gt (mul_pos zero_lt_two (thetaNoetherCurrentReal_pos x)))
  convert! h using 1
  dsimp only [thetaNoetherSpeed]
  ring

/-- The current square root is a velocity field for the conservative arithmetic force. -/
theorem thetaNoetherSpeed_mul_deriv (x : ℝ) :
    thetaNoetherSpeed x * deriv thetaNoetherSpeed x = -thetaNoetherForce x := by
  rw [(hasDerivAt_thetaNoetherSpeed x).deriv]
  have hv := (thetaNoetherSpeed_pos x).ne'
  field_simp

def thetaNoetherHamiltonJacobiAction (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, thetaNoetherSpeed y

theorem hasDerivAt_thetaNoetherHamiltonJacobiAction (x : ℝ) :
    HasDerivAt thetaNoetherHamiltonJacobiAction (thetaNoetherSpeed x) x :=
  intervalIntegral.integral_hasDerivAt_right (continuous_thetaNoetherSpeed.intervalIntegrable 0 x)
    continuous_thetaNoetherSpeed.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_thetaNoetherSpeed.continuousAt

def thetaNoetherMechanicalLagrangian (x v : ℝ) : ℝ := v ^ 2 / 2 - thetaNoetherPotential x

def thetaNoetherMechanicalEnergy (x v : ℝ) : ℝ := v ^ 2 / 2 + thetaNoetherPotential x

theorem hasDerivAt_thetaNoetherLagrangian_velocity (x v : ℝ) :
    HasDerivAt (thetaNoetherMechanicalLagrangian x) v v := by
  convert! (((hasDerivAt_id v).pow 2).div_const 2).sub_const (thetaNoetherPotential x) using 1
  simp

theorem hasDerivAt_thetaNoetherLagrangian_position (x v : ℝ) :
    HasDerivAt (fun y => thetaNoetherMechanicalLagrangian y v) (-thetaNoetherForce x) x :=
  (hasDerivAt_thetaNoetherPotential x).const_sub (v ^ 2 / 2)

/-- The time-translation Noether charge is the mechanical energy. -/
theorem thetaNoetherMechanical_noether_charge (x v : ℝ) :
    v * deriv (thetaNoetherMechanicalLagrangian x) v - thetaNoetherMechanicalLagrangian x v =
      thetaNoetherMechanicalEnergy x v := by
  rw [(hasDerivAt_thetaNoetherLagrangian_velocity x v).deriv]
  unfold thetaNoetherMechanicalLagrangian thetaNoetherMechanicalEnergy
  ring

/-- The arithmetic current gives a global, unconditional Hamilton--Jacobi solution. -/
theorem thetaNoetherHamiltonJacobi_energy (x : ℝ) :
    thetaNoetherMechanicalEnergy x (deriv thetaNoetherHamiltonJacobiAction x) =
      thetaNoetherCurrentReal 0 := by
  rw [(hasDerivAt_thetaNoetherHamiltonJacobiAction x).deriv]
  unfold thetaNoetherMechanicalEnergy thetaNoetherPotential
  rw [thetaNoetherSpeed_sq]
  ring

def thetaNoetherMechanicalAction (q : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, thetaNoetherMechanicalLagrangian (q t) (deriv q t)

/-- Exact action symmetry under translating both the trajectory and time endpoints. -/
theorem thetaNoetherMechanicalAction_time_translation (q : ℝ → ℝ) (a b c : ℝ) :
    thetaNoetherMechanicalAction (fun t => q (t + c)) a b =
      thetaNoetherMechanicalAction q (a + c) (b + c) := by
  simp only [thetaNoetherMechanicalAction, deriv_comp_add_const]
  exact intervalIntegral.integral_comp_add_right
    (fun t => thetaNoetherMechanicalLagrangian (q t) (deriv q t)) c

end RHTower.ThetaSourceWard
