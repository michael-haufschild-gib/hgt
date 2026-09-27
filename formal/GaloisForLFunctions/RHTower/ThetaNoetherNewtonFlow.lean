import GaloisForLFunctions.RHTower.ThetaNoetherHamiltonJacobi
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.IntermediateValue

/-!
# A global Newton flow from the arithmetic conservation law

Integrating the reciprocal positive arithmetic speed gives an increasing
travel-time coordinate. Its derivative has a positive global lower bound,
so it is onto the real line. Its inverse is therefore an actual global
trajectory, with the literal arithmetic exchange as conservative force.
Time translations give a real flow on the conserved energy curve.

The Newton equation and conserved Noether charge are conclusions for this
constructed trajectory; they are not assumptions supplied to the proof.
-/

noncomputable section

open MeasureTheory Filter Set Topology

namespace RHTower.ThetaSourceWard

def thetaNoetherTravelTime (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, 1 / thetaNoetherSpeed y

theorem continuous_thetaNoetherInverseSpeed : Continuous (fun x => 1 / thetaNoetherSpeed x) :=
  continuous_const.div continuous_thetaNoetherSpeed (fun x => (thetaNoetherSpeed_pos x).ne')

theorem hasDerivAt_thetaNoetherTravelTime (x : ℝ) :
    HasDerivAt thetaNoetherTravelTime (1 / thetaNoetherSpeed x) x :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_thetaNoetherInverseSpeed.intervalIntegrable 0 x)
    continuous_thetaNoetherInverseSpeed.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_thetaNoetherInverseSpeed.continuousAt

theorem continuous_thetaNoetherTravelTime : Continuous thetaNoetherTravelTime :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_thetaNoetherTravelTime x).continuousAt

theorem thetaNoetherTravelTime_zero : thetaNoetherTravelTime 0 = 0 := by
  simp [thetaNoetherTravelTime]

theorem strictMono_thetaNoetherTravelTime : StrictMono thetaNoetherTravelTime := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_thetaNoetherTravelTime x).deriv]
  exact one_div_pos.mpr (thetaNoetherSpeed_pos x)

private theorem thetaNoetherTravelTime_drift_monotone :
    Monotone (fun x => thetaNoetherTravelTime x - (1 / thetaNoetherSpeed 0) * x) := by
  have hd (x : ℝ) : HasDerivAt
      (fun y => thetaNoetherTravelTime y - (1 / thetaNoetherSpeed 0) * y)
      (1 / thetaNoetherSpeed x - 1 / thetaNoetherSpeed 0) x := by
    convert! (hasDerivAt_thetaNoetherTravelTime x).sub
      ((hasDerivAt_id x).const_mul (1 / thetaNoetherSpeed 0)) using 1
    simp only [mul_one]
  apply monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
  intro x
  rw [(hd x).deriv]
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (thetaNoetherSpeed_pos x)
    (thetaNoetherSpeed_le_center x))

theorem tendsto_thetaNoetherTravelTime_atTop : Tendsto thetaNoetherTravelTime atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (f₁ := fun x : ℝ => (1 / thetaNoetherSpeed 0) * x)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have h := thetaNoetherTravelTime_drift_monotone hx
    simp only [thetaNoetherTravelTime_zero, mul_zero, sub_zero] at h
    linarith
  · exact (tendsto_const_mul_atTop_of_pos (one_div_pos.mpr (thetaNoetherSpeed_pos 0))).mpr tendsto_id

theorem tendsto_thetaNoetherTravelTime_atBot : Tendsto thetaNoetherTravelTime atBot atBot := by
  apply tendsto_atBot_mono' atBot
    (f₁ := fun x : ℝ => (1 / thetaNoetherSpeed 0) * x)
  · filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    have h := thetaNoetherTravelTime_drift_monotone hx
    simp only [thetaNoetherTravelTime_zero, mul_zero, sub_zero] at h
    linarith
  · exact (tendsto_const_mul_atBot_of_pos (one_div_pos.mpr (thetaNoetherSpeed_pos 0))).mpr tendsto_id

theorem surjective_thetaNoetherTravelTime : Function.Surjective thetaNoetherTravelTime :=
  continuous_thetaNoetherTravelTime.surjective
    tendsto_thetaNoetherTravelTime_atTop tendsto_thetaNoetherTravelTime_atBot

def thetaNoetherTravelIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective thetaNoetherTravelTime
    strictMono_thetaNoetherTravelTime surjective_thetaNoetherTravelTime

def thetaNoetherTrajectory (t : ℝ) : ℝ := thetaNoetherTravelIso.symm t

theorem thetaNoetherTravelTime_trajectory (t : ℝ) :
    thetaNoetherTravelTime (thetaNoetherTrajectory t) = t :=
  thetaNoetherTravelIso.apply_symm_apply t

theorem thetaNoetherTrajectory_travelTime (x : ℝ) :
    thetaNoetherTrajectory (thetaNoetherTravelTime x) = x :=
  thetaNoetherTravelIso.symm_apply_apply x

theorem thetaNoetherTrajectory_zero : thetaNoetherTrajectory 0 = 0 := by
  simpa only [thetaNoetherTravelTime_zero] using thetaNoetherTrajectory_travelTime 0

theorem continuous_thetaNoetherTrajectory : Continuous thetaNoetherTrajectory :=
  thetaNoetherTravelIso.symm.toHomeomorph.continuous

theorem hasDerivAt_thetaNoetherTrajectory (t : ℝ) :
    HasDerivAt thetaNoetherTrajectory (thetaNoetherSpeed (thetaNoetherTrajectory t)) t := by
  have h := HasDerivAt.of_local_left_inverse continuous_thetaNoetherTrajectory.continuousAt
    (hasDerivAt_thetaNoetherTravelTime (thetaNoetherTrajectory t))
    (one_div_ne_zero (thetaNoetherSpeed_pos _).ne')
    (Eventually.of_forall thetaNoetherTravelTime_trajectory)
  simpa only [one_div, inv_inv] using h

/-- The constructed trajectory has the actual arithmetic exchange as its acceleration. -/
theorem hasDerivAt_thetaNoetherTrajectory_velocity (t : ℝ) :
    HasDerivAt (deriv thetaNoetherTrajectory) (-thetaNoetherForce (thetaNoetherTrajectory t)) t := by
  have he : deriv thetaNoetherTrajectory = fun u => thetaNoetherSpeed (thetaNoetherTrajectory u) :=
    funext fun u => (hasDerivAt_thetaNoetherTrajectory u).deriv
  rw [he]
  have h := (hasDerivAt_thetaNoetherSpeed (thetaNoetherTrajectory t)).comp t
    (hasDerivAt_thetaNoetherTrajectory t)
  convert! h using 1
  have hv := (thetaNoetherSpeed_pos (thetaNoetherTrajectory t)).ne'
  field_simp

theorem thetaNoetherTrajectory_newton (t : ℝ) :
    deriv (deriv thetaNoetherTrajectory) t = -thetaNoetherForce (thetaNoetherTrajectory t) :=
  (hasDerivAt_thetaNoetherTrajectory_velocity t).deriv

theorem thetaNoetherTrajectory_energy (t : ℝ) :
    thetaNoetherMechanicalEnergy (thetaNoetherTrajectory t) (deriv thetaNoetherTrajectory t) =
      thetaNoetherCurrentReal 0 := by
  rw [(hasDerivAt_thetaNoetherTrajectory t).deriv]
  unfold thetaNoetherMechanicalEnergy thetaNoetherPotential
  rw [thetaNoetherSpeed_sq]
  ring

/-- Euler--Lagrange holds for the literal time-symmetric mechanical action. -/
theorem thetaNoetherTrajectory_euler_lagrange (t : ℝ) :
    deriv (fun u => deriv (thetaNoetherMechanicalLagrangian (thetaNoetherTrajectory u))
      (deriv thetaNoetherTrajectory u)) t =
      deriv (fun x => thetaNoetherMechanicalLagrangian x (deriv thetaNoetherTrajectory t))
        (thetaNoetherTrajectory t) := by
  simp only [(hasDerivAt_thetaNoetherLagrangian_velocity _ _).deriv,
    (hasDerivAt_thetaNoetherLagrangian_position _ _).deriv, thetaNoetherTrajectory_newton]

def thetaNoetherFlow (x t : ℝ) : ℝ := thetaNoetherTrajectory (t + thetaNoetherTravelTime x)

theorem thetaNoetherFlow_zero (x : ℝ) : thetaNoetherFlow x 0 = x := by
  simp only [thetaNoetherFlow, zero_add, thetaNoetherTrajectory_travelTime]

/-- Time translation gives a global real action on the conserved energy curve. -/
theorem thetaNoetherFlow_add (x s t : ℝ) :
    thetaNoetherFlow (thetaNoetherFlow x s) t = thetaNoetherFlow x (s + t) := by
  simp only [thetaNoetherFlow, thetaNoetherTravelTime_trajectory]
  congr 1
  ring

theorem hasDerivAt_thetaNoetherFlow (x t : ℝ) :
    HasDerivAt (thetaNoetherFlow x) (thetaNoetherSpeed (thetaNoetherFlow x t)) t := by
  convert! (hasDerivAt_thetaNoetherTrajectory (t + thetaNoetherTravelTime x)).comp t
    ((hasDerivAt_id t).add_const (thetaNoetherTravelTime x)) using 1
  simp only [mul_one, thetaNoetherFlow]

theorem thetaNoetherFlow_energy (x t : ℝ) :
    thetaNoetherMechanicalEnergy (thetaNoetherFlow x t) (deriv (thetaNoetherFlow x) t) =
      thetaNoetherCurrentReal 0 := by
  rw [(hasDerivAt_thetaNoetherFlow x t).deriv]
  unfold thetaNoetherMechanicalEnergy thetaNoetherPotential
  rw [thetaNoetherSpeed_sq]
  ring

end RHTower.ThetaSourceWard
