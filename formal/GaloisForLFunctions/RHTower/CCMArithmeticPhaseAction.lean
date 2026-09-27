import GaloisForLFunctions.RHTower.CCMThetaArithmeticPhaseOrbit
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue

/-!
# A conservative action for the literal arithmetic phase potential

The exact phase orbit supplies `B(1-cos(q))`. Choosing a positive kinetic
energy above its entire range constructs a Hamilton--Jacobi action and a
global travel-time coordinate. The mechanical action has time-translation
symmetry and its Noether charge is the mechanical energy. The next module
inverts the travel coordinate to construct an actual global solution.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

def arithmeticPhasePotential (B q : ℝ) : ℝ := B * (1 - Real.cos q)

def arithmeticPhaseEnergyLevel (B : ℝ) : ℝ := 2 * |B| + 1

def arithmeticPhaseSpeed (B q : ℝ) : ℝ :=
  Real.sqrt (2 * (arithmeticPhaseEnergyLevel B - arithmeticPhasePotential B q))

def arithmeticPhaseSpeedBound (B : ℝ) : ℝ := Real.sqrt (8 * |B| + 2)

theorem abs_arithmeticPhasePotential_le (B q : ℝ) :
    |arithmeticPhasePotential B q| ≤ 2 * |B| := by
  have h0 : 0 ≤ 1 - Real.cos q := sub_nonneg.mpr (Real.cos_le_one q)
  have h2 : 1 - Real.cos q ≤ 2 := by linarith [Real.neg_one_le_cos q]
  rw [arithmeticPhasePotential, abs_mul, abs_of_nonneg h0]
  nlinarith [abs_nonneg B]

theorem arithmeticPhaseKinetic_pos (B q : ℝ) :
    0 < arithmeticPhaseEnergyLevel B - arithmeticPhasePotential B q := by
  have h := (le_abs_self (arithmeticPhasePotential B q)).trans (abs_arithmeticPhasePotential_le B q)
  unfold arithmeticPhaseEnergyLevel
  linarith

theorem arithmeticPhaseSpeed_pos (B q : ℝ) : 0 < arithmeticPhaseSpeed B q :=
  Real.sqrt_pos.mpr (mul_pos zero_lt_two (arithmeticPhaseKinetic_pos B q))

theorem arithmeticPhaseSpeed_sq (B q : ℝ) :
    arithmeticPhaseSpeed B q ^ 2 =
      2 * (arithmeticPhaseEnergyLevel B - arithmeticPhasePotential B q) :=
  Real.sq_sqrt (mul_nonneg zero_le_two (arithmeticPhaseKinetic_pos B q).le)

theorem arithmeticPhaseSpeedBound_pos (B : ℝ) : 0 < arithmeticPhaseSpeedBound B := by
  unfold arithmeticPhaseSpeedBound
  apply Real.sqrt_pos.mpr
  positivity

theorem arithmeticPhaseSpeed_le_bound (B q : ℝ) :
    arithmeticPhaseSpeed B q ≤ arithmeticPhaseSpeedBound B := by
  apply Real.sqrt_le_sqrt
  have h := (neg_le_abs (arithmeticPhasePotential B q)).trans (abs_arithmeticPhasePotential_le B q)
  unfold arithmeticPhaseEnergyLevel
  linarith

theorem hasDerivAt_arithmeticPhasePotential (B q : ℝ) :
    HasDerivAt (arithmeticPhasePotential B) (B * Real.sin q) q := by
  convert! ((Real.hasDerivAt_cos q).const_sub 1).const_mul B using 1
  simp only [neg_neg]

theorem continuous_arithmeticPhasePotential (B : ℝ) : Continuous (arithmeticPhasePotential B) := by
  unfold arithmeticPhasePotential
  fun_prop

theorem continuous_arithmeticPhaseSpeed (B : ℝ) : Continuous (arithmeticPhaseSpeed B) :=
  Real.continuous_sqrt.comp
    (continuous_const.mul (continuous_const.sub (continuous_arithmeticPhasePotential B)))

theorem hasDerivAt_arithmeticPhaseSpeed (B q : ℝ) :
    HasDerivAt (arithmeticPhaseSpeed B) (-B * Real.sin q / arithmeticPhaseSpeed B q) q := by
  have h := (((hasDerivAt_arithmeticPhasePotential B q).const_sub
    (arithmeticPhaseEnergyLevel B)).const_mul 2).sqrt
      (ne_of_gt (mul_pos zero_lt_two (arithmeticPhaseKinetic_pos B q)))
  convert! h using 1
  dsimp only [arithmeticPhaseSpeed]
  ring

def arithmeticPhaseLagrangian (B q v : ℝ) : ℝ := v ^ 2 / 2 - arithmeticPhasePotential B q

def arithmeticPhaseMechanicalEnergy (B q v : ℝ) : ℝ := v ^ 2 / 2 + arithmeticPhasePotential B q

theorem hasDerivAt_arithmeticPhaseLagrangian_velocity (B q v : ℝ) :
    HasDerivAt (arithmeticPhaseLagrangian B q) v v := by
  convert! (((hasDerivAt_id v).pow 2).div_const 2).sub_const (arithmeticPhasePotential B q) using 1
  simp

theorem hasDerivAt_arithmeticPhaseLagrangian_position (B q v : ℝ) :
    HasDerivAt (fun x => arithmeticPhaseLagrangian B x v) (-B * Real.sin q) q := by
  convert! (hasDerivAt_arithmeticPhasePotential B q).const_sub (v ^ 2 / 2) using 1
  ring

/-- Time-translation Noether charge, with the potential fixed by the arithmetic phase law. -/
theorem arithmeticPhase_noether_charge (B q v : ℝ) :
    v * deriv (arithmeticPhaseLagrangian B q) v - arithmeticPhaseLagrangian B q v =
      arithmeticPhaseMechanicalEnergy B q v := by
  rw [(hasDerivAt_arithmeticPhaseLagrangian_velocity B q v).deriv]
  unfold arithmeticPhaseLagrangian arithmeticPhaseMechanicalEnergy
  ring

def arithmeticPhaseAction (B : ℝ) (q : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, arithmeticPhaseLagrangian B (q t) (deriv q t)

theorem arithmeticPhaseAction_time_translation (B : ℝ) (q : ℝ → ℝ) (a b c : ℝ) :
    arithmeticPhaseAction B (fun t => q (t + c)) a b =
      arithmeticPhaseAction B q (a + c) (b + c) := by
  simp only [arithmeticPhaseAction, deriv_comp_add_const]
  exact intervalIntegral.integral_comp_add_right
    (fun t => arithmeticPhaseLagrangian B (q t) (deriv q t)) c

def arithmeticPhaseHamiltonJacobiAction (B q : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..q, arithmeticPhaseSpeed B x

theorem hasDerivAt_arithmeticPhaseHamiltonJacobiAction (B q : ℝ) :
    HasDerivAt (arithmeticPhaseHamiltonJacobiAction B) (arithmeticPhaseSpeed B q) q :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_arithmeticPhaseSpeed B).intervalIntegrable 0 q)
    (continuous_arithmeticPhaseSpeed B).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_arithmeticPhaseSpeed B).continuousAt

/-- Inverse construction: the energy level supplies an actual global Hamilton--Jacobi solution. -/
theorem arithmeticPhaseHamiltonJacobi_energy (B q : ℝ) :
    arithmeticPhaseMechanicalEnergy B q (deriv (arithmeticPhaseHamiltonJacobiAction B) q) =
      arithmeticPhaseEnergyLevel B := by
  rw [(hasDerivAt_arithmeticPhaseHamiltonJacobiAction B q).deriv]
  unfold arithmeticPhaseMechanicalEnergy
  rw [arithmeticPhaseSpeed_sq]
  ring

def arithmeticPhaseTravelTime (B q : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..q, 1 / arithmeticPhaseSpeed B x

theorem continuous_arithmeticPhaseInverseSpeed (B : ℝ) :
    Continuous (fun x => 1 / arithmeticPhaseSpeed B x) :=
  continuous_const.div (continuous_arithmeticPhaseSpeed B) (fun x => (arithmeticPhaseSpeed_pos B x).ne')

theorem hasDerivAt_arithmeticPhaseTravelTime (B q : ℝ) :
    HasDerivAt (arithmeticPhaseTravelTime B) (1 / arithmeticPhaseSpeed B q) q :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_arithmeticPhaseInverseSpeed B).intervalIntegrable 0 q)
    (continuous_arithmeticPhaseInverseSpeed B).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_arithmeticPhaseInverseSpeed B).continuousAt

theorem continuous_arithmeticPhaseTravelTime (B : ℝ) : Continuous (arithmeticPhaseTravelTime B) :=
  continuous_iff_continuousAt.mpr fun q => (hasDerivAt_arithmeticPhaseTravelTime B q).continuousAt

theorem arithmeticPhaseTravelTime_zero (B : ℝ) : arithmeticPhaseTravelTime B 0 = 0 := by
  simp [arithmeticPhaseTravelTime]

theorem strictMono_arithmeticPhaseTravelTime (B : ℝ) : StrictMono (arithmeticPhaseTravelTime B) := by
  apply strictMono_of_deriv_pos
  intro q
  rw [(hasDerivAt_arithmeticPhaseTravelTime B q).deriv]
  exact one_div_pos.mpr (arithmeticPhaseSpeed_pos B q)

private theorem arithmeticPhaseTravelTime_drift_monotone (B : ℝ) :
    Monotone (fun q => arithmeticPhaseTravelTime B q - (1 / arithmeticPhaseSpeedBound B) * q) := by
  have hd (q : ℝ) : HasDerivAt
      (fun x => arithmeticPhaseTravelTime B x - (1 / arithmeticPhaseSpeedBound B) * x)
      (1 / arithmeticPhaseSpeed B q - 1 / arithmeticPhaseSpeedBound B) q := by
    convert! (hasDerivAt_arithmeticPhaseTravelTime B q).sub
      ((hasDerivAt_id q).const_mul (1 / arithmeticPhaseSpeedBound B)) using 1
    simp only [mul_one]
  apply monotone_of_deriv_nonneg (fun q => (hd q).differentiableAt)
  intro q
  rw [(hd q).deriv]
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (arithmeticPhaseSpeed_pos B q)
    (arithmeticPhaseSpeed_le_bound B q))

theorem tendsto_arithmeticPhaseTravelTime_atTop (B : ℝ) :
    Tendsto (arithmeticPhaseTravelTime B) atTop atTop := by
  apply tendsto_atTop_mono' atTop (f₁ := fun q : ℝ => (1 / arithmeticPhaseSpeedBound B) * q)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
    have h := arithmeticPhaseTravelTime_drift_monotone B hq
    simp only [arithmeticPhaseTravelTime_zero, mul_zero, sub_zero] at h
    linarith
  · exact (tendsto_const_mul_atTop_of_pos (one_div_pos.mpr (arithmeticPhaseSpeedBound_pos B))).mpr tendsto_id

theorem tendsto_arithmeticPhaseTravelTime_atBot (B : ℝ) :
    Tendsto (arithmeticPhaseTravelTime B) atBot atBot := by
  apply tendsto_atBot_mono' atBot (f₁ := fun q : ℝ => (1 / arithmeticPhaseSpeedBound B) * q)
  · filter_upwards [eventually_le_atBot (0 : ℝ)] with q hq
    have h := arithmeticPhaseTravelTime_drift_monotone B hq
    simp only [arithmeticPhaseTravelTime_zero, mul_zero, sub_zero] at h
    linarith
  · exact (tendsto_const_mul_atBot_of_pos (one_div_pos.mpr (arithmeticPhaseSpeedBound_pos B))).mpr tendsto_id

theorem surjective_arithmeticPhaseTravelTime (B : ℝ) : Function.Surjective (arithmeticPhaseTravelTime B) :=
  (continuous_arithmeticPhaseTravelTime B).surjective
    (tendsto_arithmeticPhaseTravelTime_atTop B) (tendsto_arithmeticPhaseTravelTime_atBot B)

end RHTower
