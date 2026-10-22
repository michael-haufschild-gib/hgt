import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullSourceOnsetReduction

/-!
# Finite translation of the fixed causal theta source

The original smooth onset has a nonzero resonant translation moment. Its
derivative contact has zero translation moment. Both statements retain the
original complex rate and hold for every fixed nonnegative real clock step.
They do not identify this temporal moment with a physical left-QNM action.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMSourceClockTranslation
open D4BMJointSource D4BMModularCore D4BMAngularSeries D4BMHorizon D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

private theorem transition_shift_integral (h : NNReal) :
    (∫ u in -(h:ℝ)..1, (Real.smoothTransition (u+h)-Real.smoothTransition u)) = h := by
  have hc := Real.smoothTransition.continuous
  have hl : (∫ u in -(h:ℝ)..0, Real.smoothTransition u) = 0 := by
    calc
      _ = ∫ _u in -(h:ℝ)..0, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rcases mem_uIcc.mp hu with hu | hu
        · exact Real.smoothTransition.zero_of_nonpos hu.2
        · exact Real.smoothTransition.zero_of_nonpos (hu.2.trans (neg_nonpos.mpr h.2))
      _ = 0 := by simp
  have hr : (∫ u in (1:ℝ)..1+h, Real.smoothTransition u) = h := by
    calc
      _ = ∫ _u in (1:ℝ)..1+h, (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le (by linarith [h.2])] at hu
        exact Real.smoothTransition.one_of_one_le hu.1
      _ = h := by simp
  have hi : IntervalIntegrable (fun u : ℝ => Real.smoothTransition (u+(h:ℝ))) volume (-(h:ℝ)) 1 :=
    (show Continuous (fun u : ℝ => Real.smoothTransition (u+(h:ℝ))) from by fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi (hc.intervalIntegrable _ _),
    intervalIntegral.integral_comp_add_right]
  simp only [neg_add_cancel]
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) (0:ℝ) 1) (hc.intervalIntegrable (μ:=volume) 1 (1+h))
  have hb := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) (-(h:ℝ)) 0) (hc.intervalIntegrable (μ:=volume) 0 1)
  rw [hl,zero_add] at hb
  rw [hr] at ha
  linarith

private theorem transition_deriv_integral (a b : ℝ) :
    (∫ u in a..b, deriv Real.smoothTransition u) =
      Real.smoothTransition b-Real.smoothTransition a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u _
    exact ((Real.smoothTransition.contDiff (n:=1)).differentiable (by norm_num)).differentiableAt.hasDerivAt
  · exact continuous_deriv_smoothTransition.intervalIntegrable _ _

private theorem transition_deriv_shift_integral (h : NNReal) :
    (∫ u in -(h:ℝ)..1,
      deriv Real.smoothTransition (u+h)-deriv Real.smoothTransition u) = 0 := by
  have hi : IntervalIntegrable (fun u : ℝ => deriv Real.smoothTransition (u+(h:ℝ))) volume (-(h:ℝ)) 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_deriv_smoothTransition.comp (continuous_id.add_const (h:ℝ))
  rw [intervalIntegral.integral_sub hi
    (continuous_deriv_smoothTransition.intervalIntegrable _ _),
    intervalIntegral.integral_comp_add_right]
  simp only [neg_add_cancel]
  rw [transition_deriv_integral,transition_deriv_integral,
    Real.smoothTransition.one_of_one_le (by linarith [h.2]),
    Real.smoothTransition.zero_of_nonpos (by rfl),
    Real.smoothTransition.one_of_one_le (by rfl),
    Real.smoothTransition.zero_of_nonpos (show -(h:ℝ) ≤ 0 from neg_nonpos.mpr h.2)]
  ring

/-- Finite translation relative to the original exponential, at an unchanged rate. -/
def clockDifference (v : ℂ) (h : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  f (u+h)-Complex.exp (v*(h:ℂ))*f u

/-- Compact resonant moment of the actual finite translation defect. -/
def clockMoment (v : ℂ) (h : NNReal) (f : ℝ → ℂ) : ℂ :=
  ∫ u in -(h:ℝ)..1, Complex.exp (-v*(u:ℂ))*clockDifference v h f u

/-- Arbitrary spatial coefficients of the original onset and its retained contact. -/
def sourceAndContact (v A B : ℂ) (u : ℝ) : ℂ :=
  (A*(Real.smoothTransition u:ℂ)+B*((deriv Real.smoothTransition u:ℝ):ℂ))*
    Complex.exp (v*(u:ℂ))

private theorem exponential_cancel (v : ℂ) (u h : ℝ) :
    Complex.exp (-v*(u:ℂ))*Complex.exp (v*((u+h:ℝ):ℂ)) =
      Complex.exp (v*(h:ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact local clock defect, retaining both the source and derivative contact. -/
theorem sourceAndContact_clockDifference (v A B : ℂ) (h u : ℝ) :
    Complex.exp (-v*(u:ℂ))*clockDifference v h (sourceAndContact v A B) u =
      Complex.exp (v*(h:ℂ))*
        (A*((Real.smoothTransition (u+h)-Real.smoothTransition u:ℝ):ℂ)+
          B*((deriv Real.smoothTransition (u+h)-deriv Real.smoothTransition u:ℝ):ℂ)) := by
  have he := exponential_cancel v u h
  have hz := exponential_cancel v u 0
  simp only [add_zero,Complex.ofReal_zero,mul_zero,Complex.exp_zero] at hz
  dsimp only [clockDifference,sourceAndContact]
  push_cast at he ⊢
  linear_combination
    (A*(Real.smoothTransition (u+h):ℂ)+B*((deriv Real.smoothTransition (u+h):ℝ):ℂ))*he -
    Complex.exp (v*(h:ℂ))*(A*(Real.smoothTransition u:ℂ)+B*((deriv Real.smoothTransition u:ℝ):ℂ))*hz

/-- The contact cannot change the resonant translation mass of the original source. -/
theorem sourceAndContact_clockMoment (v A B : ℂ) (h : NNReal) :
    clockMoment v h (sourceAndContact v A B) = (h:ℂ)*Complex.exp (v*(h:ℂ))*A := by
  have hc : Continuous (fun u : ℝ =>
      ((Real.smoothTransition (u+h)-Real.smoothTransition u:ℝ):ℂ)) := by fun_prop
  have hd : Continuous (fun u : ℝ =>
      ((deriv Real.smoothTransition (u+h)-deriv Real.smoothTransition u:ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_deriv_smoothTransition.comp (continuous_id.add_const (h:ℝ))).sub
        continuous_deriv_smoothTransition)
  unfold clockMoment
  simp only [sourceAndContact_clockDifference]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hc.const_mul A).intervalIntegrable _ _)
      ((hd.const_mul B).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal,
    transition_shift_integral,transition_deriv_shift_integral]
  push_cast
  ring

/-- The literal smooth causal source has the exact nonzero-step contact mass. -/
theorem timeOnset_clockMoment (v : ℂ) (h : NNReal) :
    clockMoment v h (timeOnset v) = (h:ℂ)*Complex.exp (v*(h:ℂ)) := by
  have he : timeOnset v = sourceAndContact v 1 0 := by
    funext u
    simp [timeOnset,sourceAndContact]
  rw [he,sourceAndContact_clockMoment,mul_one]

/-- At a common unit clock step the original source is never translation covariant. -/
theorem timeOnset_unitClockDifference_ne_zero (v : ℂ) :
    clockDifference v 1 (timeOnset v) ≠ 0 := by
  intro he
  have hm := timeOnset_clockMoment v 1
  have hz : clockMoment v 1 (timeOnset v) = 0 := by
    simp [clockMoment,he]
  rw [hz] at hm
  simp only [NNReal.coe_one,Complex.ofReal_one,one_mul,mul_one] at hm
  exact Complex.exp_ne_zero v hm.symm

/-- Full unprojected scalar source moment, including its original gradient channel. -/
theorem timeOriginalForcing_clockMoment (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (h : NNReal) (t : ℝ) (z : Point) :
    clockMoment (2*physicalRate q branch) h
      (fun u => timeOriginalForcing q branch a (u-t) t z) =
      (h:ℂ)*Complex.exp (2*physicalRate q branch*(h:ℂ))*
        originalForcing (physicalRate q branch) 0 a 1
          (fullSquarePotential q z) (fullGradientEnergy q z/2) t := by
  have he : (fun u => timeOriginalForcing q branch a (u-t) t z) =
      sourceAndContact (2*physicalRate q branch)
        (originalForcing (physicalRate q branch) 0 a 1
          (fullSquarePotential q z) (fullGradientEnergy q z/2) t) 0 := by
    funext u
    simp [timeOriginalForcing,timeOnset,sourceAndContact,sub_add_cancel,mul_assoc]
  rw [he,sourceAndContact_clockMoment]

/-- The full retained pulse has zero resonant translation mass, with both angular channels. -/
theorem fullSourceOnsetPulse_clockMoment (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (h : NNReal) (t : ℝ) (z : Point) :
    clockMoment (2*physicalRate q branch) h
      (fun u => fullSourceOnsetPulse q branch a (u-t) t z) = 0 := by
  have he : (fun u => fullSourceOnsetPulse q branch a (u-t) t z) =
      sourceAndContact (2*physicalRate q branch) 0
        (-2*sourceSeedFieldFirst (physicalRate q branch) 0 a 1 (parameter q branch) t*
          fullAngularField q branch z+
          2*parameter q branch*radialLiftFirst (physicalRate q branch) 0 a 1 t*
            fullSquarePotential q z) := by
    funext u
    rw [fullSourceOnsetPulse_transition]
    simp [sourceAndContact,sub_add_cancel]
  rw [he,sourceAndContact_clockMoment,mul_zero]

/-- The original wave-image combination retains the full source translation mass.
The response angular field, half-square field and the actual wave operator are unchanged. -/
theorem waveImages_clockMoment (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (h : NNReal) (t : ℝ) (z : UpperHalfPlane) :
    clockMoment (2*physicalRate q branch) h
      (fun u => parameter q branch*timeFieldWave (timeLiftField q branch a)
        (u-t) t (coordinates z)-
        timeFieldWave (timeAngularSeedField q branch a) (u-t) t (coordinates z)) =
      (h:ℂ)*Complex.exp (2*physicalRate q branch*(h:ℂ))*parameter q branch*
        originalForcing (physicalRate q branch) 0 a 1
          (fullSquarePotential q (coordinates z)) (fullGradientEnergy q (coordinates z)/2) t := by
  let A := originalForcing (physicalRate q branch) 0 a 1
    (fullSquarePotential q (coordinates z)) (fullGradientEnergy q (coordinates z)/2) t
  let B := -2*sourceSeedFieldFirst (physicalRate q branch) 0 a 1 (parameter q branch) t*
    fullAngularField q branch (coordinates z)+
    2*parameter q branch*radialLiftFirst (physicalRate q branch) 0 a 1 t*
      fullSquarePotential q (coordinates z)
  have he : (fun u => parameter q branch*timeFieldWave (timeLiftField q branch a)
        (u-t) t (coordinates z)-
        timeFieldWave (timeAngularSeedField q branch a) (u-t) t (coordinates z)) =
      sourceAndContact (2*physicalRate q branch) (parameter q branch*A) (-B) := by
    funext u
    have hw := fullSourceOnset_wave_identity q branch a (u-t) t (coordinates z) z.im_pos
    rw [fullSourceOnsetPulse_transition] at hw
    dsimp only [timeOriginalForcing,timeOnset] at hw
    simp only [sub_add_cancel] at hw
    dsimp only [sourceAndContact,A,B]
    linear_combination -hw
  rw [he,sourceAndContact_clockMoment]
  dsimp only [A]
  ring

end
end RHTower.D4BMSourceClockTranslation
