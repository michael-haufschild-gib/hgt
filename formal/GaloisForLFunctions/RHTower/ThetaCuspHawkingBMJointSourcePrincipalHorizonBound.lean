import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalContinuation
import GaloisForLFunctions.HTGeometry.ForcedSecondOrderHorizonBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceGreenProfileBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTransformChamber
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceCompactPower

/-! Cancellation-preserving horizon growth of the actual continued principal differences. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual tortoise horizon coordinate supplies two powers of exponential decay. -/
theorem horizonCoordinate_norm_le_exp (t : ℝ) (ht : t < 0) :
    ‖(horizonCoordinate t:ℂ)‖ ≤ 4*Real.exp (2*t) := by
  have hu := radialUnit_bounds t ht
  have hz := horizonCoordinate_interior t ht
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz.1,horizonCoordinate_factor,mul_pow]
  have he : (Real.exp t)^2 = Real.exp (2*t) := by rw [pow_two,← Real.exp_add]; congr 1; ring
  rw [he]
  nlinarith [Real.exp_pos (2*t),mul_nonneg (Real.exp_pos (2*t)).le
    (show 0 ≤ 4-(1+radialUnit t)^2 by nlinarith)]

/-- Exact source cancellation yields the decaying forcing required by the principal ODE. -/
theorem reducedCoefficient_amplitude_norm_le_exp (s w a T J : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t < 0,
      ‖reducedCoefficient s w a T t*J‖ ≤ C*Real.exp ((w.re+2)*t) := by
  let F : ℝ → ℂ := fun u => T*(sourceHorizonProfile s a 0 u+w*sourceHorizonProfile s a 1 u)*J
  have hF : ContinuousOn F (Icc 0 1) :=
    (continuousOn_const.mul ((sourceHorizonProfile_continuousOn s a 0).add
      (continuousOn_const.mul (sourceHorizonProfile_continuousOn s a 1)))).mul continuousOn_const
  obtain ⟨C,hC,hb⟩ := laplaceProfile_norm_le_exp (w+2) F hF
  refine ⟨C,hC,fun t ht => ?_⟩
  rw [reducedCoefficient_frequency_horizon]
  simpa [F,mul_assoc] using hb t ht

/-- The true continued principal subtraction obeys its free-frequency growth bound,
including totalized values at connection zeros. The estimate is obtained from its actual ODE. -/
theorem continuedPrincipalDifference_norm_le_exp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (hwr : w.re ≤ 0) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t < 0,
      ‖continuedPrincipalDifference q branch w a i t‖ ≤ C*Real.exp (w.re*t) := by
  let s := physicalRate q branch
  let T := continuedOnset s w
  let m := principalExponent q i
  let J := principalAmplitude q i
  by_cases hc : connection w (principalFrequency q i) = 0
  · let P : ℝ → ℂ := fun u => (s*(s-1)/4)*(u:ℂ)^3*J
    obtain ⟨C,hC,hb⟩ := sourceAmplitude_profile_norm_le_exp s w a T P (by dsimp [P]; fun_prop)
    refine ⟨C,hC,fun t ht => ?_⟩
    have he : continuedPrincipalDifference q branch w a i t =
        sourceAmplitude s w a T t*P (radialUnit t) := by
      simp only [continuedPrincipalDifference,continuedTortoiseGreen,continuedResponse,
        continuedHorizonMoment,continuedOuterMoment,hc,neg_zero,div_zero,mul_zero,add_zero,zero_sub]
      dsimp [radialLift,P,s,T,J]
      ring
    rw [he]
    exact hb t ht
  · let U := continuedPrincipalDifference q branch w a i
    let V := continuedPrincipalDifferenceFirst q branch w a i
    let p : ℝ → ℂ := fun t => -(horizonCoordinate t:ℂ)*(m*(m-1))
    let f : ℝ → ℂ := fun t => reducedCoefficient s w a T t*J
    have hd (t : ℝ) (ht : t < 0) := continuedPrincipalDifference_hasDerivAt q branch w a hw hwre i t ht
    have hV (t : ℝ) (ht : t < 0) : HasDerivAt V (w^2*U t+p t*U t-f t) t := by
      have he := continuedPrincipalDifference_equation q branch w a hw hwre i hc t ht
      rw [continuedPrincipalDifference_secondDerivative q branch w a hw hwre i t ht] at he
      convert! (hd t ht).2 using 1
      dsimp [U,p,f,m,s,T,J]
      linear_combination he
    have hp (t : ℝ) (ht : t < 0) : ‖p t‖ ≤ (4*‖m*(m-1)‖)*Real.exp (2*t) := by
      dsimp [p]
      rw [norm_mul,norm_neg]
      calc
        _ ≤ (4*Real.exp (2*t))*‖m*(m-1)‖ :=
          mul_le_mul_of_nonneg_right (horizonCoordinate_norm_le_exp t ht) (norm_nonneg _)
        _ = _ := by ring
    obtain ⟨B,hB,hf⟩ := reducedCoefficient_amplitude_norm_le_exp s w a T J
    have hw0 : w ≠ 0 := by intro he; apply hw; simp [he]
    exact GaloisForLFunctions.HTGeometry.forcedSecondOrder_horizon_bound w hw0 hwr U V p f
      (4*‖m*(m-1)‖) B (by positivity) hB (fun t ht => (hd t ht).1) hV hp hf

end
end RHTower.D4BMJointSource
