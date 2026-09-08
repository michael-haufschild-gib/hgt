import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedCutoffMajorant
import GaloisForLFunctions.HTGeometry.L2RestrictedHolomorphy

/-! The original native reduced source has an undivided holomorphic family in its actual radial L² space. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMJointWave GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The native reduced source with its literal onset numerator and all horizon terms retained. -/
def clearedReducedCoefficient (s a w : ℂ) (t : ℝ) : ℂ :=
  reducedCoefficient s w a (clearedOnset s w) t

/-- The original native source is cleared by its actual single source denominator. -/
theorem clearedReducedCoefficient_eq (s a w : ℂ) (hs : w-2*s ≠ 0) (t : ℝ) :
    clearedReducedCoefficient s a w t = (w-2*s)*reducedCoefficient s w a (continuedOnset s w) t := by
  dsimp [clearedReducedCoefficient,reducedCoefficient,sourceAmplitude,clearedOnset,continuedOnset]
  field_simp [hs]

/-- The undivided native coefficient is pointwise entire in independent frequency. -/
theorem clearedReducedCoefficient_entire (s a : ℂ) (t : ℝ) :
    Differentiable ℂ (fun w => clearedReducedCoefficient s a w t) := by
  intro w
  have hS := (clearedOnset_entire s) w
  unfold clearedReducedCoefficient reducedCoefficient sourceAmplitude reducedPolynomial liftSecondPolynomial amplitudeRate
  fun_prop

/-- One positive horizon exponential dominates the entire native family on a frequency neighborhood. -/
theorem clearedReducedCoefficient_local_bound (s a w : ℂ) (hw : -2 < w.re) :
    ∃ R b C : ℝ, 0 < R ∧ 0 < b ∧ 0 ≤ C ∧
      MemLp (fun t : ℝ => C*Real.exp (b*t)) 2 radialMeasure ∧
      ∀ u ∈ ball w R, -2 < u.re ∧ ∀ t < 0,
        ‖clearedReducedCoefficient s a u t‖ ≤ C*Real.exp (b*t) := by
  let b := (w.re+2)/2
  have hb : 0 < b := by dsimp [b]; linarith
  have hwb : b-2 < w.re := by dsimp [b]; linarith
  have hn := Complex.continuous_re.continuousAt.eventually_const_lt hwb
  obtain ⟨R,hR,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  obtain ⟨C,hC,hbound⟩ := reducedCoefficient_family_norm_le_exp s a 1 (clearedOnset s) (fun _ => 1)
    (closedBall w R) (isCompact_closedBall w R) (clearedOnset_entire s).continuous.continuousOn continuousOn_const
  refine ⟨R,b,C,hR,hb,hC,horizonExponential_memLp b C hb hC,?_⟩
  intro u hu
  have hbu : b-2 < u.re := hsub (ball_subset_closedBall hu)
  refine ⟨by linarith,fun t ht => ?_⟩
  have he : ‖clearedReducedCoefficient s a u t‖ ≤ C*Real.exp ((u.re+2)*t) := by
    simpa only [clearedReducedCoefficient,one_mul,mul_one] using hbound u (ball_subset_closedBall hu) t ht
  exact he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_right (by linarith : b ≤ u.re+2) ht.le)) hC)

/-- The complete undivided native coefficient is differentiable in the genuine radial L² norm. -/
theorem clearedReducedCoefficient_l2_differentiableAt (s a w : ℂ) (hw : -2 < w.re) :
    DifferentiableAt ℂ (l2Family radialMeasure (clearedReducedCoefficient s a)) w := by
  obtain ⟨R,b,C,hR,hb,hC,hM,hbound⟩ := clearedReducedCoefficient_local_bound s a w hw
  apply differentiableAt_l2Family_restrict_of_cauchy_dominated volume (Iio 0) measurableSet_Iio
    (clearedReducedCoefficient s a) w R hR (fun t => C*Real.exp (b*t)) hM
  · intro u hu
    exact (reducedCoefficient_memLp_horizon s u a (clearedOnset s u) (hbound u hu).1).aestronglyMeasurable
  · intro t _
    exact (clearedReducedCoefficient_entire s a t).differentiableOn
  · intro t ht u hu
    exact (hbound u hu).2 t ht

/-- The native numerator is holomorphic with values in the actual radial L² space throughout its full source half-plane. -/
theorem clearedReducedCoefficient_l2_analyticAt (s a w : ℂ) (hw : -2 < w.re) :
    AnalyticAt ℂ (l2Family radialMeasure (clearedReducedCoefficient s a)) w := by
  have hd : DifferentiableOn ℂ (l2Family radialMeasure (clearedReducedCoefficient s a))
      {u : ℂ | -2 < u.re} := fun u hu => (clearedReducedCoefficient_l2_differentiableAt s a u hu).differentiableWithinAt
  exact hd.analyticAt (Complex.continuous_re.continuousAt.eventually_const_lt hw)

end
end RHTower.D4BMJointSource
