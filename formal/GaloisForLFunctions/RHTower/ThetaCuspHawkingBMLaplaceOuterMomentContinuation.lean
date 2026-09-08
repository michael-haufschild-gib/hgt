import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceOuterEndpointBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceEndpointGreen

/-! Entire outer endpoint integration with the original fixed onset and normalization restored. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric MeasureTheory GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem outerSource_measurable (s chi a J K w : ℂ) :
    Measurable (fun t : ℝ => normalizable w chi t*sourceProfile s w a J K 1 t) := by
  have hg : Measurable (fun t : ℝ => gaussFactor w chi true (1-(t:ℂ))) := by
    have ht : Measurable (fun t : ℝ => ∑' n : ℕ, ordinaryHypergeometricCoefficient
        (gaussC w-gaussA w chi) (gaussC w-gaussB w chi) (3/2:ℂ) n*(1-(t:ℂ))^n) :=
      Measurable.tsum (fun n : ℕ => show Measurable
        (fun t : ℝ => ordinaryHypergeometricCoefficient (gaussC w-gaussA w chi)
          (gaussC w-gaussB w chi) (3/2:ℂ) n*(1-(t:ℂ))^n) by fun_prop)
    simpa only [gaussFactor,radialSeries,↓reduceIte,outerSeries,ordinaryHypergeometric_sum_eq,smul_eq_mul] using ht
  have hs := (sourceRemainder_continuous s w a J K 1).measurable
  unfold normalizable dress outerFactor sourceProfile power
  fun_prop

private theorem outerSource_frequency_differentiableAt (s chi a J K w : ℂ)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    DifferentiableAt ℂ (fun u => normalizable u chi t*sourceProfile s u a J K 1 t) w := by
  rcases ht1.eq_or_lt with rfl | ht1
  · have he : (fun u => normalizable u chi 1*sourceProfile s u a J K 1 1) = fun _ : ℂ => (0:ℂ) := by
      funext u
      simp [normalizable,dress,outerFactor,power]
    rw [he]
    fun_prop
  · exact (normalizable_frequency_entire chi ⟨ht,ht1⟩ w).mul (sourceProfile_frequency_entire s a J K 1 ht w)

/-- The actual unnormalized outer endpoint integral is entire in independent frequency. -/
theorem outerSourceIntegral_entire (s chi a J K : ℂ) {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Differentiable ℂ (fun w => ∫ t in Ioc b (1:ℝ), normalizable w chi t*sourceProfile s w a J K 1 t) := by
  intro w
  obtain ⟨C,-,hbound⟩ := outerSource_uniform_bound s chi a J K w hb hb1
  let F (u : ℂ) : ℝ → ℂ := (Ioc b (1:ℝ)).indicator (fun t => normalizable u chi t*sourceProfile s u a J K 1 t)
  let bound : ℝ → ℝ := (Ioc b (1:ℝ)).indicator (fun _ => C)
  have hm (u : ℂ) (_hu : u ∈ ball w 1) : AEStronglyMeasurable (F u) volume :=
    ((outerSource_measurable s chi a J K u).indicator measurableSet_Ioc).aestronglyMeasurable
  have hd (t : ℝ) : DifferentiableOn ℂ (fun u => F u t) (ball w 1) := by
    intro u hu
    by_cases ht : t ∈ Ioc b (1:ℝ)
    · simp only [F,indicator_of_mem ht]
      exact (outerSource_frequency_differentiableAt s chi a J K u (hb.trans ht.1) ht.2).differentiableWithinAt
    · simp only [F,indicator_of_notMem ht]
      fun_prop
  have hB (t : ℝ) (u : ℂ) (hu : u ∈ ball w 1) : ‖F u t‖ ≤ bound t := by
    by_cases ht : t ∈ Ioc b (1:ℝ)
    · simp only [F,bound,indicator_of_mem ht]
      exact hbound u hu t ⟨ht.1.le,ht.2⟩
    · simp only [F,bound,indicator_of_notMem ht,norm_zero,le_refl]
  have hi : Integrable bound volume := (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have hh := differentiableAt_integral_of_cauchy_dominated (by norm_num : (0:ℝ)<1) hm hd hB hi
  simpa only [F,integral_indicator measurableSet_Ioc] using hh

/-- The original outer moment with its fixed source onset analytically continued. -/
def continuedOuterMoment (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  (∫ t in Ioc b (1:ℝ), normalizable w chi t*sourceProfile s w a J K 1 t)*
    (1/(w-2*s)+onsetCorrection (2*s) w)/(-connection w chi)

/-- The complete normalized outer moment is meromorphic off the real frequency axis. -/
theorem continuedOuterMoment_meromorphicAt (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) : MeromorphicAt (continuedOuterMoment s chi a J K b) w := by
  have hm := ((outerSourceIntegral_entire s chi a J K hb hb1).analyticAt w).meromorphicAt
  have hi : MeromorphicAt (fun u : ℂ => 1/(u-2*s)) w :=
    (show AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) w from analyticAt_const).meromorphicAt.div
      (show AnalyticAt ℂ (fun u : ℂ => u-2*s) w by fun_prop).meromorphicAt
  have hc := ((onsetCorrection_entire (2*s)).analyticAt w).meromorphicAt
  exact (hm.mul (hi.add hc)).div (connection_frequency_analyticAt w chi hw).meromorphicAt.neg

/-- The continued outer moment agrees with the literal endpoint integral in the
source convergence chamber, with no chosen boundary coefficient. -/
theorem continuedOuterMoment_eq_original (s chi a J K w : ℂ) (hsource : (2*s).re < w.re)
    {b : ℝ} (hb1 : b ≤ 1) :
    continuedOuterMoment s chi a J K b w = outerMoment w chi s a J K (onsetTransform (2*s) w) b := by
  rw [continuedOuterMoment,← onsetTransform_eq (2*s) w hsource,outerMoment,
    intervalIntegral.integral_of_le hb1,← integral_mul_const,div_eq_mul_inv,← integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  unfold sourceProfile sourceRemainder
  ring

end
end RHTower.D4BMLaplaceRadial
