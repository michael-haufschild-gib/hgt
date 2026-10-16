import GaloisForLFunctions.RHTower.PaperThetaNativeResolvent
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Literal theta Green tails on bounded continuous forcing

The original positive source ratio controls the supremum norm independently
of forcing variation. Exact moment cancellation joins the two tails.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile HedenmalmPrimeTranslation ThetaFiniteTransport

abbrev NativeContinuousSpace := ℝ →ᵇ ℂ

def boundedThetaMoment (z : ℂ) (g : NativeContinuousSpace) : ℂ :=
  ∫ y, flatCharDensity z y*g y

theorem integrable_boundedThetaDensity (z : ℂ) (g : NativeContinuousSpace) :
    Integrable (fun y => flatCharDensity z y*g y) :=
  (integrable_flatCharDensity_all z).mul_bdd g.continuous.aestronglyMeasurable
    (Eventually.of_forall g.norm_coe_le_norm)

def boundedThetaMomentBound (z : ℂ) : ℝ := ∫ y, ‖flatCharDensity z y‖

theorem boundedThetaMomentBound_nonneg (z : ℂ) : 0 ≤ boundedThetaMomentBound z :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem norm_boundedThetaMoment_le (z : ℂ) (g : NativeContinuousSpace) :
    ‖boundedThetaMoment z g‖ ≤ boundedThetaMomentBound z*‖g‖ := by
  unfold boundedThetaMoment boundedThetaMomentBound
  calc
    _ ≤ ∫ y, ‖flatCharDensity z y*g y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖g‖*‖flatCharDensity z y‖ := by
      apply integral_mono (integrable_boundedThetaDensity z g).norm
        ((integrable_flatCharDensity_all z).norm.const_mul _)
      intro y
      change ‖flatCharDensity z y*g y‖ ≤ ‖g‖*‖flatCharDensity z y‖
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm y) (norm_nonneg _)).trans_eq
        (mul_comm _ _)
    _ = _ := by rw [integral_const_mul, mul_comm]

def boundedThetaTail (z : ℂ) (g : NativeContinuousSpace) (x : ℝ) : ℂ :=
  Complex.exp (-(I*z)*(x : ℂ))/(thetaSource.normalized x : ℂ) *
    ∫ y in Ioi x, flatCharDensity z y*g y

theorem integrable_boundedThetaRatio (z : ℂ) (g : NativeContinuousSpace) (x : ℝ) :
    Integrable (fun h => (sourceRatio h x : ℂ)*sourceChar z h*g (x+h)) :=
  (integrable_sourceRatio_character z x).mul_bdd
    (g.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun _ => g.norm_coe_le_norm _)

theorem boundedThetaTail_eq_ratio (z : ℂ) (g : NativeContinuousSpace) (x : ℝ) :
    boundedThetaTail z g x =
      ∫ h in Ioi (0 : ℝ), (sourceRatio h x : ℂ)*sourceChar z h*g (x+h) := by
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (thetaSource.normalized_pos x).ne'
  rw [boundedThetaTail, ← integral_Ioi_comp_add
    (fun y => flatCharDensity z y*g y) x, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with h
  rw [sourceRatio_normalized, flatCharDensity, sourceChar, sourceChar]
  push_cast
  have he : Complex.exp (-(I*z)*(x : ℂ))*Complex.exp (I*z*((x : ℂ)+(h : ℂ))) =
      Complex.exp (I*z*(h : ℂ)) := by rw [← Complex.exp_add]; congr 1; ring
  field_simp
  simp only [neg_mul] at he
  linear_combination (thetaSource.normalized (x+h) : ℂ)*g (x+h)*he

theorem norm_boundedThetaTail_le (z : ℂ) (g : NativeContinuousSpace) (x : ℝ) :
    ‖boundedThetaTail z g x‖ ≤ ‖g‖*forcedTailMass z x := by
  rw [boundedThetaTail_eq_ratio, forcedTailMass, ← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply setIntegral_mono_on (integrable_boundedThetaRatio z g x).norm.integrableOn
    ((integrable_sourceRatio_tilt (-z.im) x).integrableOn.const_mul _)
    measurableSet_Ioi
  intro h _
  rw [norm_mul, norm_sourceRatio_character]
  exact (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _)
    (mul_nonneg (sourceRatio_pos h x).le (Real.exp_pos _).le)).trans_eq (by ring)

theorem tendsto_boundedThetaTail_atTop (z : ℂ) (g : NativeContinuousSpace) :
    Tendsto (boundedThetaTail z g) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (norm_boundedThetaTail_le z g)
  simpa using (tendsto_forcedTailMass z).const_mul ‖g‖

theorem boundedThetaTail_integral_split (z : ℂ) (g : NativeContinuousSpace) (x : ℝ) :
    (∫ y in Ioi x, flatCharDensity z y*g y) =
      boundedThetaMoment z g-∫ y in Iic x, flatCharDensity z y*g y := by
  have hs := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (b := x)
    (integrable_boundedThetaDensity z g).integrableOn
    (integrable_boundedThetaDensity z g).integrableOn
  change _ = (∫ y, flatCharDensity z y*g y)-_
  rw [← hs]
  ring

theorem hasDerivAt_boundedThetaTail (z : ℂ) (g : NativeContinuousSpace) (x : ℝ) :
    HasDerivAt (boundedThetaTail z g)
      (-(sourceLogDerivative x+I*z)*boundedThetaTail z g x-g x) x := by
  have hρ := ((differentiable_normalized_theta x).hasDerivAt.ofReal_comp).differentiableAt.hasDerivAt
  have hρ0 : (thetaSource.normalized x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (thetaSource.normalized_pos x).ne'
  have hI := hasDerivAt_setIntegral_Iic ((continuous_flatCharDensity z).mul g.continuous)
    (integrable_boundedThetaDensity z g) x
  have ht : HasDerivAt (fun x => ∫ y in Ioi x, flatCharDensity z y*g y)
      (-flatCharDensity z x*g x) x := by
    simp_rw [boundedThetaTail_integral_split]
    convert hI.const_sub (boundedThetaMoment z g) using 1 <;>
      first | rfl | simp only [Pi.mul_apply, neg_mul]
  have he : HasDerivAt (fun x : ℝ => Complex.exp (-(I*z)*(x : ℂ)))
      (-(I*z)*Complex.exp (-(I*z)*(x : ℂ))) x := by
    simpa [mul_comm] using
      (((hasDerivAt_id (x : ℂ)).const_mul (-(I*z))).cexp).comp_ofReal
  refine ((he.div hρ hρ0).mul ht).congr_deriv ?_
  dsimp [boundedThetaTail, sourceLogDerivative, flatCharDensity]
  field_simp
  have hc := exp_mul_sourceChar z x
  simp only [neg_mul] at hc
  linear_combination -(thetaSource.normalized x : ℂ)^2*g x*hc

theorem continuous_boundedThetaTail (z : ℂ) (g : NativeContinuousSpace) :
    Continuous (boundedThetaTail z g) :=
  (show Differentiable ℝ (boundedThetaTail z g) from
    fun x => (hasDerivAt_boundedThetaTail z g x).differentiableAt).continuous

def boundedThetaReflect (g : NativeContinuousSpace) : NativeContinuousSpace :=
  g.compContinuous ⟨fun x => -x, continuous_neg⟩

@[simp] theorem boundedThetaReflect_apply (g : NativeContinuousSpace) (x : ℝ) :
    boundedThetaReflect g x = g (-x) := rfl

theorem norm_boundedThetaReflect_le (g : NativeContinuousSpace) :
    ‖boundedThetaReflect g‖ ≤ ‖g‖ := g.norm_compContinuous_le _

theorem boundedThetaTail_reflection {z : ℂ} {g : NativeContinuousSpace}
    (hzero : boundedThetaMoment z g = 0) (x : ℝ) :
    boundedThetaTail z g x = -boundedThetaTail (-z) (boundedThetaReflect g) (-x) := by
  have hI : (∫ y in Iic x, flatCharDensity z y*g y) =
      ∫ y in Ioi (-x), flatCharDensity (-z) y*boundedThetaReflect g y := by
    rw [← integral_comp_neg_Iic x
      (fun y => flatCharDensity (-z) y*boundedThetaReflect g y)]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [flatCharDensity_reflection]
    simp only [boundedThetaReflect_apply, neg_neg]
  have he : Complex.exp (-(I*(-z))*((-x : ℝ) : ℂ)) =
      Complex.exp (-(I*z)*(x : ℂ)) := by congr 1; push_cast; ring
  rw [boundedThetaTail, boundedThetaTail_integral_split, hzero, zero_sub, hI,
    boundedThetaTail, he, normalized_reflection]
  ring

theorem norm_boundedThetaTail_left_le {z : ℂ} {g : NativeContinuousSpace}
    (hzero : boundedThetaMoment z g = 0) (x : ℝ) :
    ‖boundedThetaTail z g x‖ ≤ ‖g‖*forcedTailMass (-z) (-x) := by
  rw [boundedThetaTail_reflection hzero, norm_neg]
  exact (norm_boundedThetaTail_le _ _ _).trans
    (mul_le_mul_of_nonneg_right (norm_boundedThetaReflect_le g) (forcedTailMass_nonneg _ _))

theorem tendsto_boundedThetaTail_atBot {z : ℂ} {g : NativeContinuousSpace}
    (hzero : boundedThetaMoment z g = 0) :
    Tendsto (boundedThetaTail z g) atBot (𝓝 0) := by
  have h := ((tendsto_boundedThetaTail_atTop (-z) (boundedThetaReflect g)).comp
    tendsto_neg_atBot_atTop).neg
  simp only [neg_zero] at h
  exact h.congr fun x => (boundedThetaTail_reflection hzero x).symm

theorem forcedTailMass_antitone (z : ℂ) : Antitone (forcedTailMass z) := by
  intro x y hxy
  apply setIntegral_mono_on (integrable_sourceRatio_tilt (-z.im) y).integrableOn
    (integrable_sourceRatio_tilt (-z.im) x).integrableOn measurableSet_Ioi
  intro h hh
  exact mul_le_mul_of_nonneg_right (sourceRatio_antitone_all ⟨h, hh.le⟩ hxy)
    (Real.exp_pos _).le

theorem norm_boundedThetaTail_global {z : ℂ} {g : NativeContinuousSpace}
    (hzero : boundedThetaMoment z g = 0) (x : ℝ) :
    ‖boundedThetaTail z g x‖ ≤ ‖g‖*(forcedTailMass z 0+forcedTailMass (-z) 0) := by
  by_cases hx : 0 ≤ x
  · exact (norm_boundedThetaTail_le z g x).trans (mul_le_mul_of_nonneg_left
      ((forcedTailMass_antitone z hx).trans
        (le_add_of_nonneg_right (forcedTailMass_nonneg (-z) 0))) (norm_nonneg g))
  · have hx' : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
    exact (norm_boundedThetaTail_left_le hzero x).trans (mul_le_mul_of_nonneg_left
      ((forcedTailMass_antitone (-z) hx').trans
        (le_add_of_nonneg_left (forcedTailMass_nonneg z 0))) (norm_nonneg g))

end RHTower.PaperThetaEndpoint
