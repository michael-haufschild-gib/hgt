import GaloisForLFunctions.HTGeometry.EinastoShapeSourceThreshold

/-!
# Noncommuting shape and central-radius limits in the actual Einasto source

The source threshold from arXiv:2608.23600 is not merely a discontinuous
parameterization of the density. Density, enclosed mass factor, metric, and
the actual positive-radius source vary continuously with shape. Nevertheless,
approaching the Gaussian shape after taking the central limit gives a different
answer from approaching that shape first. Both iterated limits are proved, and
their nonzero difference is independent of the algebraic-sign discrepancy.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem einastoProfilePower_shapeRadius_continuous (l : ℝ) :
    Continuous (fun p : ℝ × ℝ => einastoProfilePower l p.1 p.2) := by
  exact (continuous_snd.div_const (exp l)).rpow (Real.continuous_exp.comp continuous_fst.neg)
    (fun p => Or.inr (exp_pos (-p.1)))

/-- Joint shape-radius continuity includes the integration endpoint at the center. -/
theorem einastoDensity_shapeRadius_continuous (d l : ℝ) :
    Continuous (fun p : ℝ × ℝ => einastoDensity d l p.1 p.2) := by
  exact continuous_const.mul (Real.continuous_exp.comp (einastoProfilePower_shapeRadius_continuous l).neg)

/-- The shape limit passes through the actual enclosed-density integral. -/
theorem einastoCore_shapeRadius_continuous (d l : ℝ) :
    Continuous (fun p : ℝ × ℝ => einastoCore d l p.1 p.2) := by
  unfold einastoCore
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_snd.pow 2).mul ((einastoDensity_shapeRadius_continuous d l).comp
    (continuous_fst.fst.prodMk (continuous_fst.snd.mul continuous_snd)))

theorem einastoMetric_shapeRadius_continuous (d l : ℝ) :
    Continuous (fun p : ℝ × ℝ => einastoMetric d l p.1 p.2) := by
  simp_rw [einastoMetric_core]
  exact continuous_const.sub ((continuous_const.mul (continuous_snd.pow 2)).mul
    (einastoCore_shapeRadius_continuous d l))

theorem einastoShapeRicci_shapeRadius_continuous (d l : ℝ) :
    Continuous (fun p : ℝ × ℝ => einastoShapeRicci d l p.1 p.2) := by
  have hD := einastoDensity_shapeRadius_continuous d l
  have hU := einastoProfilePower_shapeRadius_continuous l
  unfold einastoShapeRicci
  fun_prop

theorem einastoShapeSourceFactor_shapeRadius_continuous (d l : ℝ) :
    Continuous (fun p : ℝ × ℝ => einastoShapeSourceFactor d l p.1 p.2) := by
  have hD := einastoDensity_shapeRadius_continuous d l
  have hU := einastoProfilePower_shapeRadius_continuous l
  have hf := einastoMetric_shapeRadius_continuous d l
  have hC := einastoCore_shapeRadius_continuous d l
  unfold einastoShapeSourceFactor
  dsimp only
  fun_prop

theorem einastoShapeSourceDefect_shapeRadius_continuous (d l σ : ℝ) :
    Continuous (fun p : ℝ × ℝ => einastoShapeSourceDefect d l p.1 σ p.2) :=
  (continuous_const.mul ((einastoShapeRicci_shapeRadius_continuous d l).pow 2)).div_const (16 * Real.pi)

/-- Despite the central jump, the actual source is continuous in shape at every positive radius. -/
theorem einastoShapeSource_shape_continuous (d l σ t : ℝ) :
    Continuous (fun a => quadraticRadialSource σ (einastoMetric d l a) (exp t)) := by
  simp_rw [einastoShapeSource_exp_decomposition]
  have hF := (einastoShapeSourceFactor_shapeRadius_continuous d l).comp
    (continuous_id.prodMk (continuous_const (y := exp t)))
  have hD := (einastoShapeSourceDefect_shapeRadius_continuous d l σ).comp
    (continuous_id.prodMk (continuous_const (y := exp t)))
  fun_prop

/-- A family of shapes approaching the regularity boundary from the regular side. -/
def einastoSuperGaussianShape (s : ℝ) : ℝ := -log (2 + exp s)

theorem einastoSuperGaussianShape_limit :
    Tendsto einastoSuperGaussianShape atBot (𝓝 (-log 2)) := by
  have h : Tendsto (fun s : ℝ => 2 + exp s) atBot (𝓝 2) := by
    simpa only [add_zero] using tendsto_exp_atBot.const_add 2
  exact ((continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp h).neg

/-- At any fixed positive radius, the actual super-Gaussian sources approach the Gaussian source. -/
theorem einastoShapeSource_gaussian_shape_limit (d l σ t : ℝ) :
    Tendsto (fun s => quadraticRadialSource σ (einastoMetric d l (einastoSuperGaussianShape s)) (exp t)) atBot
      (𝓝 (quadraticRadialSource σ (einastoMetric d l (-log 2)) (exp t))) :=
  (einastoShapeSource_shape_continuous d l σ t).continuousAt.tendsto.comp einastoSuperGaussianShape_limit

/-- The two orders of taking the shape and central-radius limits have strictly different values. -/
theorem einastoShapeSource_noncommuting_limits (d l σ : ℝ) :
    ∃ A B : ℝ,
      (∀ s : ℝ, Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l (einastoSuperGaussianShape s)) (exp t)) atBot (𝓝 A)) ∧
      (∀ t : ℝ, Tendsto (fun s => quadraticRadialSource σ (einastoMetric d l (einastoSuperGaussianShape s)) (exp t)) atBot
        (𝓝 (quadraticRadialSource σ (einastoMetric d l (-log 2)) (exp t)))) ∧
      Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l (-log 2)) (exp t)) atBot (𝓝 B) ∧ B < A := by
  refine ⟨64 * Real.pi * (σ - 1) * exp d ^ 2,
    -72 * exp d * exp (-2 * l) + 64 * Real.pi * (σ - 1) * exp d ^ 2,
    (fun s => einastoShapeSource_superGaussian_limit d l σ s),
    (fun t => einastoShapeSource_gaussian_shape_limit d l σ t),
    einastoShapeSource_gaussian_limit d l σ, ?_⟩
  have hp : 0 < 72 * exp d * exp (-2 * l) := by positivity
  linarith

/-- The limiting core source jumps at the Gaussian shape, even though every positive-radius source is continuous. -/
theorem einastoShapeSourceCoreValue_not_continuousAt (d l σ : ℝ) :
    ¬ContinuousAt (fun a => einastoShapeSourceCoreValue d l a σ) (-log 2) := by
  intro hc
  have hlim := hc.tendsto.comp einastoSuperGaussianShape_limit
  have he (s : ℝ) : einastoShapeSourceCoreValue d l (einastoSuperGaussianShape s) σ =
      64 * Real.pi * (σ - 1) * exp d ^ 2 := by
    have hq : exp (-einastoSuperGaussianShape s) = 2 + exp s := by
      unfold einastoSuperGaussianShape
      rw [neg_neg, exp_log (by positivity : 0 < 2 + exp s)]
    have hn : exp (-einastoSuperGaussianShape s) ≠ 2 := by
      rw [hq]
      linarith [exp_pos s]
    simp only [einastoShapeSourceCoreValue, if_neg hn, zero_add]
  have hconst : Tendsto (fun s => einastoShapeSourceCoreValue d l (einastoSuperGaussianShape s) σ) atBot
      (𝓝 (64 * Real.pi * (σ - 1) * exp d ^ 2)) := by
    simp_rw [he]
    exact tendsto_const_nhds
  have hv := tendsto_nhds_unique hlim hconst
  have hq : exp (-(-log 2)) = 2 := by rw [neg_neg, exp_log (by norm_num : (0 : ℝ) < 2)]
  simp only [einastoShapeSourceCoreValue, if_pos hq] at hv
  have hp : 0 < 72 * exp d * exp (-2 * l) := by positivity
  linarith

end GaloisForLFunctions.HTGeometry
