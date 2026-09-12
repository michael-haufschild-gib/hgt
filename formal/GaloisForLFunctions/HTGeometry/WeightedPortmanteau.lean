import GaloisForLFunctions.HTGeometry.CompactMomentDeterminacy
import Mathlib.Probability.Moments.Tilted
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Weighted continuity sets under weak convergence

A continuous positive weight can be absorbed into an exponential tilt of a probability measure.
Weak convergence is preserved by this tilt: both its normalizing integral and every tilted test
integral are quotients of bounded-continuous test integrals.  Portmanteau can then be applied to a
sharp continuity set.  Multiplying the normalizer back gives convergence of the original weighted
set integrals.

This is the useful bridge between compact weak convergence and sharp truncated Tauberian sums.
-/

open MeasureTheory Filter Set Topology
open scoped BoundedContinuousFunction NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Exponential of a continuous real function on a compact space, bundled as a bounded-continuous
function. -/
def continuousExpWeight (q : C(X, ℝ)) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Real.exp (q x), Real.continuous_exp.comp q.continuous⟩

theorem integrable_continuousExpWeight (μ : ProbabilityMeasure X) (q : C(X, ℝ)) :
    Integrable (fun x => Real.exp (q x)) (μ : Measure X) :=
  BoundedContinuousFunction.integrable (μ : Measure X) (continuousExpWeight q)

/-- Probability measure obtained by continuously exponentially tilting a probability measure. -/
def continuousTiltProbability (μ : ProbabilityMeasure X) (q : C(X, ℝ)) :
    ProbabilityMeasure X :=
  ⟨(μ : Measure X).tilted q,
    isProbabilityMeasure_tilted (integrable_continuousExpWeight μ q)⟩

@[simp] theorem continuousTiltProbability_toMeasure
    (μ : ProbabilityMeasure X) (q : C(X, ℝ)) :
    ((continuousTiltProbability μ q : ProbabilityMeasure X) : Measure X) =
      (μ : Measure X).tilted q := rfl

/-- Weak convergence is preserved by a fixed continuous exponential tilt on a compact space. -/
theorem tendsto_continuousTiltProbability {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) (q : C(X, ℝ)) :
    Tendsto (fun i => continuousTiltProbability (μs i) q) l
      (𝓝 (continuousTiltProbability μ q)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have htest := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
  let eq : X →ᵇ ℝ := continuousExpWeight q
  let eqg : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Real.exp (q x) * g x,
      (Real.continuous_exp.comp q.continuous).mul g.continuous⟩
  have hden := htest eq
  have hnum := htest eqg
  have hden_ne : (∫ x, eq x ∂(μ : Measure X)) ≠ 0 :=
    (integral_exp_pos (integrable_continuousExpWeight μ q)).ne'
  have hquot := hnum.div hden hden_ne
  have hform : ∀ ν : ProbabilityMeasure X,
      (∫ x, g x ∂(continuousTiltProbability ν q : Measure X)) =
        (∫ x, eqg x ∂(ν : Measure X)) / (∫ x, eq x ∂(ν : Measure X)) := by
    intro ν
    rw [continuousTiltProbability_toMeasure, integral_tilted]
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards with x
    simp only [eq, eqg, continuousExpWeight,
      BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk, smul_eq_mul]
    ring
  change Tendsto
    (fun i => (∫ x, eqg x ∂(μs i : Measure X)) /
      (∫ x, eq x ∂(μs i : Measure X))) l
    (𝓝 ((∫ x, eqg x ∂(μ : Measure X)) /
      (∫ x, eq x ∂(μ : Measure X)))) at hquot
  simpa only [hform] using hquot

/-- Weighted Portmanteau theorem for a sharp continuity set.  The integrand is a continuous
strictly positive weight `exp q`; no continuity of the indicator is required. -/
theorem tendsto_setIntegral_exp_of_null_frontier
    [PseudoMetricSpace X] [BorelSpace X] [HasOuterApproxClosed X]
    {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) (q : C(X, ℝ))
    {E : Set X} (hE : MeasurableSet E)
    (hfrontier : (μ : Measure X) (frontier E) = 0) :
    Tendsto (fun i => ∫ x in E, Real.exp (q x) ∂(μs i : Measure X)) l
      (𝓝 (∫ x in E, Real.exp (q x) ∂(μ : Measure X))) := by
  have htilt := tendsto_continuousTiltProbability hμ q
  have hfrontierTilt :
      ((continuousTiltProbability μ q : ProbabilityMeasure X) : Measure X) (frontier E) = 0 := by
    exact tilted_absolutelyContinuous (μ : Measure X) q hfrontier
  have hset := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    htilt (by simpa using hfrontierTilt)
  have hsetReal : Tendsto
      (fun i => ((↑) : ℝ≥0 → ℝ) ((continuousTiltProbability (μs i) q) E)) l
      (𝓝 (((↑) : ℝ≥0 → ℝ) ((continuousTiltProbability μ q) E))) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hset
  have hden := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
    (continuousExpWeight q)
  have hprod := hden.mul hsetReal
  have hform : ∀ ν : ProbabilityMeasure X,
      (∫ x in E, Real.exp (q x) ∂(ν : Measure X)) =
        (∫ x, Real.exp (q x) ∂(ν : Measure X)) *
          (((↑) : ℝ≥0 → ℝ) ((continuousTiltProbability ν q) E)) := by
    intro ν
    have h := setIntegral_tilted' (μ := (ν : Measure X)) q (fun _ => (1 : ℝ)) hE
    rw [← continuousTiltProbability_toMeasure] at h
    have hZ : (∫ x, Real.exp (q x) ∂(ν : Measure X)) ≠ 0 :=
      (integral_exp_pos (integrable_continuousExpWeight ν q)).ne'
    rw [setIntegral_one_eq_measureReal,
      ProbabilityMeasure.measureReal_eq_coe_coeFn] at h
    simp only [smul_eq_mul, mul_one] at h
    change (((↑) : ℝ≥0 → ℝ) ((continuousTiltProbability ν q) E)) =
      ∫ x, Real.exp (q x) / (∫ x, Real.exp (q x) ∂(ν : Measure X))
        ∂((ν : Measure X).restrict E) at h
    rw [integral_div] at h
    have hdiv : (∫ x in E, Real.exp (q x) ∂(ν : Measure X)) /
        (∫ x, Real.exp (q x) ∂(ν : Measure X)) =
          (((↑) : ℝ≥0 → ℝ) ((continuousTiltProbability ν q) E)) := by
      rw [← h]
    field_simp [hZ] at hdiv
    exact hdiv
  simpa only [continuousExpWeight, BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk, hform] using hprod

end

end GaloisForLFunctions.HTGeometry
