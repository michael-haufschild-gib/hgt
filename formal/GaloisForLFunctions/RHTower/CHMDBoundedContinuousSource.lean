import GaloisForLFunctions.RHTower.CHMDBVUniformConvergence
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Bounded continuous representatives commute with graph averaging

The source projection and the bounded-continuous-to-L2 map both commute with
Bochner integration. Literal source identities can therefore be checked by
bounded continuous evaluation, without a new pointwise L2 representative.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace RHTower.CHMDDoobGraph
open GaloisForLFunctions.HTGeometry

def bvContinuousFunction (f : ℝ → ℝ) (hc : Continuous f)
    (hv : BoundedVariationOn f univ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hc
    (‖f 0‖ + (eVariationOn f univ).toReal) (norm_le_of_boundedVariation_univ hv)

@[simp] theorem bvContinuousFunction_apply (f : ℝ → ℝ) (hc : Continuous f)
    (hv : BoundedVariationOn f univ) (x : ℝ) : bvContinuousFunction f hc hv x = f x := rfl

theorem continuous_bvContinuousFunction_of_common_compact {v : ℝ → ℝ → ℝ}
    (hc : ∀ t, Continuous (v t)) (hv : ∀ t, BoundedVariationOn (v t) univ)
    (hjoint : Continuous (fun p : ℝ × ℝ => v p.1 p.2))
    {K : Set ℝ} (hK : IsCompact K) (hz : ∀ t x, x ∉ K → v t x = 0) :
    Continuous (fun t => bvContinuousFunction (v t) (hc t) (hv t)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply continuous_iff_continuousAt.mpr
  intro t
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
  change TendstoUniformly v (v t) (𝓝 t)
  have hrestricted : Continuous (fun p : ℝ × K => v p.1 p.2) :=
    hjoint.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have huK := Continuous.tendstoUniformly (fun a (x : K) => v a x) hrestricted t
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp huK) ε hε] with a ha
  intro x
  by_cases hx : x ∈ K
  · exact ha ⟨x, hx⟩
  · simpa only [hz t x hx, hz a x hx, dist_self] using hε

theorem sourceMap_bvLift_eq_bcfToLp (f : ℝ → ℝ) (hc : Continuous f)
    (hv : BoundedVariationOn f univ) :
    sourceMap (bvLift f hv) =
      BoundedContinuousFunction.toLp 2 massMeasure ℝ (bvContinuousFunction f hc hv) := by
  apply Lp.ext
  exact (bvLift_source f hv).trans
    (BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := massMeasure) (𝕜 := ℝ)
      (bvContinuousFunction f hc hv)).symm

theorem boundedContinuous_integral_apply {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : α → (ℝ →ᵇ ℝ)} (hF : Integrable F μ) (x : ℝ) :
    (∫ a, F a ∂μ) x = ∫ a, F a x ∂μ :=
  ((BoundedContinuousFunction.evalCLM ℝ x).integral_comp_comm hF).symm

theorem sourceMap_integral_boundedContinuous {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : α → SourceGraph} {F : α → (ℝ →ᵇ ℝ)}
    (hp : Integrable p μ) (hF : Integrable F μ)
    (he : ∀ᵐ a ∂μ, sourceMap (p a) = BoundedContinuousFunction.toLp 2 massMeasure ℝ (F a)) :
    sourceMap (∫ a, p a ∂μ) = BoundedContinuousFunction.toLp 2 massMeasure ℝ (∫ a, F a ∂μ) := by
  rw [← sourceMap.integral_comp_comm hp,
    ← (BoundedContinuousFunction.toLp 2 massMeasure ℝ).integral_comp_comm hF]
  exact integral_congr_ae he

end RHTower.CHMDDoobGraph
