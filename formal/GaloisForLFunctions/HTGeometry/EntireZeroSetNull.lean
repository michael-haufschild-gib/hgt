import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Compactness.Lindelof

/-!
# The zero set of a nonzero entire function is countable, and its real trace is null

The zeros of a function analytic on a preconnected open set are isolated unless the function
vanishes identically, so the zero set carries the discrete topology.  In a second-countable space
every set is Lindelöf, and a discrete Lindelöf set is countable.  Restricting to the real axis, the
real zero set of a nonzero entire function is therefore countable, hence Lebesgue-null.

This is the measure-theoretic input to Fourier-multiplier arguments whose symbol is an entire
function.

* `HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd`;
* `HTGeometry.volume_real_setOf_eq_zero_eq_zero`.
-/

open Set Filter Topology MeasureTheory

namespace HTGeometry

/-- **Isolated zeros.**  A function analytic on a preconnected open set and not identically zero has
a discrete zero set. -/
theorem discreteTopology_setOf_eq_zero {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (h0 : ∃ z, f z ≠ 0) : DiscreteTopology {z : ℂ | f z = 0} := by
  rw [discreteTopology_subtype_iff]
  intro z₀ _
  have hne : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
    rcases (hf z₀ (Set.mem_univ z₀)).eventually_eq_zero_or_eventually_ne_zero with hev | hev
    · exfalso
      obtain ⟨w, hw⟩ := h0
      exact hw (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ z₀) hev (Set.mem_univ w))
    · exact hev
  rw [← Filter.empty_mem_iff_bot]
  refine Filter.mem_of_superset
    (Filter.inter_mem_inf hne (Filter.mem_principal_self {z : ℂ | f z = 0})) ?_
  rintro z ⟨hz1, hz2⟩
  exact absurd hz2 hz1

/-- **The zero set of a nonzero entire function is countable.** -/
theorem countable_setOf_eq_zero_of_analyticOnNhd {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (h0 : ∃ z, f z ≠ 0) : {z : ℂ | f z = 0}.Countable :=
  IsLindelof.countable IsLindelof.of_coe (discreteTopology_setOf_eq_zero hf h0)

/-- **The real zero set of a nonzero entire function is Lebesgue-null.** -/
theorem volume_real_setOf_eq_zero_eq_zero {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (h0 : ∃ z, f z ≠ 0) : volume {x : ℝ | f (x : ℂ) = 0} = 0 := by
  have hpre : {x : ℝ | f (x : ℂ) = 0} = (fun x : ℝ => (x : ℂ)) ⁻¹' {z : ℂ | f z = 0} := rfl
  rw [hpre]
  exact ((countable_setOf_eq_zero_of_analyticOnNhd hf h0).preimage
    Complex.ofReal_injective).measure_zero volume

end HTGeometry
