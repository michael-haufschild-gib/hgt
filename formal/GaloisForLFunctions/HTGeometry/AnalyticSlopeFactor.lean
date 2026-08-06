import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Dividing out a root of an analytic function

The divided difference `(f z - f c)/(z - c)`, extended across `c` by `f'(c)`, is again analytic at
`c`: it is continuous there by the definition of the derivative and holomorphic on a punctured
neighbourhood, so the removable-singularity theorem applies.

Iterating gives the second-order Taylor expansion with an analytic remainder,

```text
f z = f c + (z - c) f'(c) + (z - c)^2 g z,
```

which is the form needed to subtract the singular part of a Mellin integrand.
-/

open Complex Filter Metric
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The divided difference `(f z - f c)/(z - c)`, extended across `c` by the derivative. -/
def analyticSlope (f : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  fun z => if z = c then deriv f c else (f z - f c) / (z - c)

@[simp] theorem analyticSlope_self (f : ℂ → ℂ) (c : ℂ) : analyticSlope f c c = deriv f c := by
  simp [analyticSlope]

theorem analyticSlope_of_ne {f : ℂ → ℂ} {c z : ℂ} (h : z ≠ c) :
    analyticSlope f c z = (f z - f c) / (z - c) := by
  simp [analyticSlope, h]

/-- **Dividing out a root.**  The value of `f` is recovered from its divided difference. -/
theorem sub_eq_mul_analyticSlope (f : ℂ → ℂ) (c z : ℂ) :
    f z - f c = (z - c) * analyticSlope f c z := by
  rcases eq_or_ne z c with rfl | h
  · simp
  · rw [analyticSlope_of_ne h, mul_div_cancel₀ _ (sub_ne_zero.mpr h)]

theorem analyticSlope_eventuallyEq (f : ℂ → ℂ) (c : ℂ) :
    analyticSlope f c =ᶠ[𝓝[≠] c] slope f c := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [analyticSlope_of_ne hz, slope_def_field]

theorem continuousAt_analyticSlope {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    ContinuousAt (analyticSlope f c) c := by
  have hderiv : HasDerivAt f (deriv f c) c := hf.differentiableAt.hasDerivAt
  have hslope : Tendsto (slope f c) (𝓝[≠] c) (𝓝 (deriv f c)) :=
    hasDerivAt_iff_tendsto_slope.mp hderiv
  have h1 : Tendsto (analyticSlope f c) (𝓝[≠] c) (𝓝 (analyticSlope f c c)) := by
    rw [analyticSlope_self]
    exact hslope.congr' (analyticSlope_eventuallyEq f c).symm
  have h2 : Tendsto (analyticSlope f c) (pure c) (𝓝 (analyticSlope f c c)) :=
    tendsto_pure_nhds _ _
  have h := h1.sup h2
  rw [nhdsNE_sup_pure] at h
  exact h

theorem eventually_differentiableAt_analyticSlope {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ (analyticSlope f c) z := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds hf.eventually_analyticAt] with z hz hza
  have hzc : z ≠ c := hz
  have hUopen : IsOpen ({w : ℂ | AnalyticAt ℂ f w} ∩ {c}ᶜ) := by
    refine IsOpen.inter ?_ isOpen_compl_singleton
    exact isOpen_iff_eventually.mpr fun w hw => hw.eventually_analyticAt
  have hzU : z ∈ {w : ℂ | AnalyticAt ℂ f w} ∩ {c}ᶜ := ⟨hza, hz⟩
  have heq : analyticSlope f c =ᶠ[𝓝 z] fun w => (f w - f c) / (w - c) := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    exact analyticSlope_of_ne hw.2
  refine (Filter.EventuallyEq.differentiableAt_iff heq).mpr ?_
  exact (hza.differentiableAt.sub_const _).div
    ((differentiableAt_id).sub_const c) (sub_ne_zero.mpr hzc)

/-- **The divided difference of an analytic function is analytic.** -/
theorem analyticAt_analyticSlope {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    AnalyticAt ℂ (analyticSlope f c) c :=
  Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    (eventually_differentiableAt_analyticSlope hf) (continuousAt_analyticSlope hf)

/-- **Second-order Taylor expansion with an analytic remainder.** -/
theorem eq_taylor_two_add_sq_mul (f : ℂ → ℂ) (c z : ℂ) :
    f z = f c + (z - c) * deriv f c
      + (z - c) ^ 2 * analyticSlope (analyticSlope f c) c z := by
  have h1 := sub_eq_mul_analyticSlope f c z
  have h2 := sub_eq_mul_analyticSlope (analyticSlope f c) c z
  rw [analyticSlope_self] at h2
  have h3 : analyticSlope f c z
      = deriv f c + (z - c) * analyticSlope (analyticSlope f c) c z := by
    linear_combination h2
  rw [h3] at h1
  linear_combination h1

theorem analyticAt_analyticSlope_two {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    AnalyticAt ℂ (analyticSlope (analyticSlope f c) c) c :=
  analyticAt_analyticSlope (analyticAt_analyticSlope hf)

/-- Away from the base point the second divided difference is the explicit Taylor remainder. -/
theorem analyticSlope_two_of_ne {f : ℂ → ℂ} {c z : ℂ} (h : z ≠ c) :
    analyticSlope (analyticSlope f c) c z
      = (f z - f c - (z - c) * deriv f c) / (z - c) ^ 2 := by
  have hz : (z - c) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr h)
  have ht := eq_taylor_two_add_sq_mul f c z
  rw [eq_div_iff hz]
  linear_combination -ht

end

end GaloisForLFunctions.HTGeometry
