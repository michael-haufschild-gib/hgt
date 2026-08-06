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
open scoped Topology BigOperators

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


/-- The iterated divided difference at a point. -/
def analyticSlopeIter (f : ℂ → ℂ) (c : ℂ) : ℕ → (ℂ → ℂ)
  | 0 => f
  | n + 1 => analyticSlope (analyticSlopeIter f c n) c

@[simp] theorem analyticSlopeIter_zero (f : ℂ → ℂ) (c : ℂ) : analyticSlopeIter f c 0 = f := rfl

@[simp] theorem analyticSlopeIter_succ (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    analyticSlopeIter f c (n + 1) = analyticSlope (analyticSlopeIter f c n) c := rfl

theorem analyticAt_analyticSlopeIter {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) (n : ℕ) :
    AnalyticAt ℂ (analyticSlopeIter f c n) c := by
  induction n with
  | zero => simpa using hf
  | succ n ih => exact analyticAt_analyticSlope ih

/-- **Taylor expansion to any order with an analytic remainder.**  The coefficients are the values
of the iterated divided differences at the base point. -/
theorem eq_taylor_add_pow_mul (f : ℂ → ℂ) (c z : ℂ) (n : ℕ) :
    f z = (∑ k ∈ Finset.range n, (z - c) ^ k * analyticSlopeIter f c k c)
      + (z - c) ^ n * analyticSlopeIter f c n z := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := sub_eq_mul_analyticSlope (analyticSlopeIter f c n) c z
      have hval : analyticSlopeIter f c n z
          = analyticSlopeIter f c n c + (z - c) * analyticSlopeIter f c (n + 1) z := by
        rw [analyticSlopeIter_succ]
        linear_combination hstep
      rw [Finset.sum_range_succ]
      rw [hval] at ih
      linear_combination ih


/-- Away from the base point the iterated divided difference is the explicit Taylor remainder. -/
theorem analyticSlopeIter_of_ne {f : ℂ → ℂ} {c z : ℂ} (h : z ≠ c) (n : ℕ) :
    analyticSlopeIter f c n z
      = (f z - ∑ k ∈ Finset.range n, (z - c) ^ k * analyticSlopeIter f c k c) / (z - c) ^ n := by
  have hz : (z - c) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr h)
  have ht := eq_taylor_add_pow_mul f c z n
  rw [eq_div_iff hz]
  linear_combination -ht


theorem analyticSlopeIter_succ' (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    analyticSlopeIter f c (n + 1) = analyticSlopeIter (analyticSlope f c) c n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [analyticSlopeIter_succ, ih, analyticSlopeIter_succ]

/-- The divided difference is additive. -/
theorem analyticSlope_add {f g : ℂ → ℂ} {c : ℂ} (hf : DifferentiableAt ℂ f c)
    (hg : DifferentiableAt ℂ g c) :
    analyticSlope (fun z => f z + g z) c = fun z => analyticSlope f c z + analyticSlope g c z := by
  funext z
  rcases eq_or_ne z c with rfl | hz
  · rw [analyticSlope_self, analyticSlope_self, analyticSlope_self]
    exact (hf.hasDerivAt.add hg.hasDerivAt).deriv
  · have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz
    rw [analyticSlope_of_ne hz, analyticSlope_of_ne hz, analyticSlope_of_ne hz]
    field_simp
    ring

/-- **Peeling one factor.**  Adding `(z - c)` times a function shifts the divided difference by that
function. -/
theorem analyticSlope_add_sub_mul {B C : ℂ → ℂ} {c : ℂ} (hB : DifferentiableAt ℂ B c)
    (hC : DifferentiableAt ℂ C c) :
    analyticSlope (fun z => B z + (z - c) * C z) c = fun z => analyticSlope B c z + C z := by
  have h1 : HasDerivAt (fun z : ℂ => z - c) 1 c := (hasDerivAt_id c).sub_const c
  funext z
  rcases eq_or_ne z c with rfl | hz
  · have hA : HasDerivAt (fun w : ℂ => B w + (w - z) * C w)
        (deriv B z + (1 * C z + (z - z) * deriv C z)) z :=
      hB.hasDerivAt.add (h1.mul hC.hasDerivAt)
    rw [analyticSlope_self, analyticSlope_self]
    rw [hA.deriv]
    ring
  · have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz
    rw [analyticSlope_of_ne hz, analyticSlope_of_ne hz]
    field_simp
    ring

theorem analyticSlopeIter_add {f g : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c)
    (hg : AnalyticAt ℂ g c) (n : ℕ) :
    analyticSlopeIter (fun z => f z + g z) c n
      = fun z => analyticSlopeIter f c n z + analyticSlopeIter g c n z := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
      rw [analyticSlopeIter_succ', analyticSlope_add hf.differentiableAt hg.differentiableAt,
        ih (analyticAt_analyticSlope hf) (analyticAt_analyticSlope hg),
        analyticSlopeIter_succ', analyticSlopeIter_succ']

/-- **Peeling one factor, iterated.** -/
theorem analyticSlopeIter_add_sub_mul {B C : ℂ → ℂ} {c : ℂ} (hB : AnalyticAt ℂ B c)
    (hC : AnalyticAt ℂ C c) (n : ℕ) :
    analyticSlopeIter (fun z => B z + (z - c) * C z) c (n + 1)
      = fun z => analyticSlopeIter B c (n + 1) z + analyticSlopeIter C c n z := by
  rw [analyticSlopeIter_succ', analyticSlope_add_sub_mul hB.differentiableAt hC.differentiableAt,
    analyticSlopeIter_add (analyticAt_analyticSlope hB) hC n, analyticSlopeIter_succ']

end

end GaloisForLFunctions.HTGeometry
