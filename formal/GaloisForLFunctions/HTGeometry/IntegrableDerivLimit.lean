import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A function with integrable derivative converges

If a function is differentiable on a ray and its derivative is integrable there, the function has
a limit at infinity — and the limit is not merely abstract, it is

```text
lim A = A(a) + ∫_{(a,∞)} A'.
```

The fundamental theorem of calculus turns `A(b)` into `A(a) + ∫_a^b A'`, and the improper integral
of an integrable function over a ray is the limit of its truncations, so the two statements are the
same statement.  No Cauchy-sequence argument and no completeness bookkeeping is needed beyond what
the integral already carries.

This is the mechanism by which an oscillatory solution acquires a *constant*: once a transported
amplitude is shown to move at an integrable rate, its terminal value exists and is computed by the
total transport.
-/

open MeasureTheory Filter Set

namespace GaloisForLFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **A function with integrable derivative converges, with an explicit limit.** -/
theorem tendsto_of_hasDerivAt_of_integrableOn_Ioi {A A' : ℝ → E} {a : ℝ}
    (hA : ∀ x ∈ Ici a, HasDerivAt A (A' x) x)
    (hint : IntegrableOn A' (Ioi a) volume) :
    Tendsto A atTop (nhds (A a + ∫ x in Ioi a, A' x)) := by
  have hFTC : ∀ b : ℝ, a ≤ b → A b = A a + ∫ y in a..b, A' y := by
    intro b hab
    have hderiv : ∀ x ∈ uIcc a b, HasDerivAt A (A' x) x := by
      intro x hx
      rw [uIcc_of_le hab] at hx
      exact hA x hx.1
    have hii : IntervalIntegrable A' volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        (hint.mono_set Ioc_subset_Ioi_self)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii
    linear_combination (norm := abel) -this
  have hlim : Tendsto (fun b : ℝ => ∫ y in a..b, A' y) atTop (nhds (∫ x in Ioi a, A' x)) :=
    intervalIntegral_tendsto_integral_Ioi a hint tendsto_id
  have hshift : Tendsto (fun b : ℝ => A a + ∫ y in a..b, A' y) atTop
      (nhds (A a + ∫ x in Ioi a, A' x)) := tendsto_const_nhds.add hlim
  refine hshift.congr' ?_
  filter_upwards [eventually_ge_atTop a] with b hb
  exact (hFTC b hb).symm

/-- **Uniform displacement bound.**  Every excursion of `A` beyond `a` is bounded by the total
transport, uniformly in the endpoint. -/
theorem norm_sub_le_integral_norm_of_hasDerivAt {A A' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ x ∈ Ici a, HasDerivAt A (A' x) x)
    (hint : IntegrableOn A' (Ioi a) volume) :
    ‖A b - A a‖ ≤ ∫ x in Ioi a, ‖A' x‖ := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt A (A' x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact hA x hx.1
  have hii : IntervalIntegrable A' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hint.mono_set Ioc_subset_Ioi_self)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii
  have hnorm : ‖∫ y in a..b, A' y‖ ≤ ∫ y in a..b, ‖A' y‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have hIoc : ∫ y in a..b, ‖A' y‖ = ∫ y in Ioc a b, ‖A' y‖ :=
    intervalIntegral.integral_of_le hab
  have hmono : ∫ y in Ioc a b, ‖A' y‖ ≤ ∫ y in Ioi a, ‖A' y‖ := by
    refine setIntegral_mono_set hint.norm ?_ ?_
    · filter_upwards with x using norm_nonneg _
    · exact Filter.Eventually.of_forall Ioc_subset_Ioi_self
  rw [← hFTC]
  calc ‖∫ y in a..b, A' y‖ ≤ ∫ y in a..b, ‖A' y‖ := hnorm
    _ = ∫ y in Ioc a b, ‖A' y‖ := hIoc
    _ ≤ ∫ y in Ioi a, ‖A' y‖ := hmono

/-- **Convergence from a dominating integrable rate.**  If the derivative is dominated in norm by
an integrable function, the conclusion holds without integrability of the derivative being assumed
separately. -/
theorem tendsto_of_hasDerivAt_of_norm_le {A A' : ℝ → E} {g : ℝ → ℝ} {a : ℝ}
    (hA : ∀ x ∈ Ici a, HasDerivAt A (A' x) x)
    (hmeas : AEStronglyMeasurable A' (volume.restrict (Ioi a)))
    (hg : IntegrableOn g (Ioi a) volume)
    (hle : ∀ᵐ x ∂(volume.restrict (Ioi a)), ‖A' x‖ ≤ g x) :
    ∃ L : E, Tendsto A atTop (nhds L) := by
  have hint : IntegrableOn A' (Ioi a) volume := by
    refine Integrable.mono hg hmeas ?_
    filter_upwards [hle] with x hx
    exact le_trans hx (le_abs_self _)
  exact ⟨_, tendsto_of_hasDerivAt_of_integrableOn_Ioi hA hint⟩

end GaloisForLFunctions
