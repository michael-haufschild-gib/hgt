import GaloisForLFunctions.HTGeometry.MomentWeakConvergence

/-!
# Portmanteau bounds from explicit ramps

Weak convergence controls masses through continuous test functions that dominate indicators.  The
cheapest such functions are clamped ramps

`ramp a b x = max 0 (min 1 ((x - a)/(b - a)))`,

which are continuous, take values in `[0,1]`, vanish below `a` and equal one above `b`.  A ramp
dominates the indicator of `[b, ∞)` and is dominated by the indicator of `(a, ∞)`, and the
trapezoid `min (ramp a b) (1 - ramp c d)` does the same for a bounded window.

Hence: the mass of a closed set is at most the integral of any dominating ramp, and the limit of
those integrals is the integral against the limit source.  That is all the portmanteau input a
hard-edge collapse statement or an isolated-atom statement needs.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The clamped ramp -/

/-- The clamped ramp from `a` to `b`. -/
def ramp (a b x : ℝ) : ℝ := max 0 (min 1 ((x - a) / (b - a)))

theorem continuous_ramp (a b : ℝ) : Continuous (ramp a b) := by
  unfold ramp
  fun_prop

theorem ramp_nonneg (a b x : ℝ) : 0 ≤ ramp a b x := le_max_left _ _

theorem ramp_le_one (a b x : ℝ) : ramp a b x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem ramp_eq_zero_of_le {a b x : ℝ} (hab : a < b) (hx : x ≤ a) : ramp a b x = 0 := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hnum : x - a ≤ 0 := by linarith
  have hdiv : (x - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hba.le
  rw [ramp, max_eq_left]
  exact le_trans (min_le_right _ _) hdiv

theorem ramp_eq_one_of_le {a b x : ℝ} (hab : a < b) (hx : b ≤ x) : ramp a b x = 1 := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hge : (1 : ℝ) ≤ (x - a) / (b - a) := by
    rw [le_div_iff₀ hba]
    linarith
  rw [ramp, min_eq_left hge, max_eq_right zero_le_one]

/-- The trapezoid: one on `[b, c]`, zero outside `(a, d)`. -/
def trapezoid (a b c d x : ℝ) : ℝ := min (ramp a b x) (1 - ramp c d x)

theorem continuous_trapezoid (a b c d : ℝ) : Continuous (trapezoid a b c d) :=
  (continuous_ramp a b).min (continuous_const.sub (continuous_ramp c d))

theorem trapezoid_nonneg {a b c d x : ℝ} (hcd : c < d) (hx : x ≤ c) :
    0 ≤ trapezoid a b c d x := by
  refine le_min (ramp_nonneg _ _ _) ?_
  have : ramp c d x = 0 := ramp_eq_zero_of_le hcd hx
  rw [this]
  norm_num

theorem trapezoid_le_one (a b c d x : ℝ) : trapezoid a b c d x ≤ 1 :=
  le_trans (min_le_left _ _) (ramp_le_one _ _ _)

theorem trapezoid_eq_one {a b c d x : ℝ} (hab : a < b) (hcd : c < d)
    (hxb : b ≤ x) (hxc : x ≤ c) : trapezoid a b c d x = 1 := by
  rw [trapezoid, ramp_eq_one_of_le hab hxb, ramp_eq_zero_of_le hcd hxc]
  norm_num

/-! ## The portmanteau bound -/

/-- The mass of a measurable set is at most the integral of any nonnegative continuous function
dominating its indicator. -/
theorem measureReal_le_integral {μ : Measure HausdorffSourceSpace} [IsFiniteMeasure μ]
    {A : Set HausdorffSourceSpace} (hA : MeasurableSet A) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hnn : ∀ y : HausdorffSourceSpace, 0 ≤ f (y : ℝ))
    (hle : ∀ y ∈ A, (1 : ℝ) ≤ f (y : ℝ)) :
    (μ A).toReal ≤ ∫ y : HausdorffSourceSpace, f (y : ℝ) ∂μ := by
  have hfi := integrable_of_continuousOn hf μ
  have hsetle : ∫ y in A, (1 : ℝ) ∂μ ≤ ∫ y in A, f (y : ℝ) ∂μ := by
    refine setIntegral_mono_on (integrableOn_const (measure_ne_top μ A))
      (hfi.integrableOn) hA ?_
    intro y hy
    exact hle y hy
  have hwhole : ∫ y in A, f (y : ℝ) ∂μ ≤ ∫ y : HausdorffSourceSpace, f (y : ℝ) ∂μ :=
    setIntegral_le_integral hfi (Filter.Eventually.of_forall hnn)
  have hone : ∫ y in A, (1 : ℝ) ∂μ = (μ A).toReal := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  linarith [hone ▸ hsetle, hwhole]

/-- **The portmanteau upper bound.**  If the integrals against a dominating ramp converge, the
masses are eventually below the limit integral, up to any margin. -/
theorem limsup_measureReal_le {σ : ℕ → Measure HausdorffSourceSpace}
    {τ : Measure HausdorffSourceSpace} [∀ n, IsFiniteMeasure (σ n)] [IsFiniteMeasure τ]
    {A : Set HausdorffSourceSpace} (hA : MeasurableSet A) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hnn : ∀ y : HausdorffSourceSpace, 0 ≤ f (y : ℝ))
    (hle : ∀ y ∈ A, (1 : ℝ) ≤ f (y : ℝ))
    (hconv : Tendsto (fun n => ∫ y : HausdorffSourceSpace, f (y : ℝ) ∂(σ n)) atTop
      (𝓝 (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ((σ n) A).toReal ≤ (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ) + ε := by
  have hnear : ∀ᶠ n in atTop,
      (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂(σ n))
        < (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ) + ε := by
    have := hconv.eventually (eventually_lt_nhds (by linarith :
      (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ)
        < (∫ y : HausdorffSourceSpace, f (y : ℝ) ∂τ) + ε))
    exact this
  filter_upwards [hnear] with n hn
  exact le_trans (measureReal_le_integral hA hf hnn hle) hn.le

end GaloisForLFunctions.HTGeometry
