/-
The concavity mean-value bridge: Jensen's inequality turning an average of `log g` into the log of a
mean value.

This is the analytic glue between the counting half of a zero-density theorem (Littlewood's lemma,
which bounds a zero count by a circle average of `log‖ξ‖`) and its analytic half (a moment / mean
value).  Concavity of `log` on `(0, ∞)` gives, for a probability average `⨍` of a function bounded in
a positive interval `[a, b]`,

  ⨍ log g ≤ log (⨍ g)          (`jensen_avg_log`),
  ⨍ log g ≤ ½ · log (⨍ g²)     (`jensen_avg_log_sq`),

the second by applying the first to `g²` and `log g = ½ log g²`.  Read on the circle
`g = ‖ξ(c + R e^{iθ})‖`, the right-hand side is a *mean square* — the second moment — so a large circle
average of `log‖ξ‖` (forced by many enclosed zeros, via `LittlewoodXi`) demands a large mean square,
which the moment bound (`SecondMoment`, `FourthMoment`) then caps.  This is the mechanism by which a
positive zero density contradicts a bounded mean value.

The positivity hypothesis `a ≤ g` (with `0 < a`) is the honest content: `log` is concave only on the
open half-line, so the average must avoid the boundary — on a circle this means avoiding the zeros of
`ξ`, which holds on any circle disjoint from the ξ-divisor.
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open MeasureTheory Real Set

namespace RHTower

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- **Jensen's inequality for `log`.**  For a probability average of a function valued in a positive
closed interval `[a, b]`, the average of `log g` is at most the `log` of the average: concavity of
`log` on `(0, ∞)`. -/
theorem jensen_avg_log [IsProbabilityMeasure μ] {g : α → ℝ} {a b : ℝ} (ha : 0 < a)
    (hmem : ∀ᵐ x ∂μ, g x ∈ Set.Icc a b)
    (hgi : Integrable g μ) (hlogi : Integrable (fun x => Real.log (g x)) μ) :
    (⨍ x, Real.log (g x) ∂μ) ≤ Real.log (⨍ x, g x ∂μ) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  have hconc : ConcaveOn ℝ (Set.Icc a b) Real.log :=
    (StrictConcaveOn.concaveOn Real.strictConcaveOn_log_Ioi).subset hsub (convex_Icc a b)
  have hcont : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1))
  exact hconc.le_map_average hcont isClosed_Icc hmem hgi hlogi

/-- **The mean-square form of the bridge.**  For a probability average of a function valued in a
positive closed interval, `⨍ log g ≤ ½ · log(⨍ g²)`: the average of `log g` is controlled by the
second moment `⨍ g²`.  Applied on a zero-avoiding circle to `g = ‖ξ‖`, this converts the Littlewood
circle average of `log‖ξ‖` into a mean square. -/
theorem jensen_avg_log_sq [IsProbabilityMeasure μ] {g : α → ℝ} {a b : ℝ} (ha : 0 < a)
    (hmem : ∀ᵐ x ∂μ, g x ∈ Set.Icc a b)
    (hgi : Integrable g μ) (hsqi : Integrable (fun x => g x ^ 2) μ)
    (hlogi : Integrable (fun x => Real.log (g x)) μ) :
    (⨍ x, Real.log (g x) ∂μ) ≤ (1 / 2) * Real.log (⨍ x, (g x) ^ 2 ∂μ) := by
  -- `log g = ½ log (g²)` pointwise a.e. (g > 0), then Jensen on `g²`.
  have hmemsq : ∀ᵐ x ∂μ, g x ^ 2 ∈ Set.Icc (a ^ 2) (b ^ 2) := by
    filter_upwards [hmem] with x hx
    exact ⟨by nlinarith [hx.1, ha.le], by nlinarith [hx.1, hx.2, ha.le]⟩
  have hlogsqi : Integrable (fun x => Real.log (g x ^ 2)) μ := by
    have : (fun x => Real.log (g x ^ 2)) = (fun x => 2 * Real.log (g x)) := by
      funext x; rw [Real.log_pow]; push_cast; ring
    rw [this]; exact hlogi.const_mul 2
  have hjensen := jensen_avg_log (μ := μ) (g := fun x => g x ^ 2) (a := a ^ 2) (b := b ^ 2)
    (by positivity) hmemsq hsqi hlogsqi
  -- rewrite `⨍ log (g²) = 2 ⨍ log g`
  have hrw : (⨍ x, Real.log (g x ^ 2) ∂μ) = 2 * ⨍ x, Real.log (g x) ∂μ := by
    rw [← integral_average, ← integral_average]
    rw [← integral_mul_left]
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.log_pow]; push_cast; ring
  rw [hrw] at hjensen
  linarith
end RHTower
