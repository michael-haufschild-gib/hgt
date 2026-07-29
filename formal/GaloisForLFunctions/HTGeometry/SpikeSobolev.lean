/-
A pointwise value is controlled by a local mean square plus the local variation.

For a differentiable real function on `[a,b]`, the square of any value differs from the square of
any other value by at most the total variation of `f²`:

  `f t₀ ^ 2 - f t ^ 2 ≤ ∫_a^b |2 f f'|`,

and integrating this over `t` gives the Sobolev-type bound

  `(b-a) · f t₀ ^ 2 ≤ ∫_a^b f² + (b-a) · ∫_a^b |2 f f'|`.

This is the analytic content of the passage from a moment bound to a pointwise bound: a large value
of `|f|` at one point must be sustained across the whole interval unless the derivative is large,
so the mean square sees it.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

open intervalIntegral MeasureTheory

namespace HTGeometry

/-- The square of a differentiable function has derivative `2 f f'`. -/
theorem hasDerivAt_sq {f f' : ℝ → ℝ} {x : ℝ} (h : HasDerivAt f (f' x) x) :
    HasDerivAt (fun y => f y ^ 2) (2 * f x * f' x) x := by
  have hm := HasDerivAt.mul h h
  have hfun : (f * f) = fun y => f y ^ 2 := by funext y; simp [sq]
  rw [hfun] at hm
  exact hm.congr_deriv (by ring)

/-- **Pointwise-to-mean transfer, difference form.**  For `f` differentiable on `[a,b]` with
`2 f f'` integrable, the difference of squares at any two points of `[a,b]` is bounded by the total
variation of `f²`.  Proof: fundamental theorem of calculus on the subinterval, then monotonicity of
the integral of `|2 f f'|` from that subinterval to `[a,b]`. -/
theorem sq_sub_sq_le_variation {f f' : ℝ → ℝ} {a b t₀ t : ℝ}
    (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable (fun x => 2 * f x * f' x) volume a b) :
    f t₀ ^ 2 - f t ^ 2 ≤ ∫ x in a..b, |2 * f x * f' x| := by
  have hIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  -- every subinterval with endpoints in `[a,b]` sits inside `uIcc a b`
  have hsub : ∀ u v : ℝ, u ∈ Set.Icc a b → v ∈ Set.Icc a b →
      Set.uIcc u v ⊆ Set.uIcc a b := by
    intro u v hu hv
    rw [hIcc]
    exact Set.uIcc_subset_Icc hu hv
  -- the fundamental theorem of calculus on any such subinterval
  have hFTC : ∀ u v : ℝ, u ∈ Set.Icc a b → v ∈ Set.Icc a b →
      (∫ x in u..v, 2 * f x * f' x) = f v ^ 2 - f u ^ 2 := by
    intro u v hu hv
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_sq (hderiv x (hsub u v hu hv hx)))
      (hint.mono_set (hsub u v hu hv))
  -- the absolute integral over a subinterval is at most the absolute integral over `[a,b]`
  have hmono : ∀ u v : ℝ, u ∈ Set.Icc a b → v ∈ Set.Icc a b → u ≤ v →
      |∫ x in u..v, 2 * f x * f' x| ≤ ∫ x in a..b, |2 * f x * f' x| := by
    intro u v hu hv huv
    refine (intervalIntegral.abs_integral_le_integral_abs huv).trans ?_
    exact intervalIntegral.integral_mono_interval hu.1 huv hv.2
      (Filter.Eventually.of_forall fun x => abs_nonneg _) hint.abs
  rcases le_total t t₀ with h | h
  · calc f t₀ ^ 2 - f t ^ 2 = ∫ x in t..t₀, 2 * f x * f' x := (hFTC t t₀ ht ht₀).symm
      _ ≤ |∫ x in t..t₀, 2 * f x * f' x| := le_abs_self _
      _ ≤ ∫ x in a..b, |2 * f x * f' x| := hmono t t₀ ht ht₀ h
  · have hneg : f t₀ ^ 2 - f t ^ 2 = -(∫ x in t₀..t, 2 * f x * f' x) := by
      rw [hFTC t₀ t ht₀ ht]; ring
    calc f t₀ ^ 2 - f t ^ 2 = -(∫ x in t₀..t, 2 * f x * f' x) := hneg
      _ ≤ |∫ x in t₀..t, 2 * f x * f' x| := neg_le_abs _
      _ ≤ ∫ x in a..b, |2 * f x * f' x| := hmono t₀ t ht₀ ht h

/-- **The spike inequality.**  Integrating the difference form over the second point gives a genuine
Sobolev bound: the value at any point is controlled by the mean square over the interval plus the
variation.  A spike of `f` therefore cannot hide from `∫ f²` unless `f'` is correspondingly large. -/
theorem sq_le_mean_add_variation {f f' : ℝ → ℝ} {a b t₀ : ℝ}
    (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable (fun x => 2 * f x * f' x) volume a b) :
    (b - a) * f t₀ ^ 2
      ≤ (∫ t in a..b, f t ^ 2) + (b - a) * ∫ x in a..b, |2 * f x * f' x| := by
  set V : ℝ := ∫ x in a..b, |2 * f x * f' x| with hV
  have hcontf : ContinuousOn f (Set.uIcc a b) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b :=
    (hcontf.pow 2).intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc a b, f t₀ ^ 2 - f t ^ 2 ≤ V := fun t ht =>
    sq_sub_sq_le_variation hab ht₀ ht hderiv hint
  have hstep : (∫ t in a..b, (f t₀ ^ 2 - f t ^ 2)) ≤ ∫ _t in a..b, V :=
    intervalIntegral.integral_mono_on hab
      ((intervalIntegrable_const).sub hf2) intervalIntegrable_const hpt
  have hsplit : (∫ t in a..b, (f t₀ ^ 2 - f t ^ 2))
      = (b - a) * f t₀ ^ 2 - ∫ t in a..b, f t ^ 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hf2,
      intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hconst : (∫ _t in a..b, V) = (b - a) * V := by
    rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  rw [hsplit, hconst] at hstep
  linarith

end HTGeometry
