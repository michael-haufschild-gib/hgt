import GaloisForLFunctions.RHTower.Sieve.DirichletMeanValue

/-!
# Gallagher's Sobolev lemma

A `C¹` function is controlled at a point by its averages over a surrounding interval:

`|f(a)| ≤ (2h)^{-1} ∫_{a-h}^{a+h} |f| + ∫_{a-h}^{a+h} |f'|`.

The proof is the fundamental theorem of calculus followed by averaging: for every `x` in the
interval, `f(a) = f(x) + ∫_x^a f'`, so `|f(a)| ≤ |f(x)| + ∫_{a-h}^{a+h} |f'|`, and integrating this
in `x` over an interval of length `2h` gives the statement.

This is the analytic core of Gallagher's proof of the large sieve.  Applied to `|S|²` at separated
points, the intervals are disjoint and the averages assemble into `∫_0^1 |S|²` and `∫_0^1 |S| |S'|`,
which Parseval evaluates — giving a constant of the sharp shape `N + δ^{-1}`, with no logarithm.
That is the route past the obstruction `sum_inv_abs_dist_le` identifies for absolute-value
arguments: it never forms a sum of reciprocal separations at all.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **Gallagher's Sobolev lemma.** -/
theorem gallagher_sobolev {f f' : ℝ → ℝ} {a h : ℝ} (hh : 0 < h)
    (hderiv : ∀ x ∈ Set.Icc (a - h) (a + h), HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Set.Icc (a - h) (a + h))) :
    |f a| ≤ (1 / (2 * h)) * (∫ x in (a - h)..(a + h), |f x|)
      + (∫ x in (a - h)..(a + h), |f' x|) := by
  have hab : a - h ≤ a + h := by linarith
  have huIcc : Set.uIcc (a - h) (a + h) = Set.Icc (a - h) (a + h) := Set.uIcc_of_le hab
  -- `f` is continuous on the interval
  have hcontf : ContinuousOn f (Set.Icc (a - h) (a + h)) := fun x hx =>
    ((hderiv x hx).continuousAt).continuousWithinAt
  have hIf : IntervalIntegrable (fun x => |f x|) volume (a - h) (a + h) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact hcontf.abs
  have hIf' : IntervalIntegrable (fun x => |f' x|) volume (a - h) (a + h) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact hcont.abs
  have hIf'0 : IntervalIntegrable f' volume (a - h) (a + h) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact hcont
  set D : ℝ := ∫ x in (a - h)..(a + h), |f' x| with hD
  -- the derivative integral dominates every partial one
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact intervalIntegral.integral_nonneg hab (fun x _ => abs_nonneg _)
  have hmem_a : a ∈ Set.Icc (a - h) (a + h) := by
    constructor <;> linarith
  -- pointwise: the value at `a` is controlled by the value at any nearby point
  have hkey : ∀ x ∈ Set.Icc (a - h) (a + h), |f a| ≤ |f x| + D := by
    intro x hx
    have hsub : Set.uIcc x a ⊆ Set.Icc (a - h) (a + h) :=
      Set.uIcc_subset_Icc hx hmem_a
    have hIsub : IntervalIntegrable f' volume x a := by
      refine ContinuousOn.intervalIntegrable ?_
      exact hcont.mono hsub
    have hFTC : ∫ y in x..a, f' y = f a - f x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hderiv y (hsub hy)) hIsub
    have hpartabs : |(∫ y in x..a, |f' y|)| ≤ D := by
      rcases le_total x a with hxa | hax
      · have hnn : (0 : ℝ) ≤ ∫ y in x..a, |f' y| :=
          intervalIntegral.integral_nonneg hxa (fun y _ => abs_nonneg _)
        rw [abs_of_nonneg hnn, hD]
        exact intervalIntegral.integral_mono_interval hx.1 hxa (by linarith [hmem_a.2])
          (Filter.Eventually.of_forall (fun y => abs_nonneg _)) hIf'
      · have hsym : (∫ y in x..a, |f' y|) = -(∫ y in a..x, |f' y|) :=
          intervalIntegral.integral_symm a x
        have hnn : (0 : ℝ) ≤ ∫ y in a..x, |f' y| :=
          intervalIntegral.integral_nonneg hax (fun y _ => abs_nonneg _)
        rw [hsym, abs_neg, abs_of_nonneg hnn, hD]
        exact intervalIntegral.integral_mono_interval (by linarith [hmem_a.1]) hax hx.2
          (Filter.Eventually.of_forall (fun y => abs_nonneg _)) hIf'
    have hbound : |f a - f x| ≤ D := by
      rw [← hFTC]
      have h1 : ‖∫ y in x..a, f' y‖ ≤ |(∫ y in x..a, ‖f' y‖)| :=
        intervalIntegral.norm_integral_le_abs_integral_norm
      simp only [Real.norm_eq_abs] at h1
      linarith [hpartabs]
    have habs : |f a| ≤ |f x| + |f a - f x| := by
      have := abs_sub_abs_le_abs_sub (f a) (f x)
      linarith
    linarith
  -- average the pointwise bound
  have haverage : ∫ x in (a - h)..(a + h), |f a|
      ≤ ∫ x in (a - h)..(a + h), (|f x| + D) := by
    refine intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (hIf.add intervalIntegrable_const) ?_
    intro x hx
    exact hkey x hx
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hIf intervalIntegrable_const,
    intervalIntegral.integral_const] at haverage
  simp only [smul_eq_mul] at haverage
  have hlen : (a + h) - (a - h) = 2 * h := by ring
  rw [hlen] at haverage
  -- divide by the length
  have hpos : (0 : ℝ) < 2 * h := by linarith
  have hgoal : (2 * h) * |f a|
      ≤ (2 * h) * ((1 / (2 * h)) * (∫ x in (a - h)..(a + h), |f x|) + D) := by
    have heq : (2 * h) * ((1 / (2 * h)) * (∫ x in (a - h)..(a + h), |f x|) + D)
        = (∫ x in (a - h)..(a + h), |f x|) + (2 * h) * D := by
      field_simp
    rw [heq]
    exact haverage
  exact le_of_mul_le_mul_left hgoal hpos

end RHTower.Sieve
