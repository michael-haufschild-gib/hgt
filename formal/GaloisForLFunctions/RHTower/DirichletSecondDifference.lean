import GaloisForLFunctions.RHTower.DirichletFirstDifference

/-!
# The unit second difference of the Dirichlet kernel

```text
‖ x^{−s} − 2(x+1)^{−s} + (x+2)^{−s} ‖  ≤  ‖s‖ · ‖s+1‖ · x^{−Re s−2} .
```

The first difference is an integral of the derivative, `x^{−s} − (x+1)^{−s} = s ∫_x^{x+1} y^{−s−1}dy`;
subtracting the shifted copy turns the second difference into a single integral of a first
difference at exponent `s+1`, which the previous section bounds by `‖s+1‖ y^{−Re s−2}`.  Two unit
steps therefore cost two powers of the exponent and two powers of `x`.

This is the estimate a doubly Abel-summed Dirichlet series needs: paired with smoothed partial sums
of size `O(jᵅ)` it makes `∑ⱼ ‖A₁(j)‖ ‖Δ²bⱼ‖` converge exactly on `Re s > α − 1`.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- **The first difference as an integral of the derivative.** -/
theorem cpow_neg_sub_eq_integral {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (a : ℂ) ^ (-s) - (b : ℂ) ^ (-s) = ∫ x in a..b, s * (x : ℂ) ^ (-s - 1) := by
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1 : -s - 1 ≠ 0 := by
    intro h
    have hval : s = -1 := by linear_combination -h
    rw [hval] at hs
    norm_num at hs
  have hpos : ∀ x ∈ Set.uIcc a b, (0 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x := fun x hx =>
    hasDerivAt_ofReal_cpow_const (ne_of_gt (hpos x hx)) (neg_ne_zero.2 hsne)
  have hcont : ContinuousOn (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) (Set.uIcc a b) := by
    intro x hx
    have hd := hasDerivAt_ofReal_cpow_const (r := -s - 1) (ne_of_gt (hpos x hx)) hs1
    exact ((hd.continuousAt).const_mul (-s)).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hneg : (∫ x in a..b, s * (x : ℂ) ^ (-s - 1))
      = -∫ x in a..b, -s * (x : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [hneg, hftc]
  ring

/-- **The unit second difference of the Dirichlet kernel.** -/
theorem norm_second_difference_cpow_le {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s) - 2 * ((x + 1 : ℝ) : ℂ) ^ (-s) + ((x + 2 : ℝ) : ℂ) ^ (-s)‖
      ≤ ‖s‖ * ‖s + 1‖ * x ^ (-s.re - 2) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have h1 := cpow_neg_sub_eq_integral hs hx (by linarith : x ≤ x + 1)
  have h2 := cpow_neg_sub_eq_integral hs hx1 (by linarith : x + 1 ≤ x + 2)
  -- the second difference is a single integral of a shifted first difference
  have hshift : (∫ y in (x + 1)..(x + 2), s * (y : ℂ) ^ (-s - 1))
      = ∫ y in x..(x + 1), s * ((y + 1 : ℝ) : ℂ) ^ (-s - 1) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := x) (b := x + 1) (f := fun y : ℝ => s * (y : ℂ) ^ (-s - 1)) 1
    simpa [show x + 1 + 1 = x + 2 by ring] using h.symm
  have hkey : (x : ℂ) ^ (-s) - 2 * ((x + 1 : ℝ) : ℂ) ^ (-s) + ((x + 2 : ℝ) : ℂ) ^ (-s)
      = ∫ y in x..(x + 1), s * ((y : ℂ) ^ (-s - 1) - ((y + 1 : ℝ) : ℂ) ^ (-s - 1)) := by
    have hsub : (∫ y in x..(x + 1), s * ((y : ℂ) ^ (-s - 1) - ((y + 1 : ℝ) : ℂ) ^ (-s - 1)))
        = (∫ y in x..(x + 1), s * (y : ℂ) ^ (-s - 1))
          - ∫ y in x..(x + 1), s * ((y + 1 : ℝ) : ℂ) ^ (-s - 1) := by
      rw [← intervalIntegral.integral_sub]
      · refine intervalIntegral.integral_congr fun y _ => ?_
        ring
      · refine ContinuousOn.intervalIntegrable ?_
        intro y hy
        have hy0 : (0 : ℝ) < y := by
          rw [Set.uIcc_of_le (by linarith)] at hy
          exact lt_of_lt_of_le hx hy.1
        have hs1 : (-s - 1 : ℂ) ≠ 0 := by
          intro h
          have hval : s = -1 := by linear_combination -h
          rw [hval] at hs
          norm_num at hs
        exact (((hasDerivAt_ofReal_cpow_const (ne_of_gt hy0) hs1).continuousAt).const_mul
          s).continuousWithinAt
      · refine ContinuousOn.intervalIntegrable ?_
        intro y hy
        have hy0 : (0 : ℝ) < y + 1 := by
          rw [Set.uIcc_of_le (by linarith)] at hy
          have := lt_of_lt_of_le hx hy.1
          linarith
        have hs1 : (-s - 1 : ℂ) ≠ 0 := by
          intro h
          have hval : s = -1 := by linear_combination -h
          rw [hval] at hs
          norm_num at hs
        have hcomp : ContinuousAt (fun z : ℝ => ((z + 1 : ℝ) : ℂ) ^ (-s - 1)) y := by
          have hg : ContinuousAt (fun w : ℝ => (w : ℂ) ^ (-s - 1)) (y + 1) :=
            (hasDerivAt_ofReal_cpow_const (x := y + 1) (ne_of_gt hy0) hs1).continuousAt
          exact ContinuousAt.comp (g := fun w : ℝ => (w : ℂ) ^ (-s - 1))
            (f := fun z : ℝ => z + 1) hg ((continuous_id.add continuous_const).continuousAt)
        exact (hcomp.const_mul s).continuousWithinAt
    rw [hsub, ← hshift]
    have hexp := h1
    have hexp2 := h2
    rw [← hexp, ← hexp2]
    ring
  rw [hkey]
  have hbound : ∀ y ∈ Set.uIoc x (x + 1),
      ‖s * ((y : ℂ) ^ (-s - 1) - ((y + 1 : ℝ) : ℂ) ^ (-s - 1))‖
        ≤ ‖s‖ * ‖s + 1‖ * x ^ (-s.re - 2) := by
    intro y hy
    rw [Set.uIoc_of_le (by linarith)] at hy
    have hy0 : (0 : ℝ) < y := lt_trans hx hy.1
    have hneg : (-s - 1 : ℂ) = -(s + 1) := by ring
    rw [norm_mul, hneg]
    have hstep := norm_cpow_neg_succ_sub_succ_le hs hy0
    have hmono : y ^ (-s.re - 2) ≤ x ^ (-s.re - 2) :=
      Real.rpow_le_rpow_of_nonpos hx hy.1.le (by linarith)
    have hchain : ‖(y : ℂ) ^ (-(s + 1)) - ((y + 1 : ℝ) : ℂ) ^ (-(s + 1))‖
        ≤ ‖s + 1‖ * x ^ (-s.re - 2) :=
      le_trans hstep (mul_le_mul_of_nonneg_left hmono (norm_nonneg _))
    calc ‖s‖ * ‖(y : ℂ) ^ (-(s + 1)) - ((y + 1 : ℝ) : ℂ) ^ (-(s + 1))‖
        ≤ ‖s‖ * (‖s + 1‖ * x ^ (-s.re - 2)) :=
          mul_le_mul_of_nonneg_left hchain (norm_nonneg _)
      _ = ‖s‖ * ‖s + 1‖ * x ^ (-s.re - 2) := by ring
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have habs : |x + 1 - x| = 1 := by
    rw [show x + 1 - x = 1 by ring, abs_one]
  rwa [habs, mul_one] at hle

end GaloisForLFunctions.RHTower

end
