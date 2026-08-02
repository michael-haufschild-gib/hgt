import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Two-sided Wold-breadth deviation rate

The reciprocal-marker reservoir can absorb any Route E source sector whose local population is
`o(H / log log X)`.  Shiu's bound for `c ^ omega(n)` gives the same entropy rate on both sides of
normal Wold breadth:

`I(c) = 1 - c + c log c`.

This file records the exact unconditional calculus fact omitted by the earlier lower-tail audit:
`I(c)` is strictly positive for every positive `c != 1`, including `c > 1`.  The paper argument
then applies the existing marker reservoir to both fixed tails.  No distributional theorem is
asserted in Lean here.
-/

namespace RHTower

noncomputable section

/-- Chernoff entropy rate for a fixed multiplicative Wold-breadth tilt. -/
def woldBreadthDeviationRate (c : ℝ) : ℝ :=
  1 - c + c * Real.log c

/-- Exact exponent produced after optimizing the `c ^ omega` tail bound. -/
theorem woldBreadthDeviationExponent_eq_neg_rate (c : ℝ) :
    c - 1 - c * Real.log c = -woldBreadthDeviationRate c := by
  unfold woldBreadthDeviationRate
  ring

/-- The Wold-breadth Chernoff rate vanishes at normal order. -/
@[simp]
theorem woldBreadthDeviationRate_one :
    woldBreadthDeviationRate 1 = 0 := by
  simp [woldBreadthDeviationRate]

/-- Strict positivity holds on both fixed sides of normal order. -/
theorem woldBreadthDeviationRate_pos
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≠ 1) :
    0 < woldBreadthDeviationRate c := by
  have hlog := Real.self_sub_one_lt_mul_log hc hc1
  unfold woldBreadthDeviationRate
  linarith

/-- Lower-tail specialization used in the original marker transport theorem. -/
theorem woldBreadthDeviationRate_pos_of_lt_one
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    0 < woldBreadthDeviationRate c :=
  woldBreadthDeviationRate_pos hc.le (ne_of_lt hc1)

/-- New symmetric upper-tail specialization: every fixed upper Wold-breadth deviation has the
same positive entropy gap and is therefore smaller than the growing reciprocal-marker reservoir. -/
theorem woldBreadthDeviationRate_pos_of_one_lt
    {c : ℝ} (hc : 1 < c) :
    0 < woldBreadthDeviationRate c :=
  woldBreadthDeviationRate_pos (le_trans (by norm_num) hc.le)
    (ne_of_gt hc)

end

end RHTower
