import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# First-order Gibbs cost of a bounded displacement

Moving a source vertex to a target at displacement at most `H` changes the exponential weight
`n ↦ exp (-(x n))` by at most `x · H`.  The sharp form is the one-sided mean value estimate

`|exp (-y₁) - exp (-y₂)| ≤ |y₁ - y₂| · exp (-min y₁ y₂)`,

valid for all reals with no restriction on the increment: the difference factors as
`exp(-y₁)(1 - exp(-(y₂-y₁)))` and `1 - exp(-s) ≤ s` for `s ≥ 0`.

Summed over a shell of source vertices this gives a total cost of `#shell · x · H`, which for the
Gibbs scale `x ≍ 1/U` on a dyadic shell of size `U` is `O(H)`.
-/

namespace RHTower

open Finset

/-- `1 - exp(-s) ≤ s`, valid for every real `s`. -/
theorem one_sub_exp_neg_le (s : ℝ) : 1 - Real.exp (-s) ≤ s := by
  have := Real.add_one_le_exp (-s)
  linarith

/-- The one-sided form of the exponential displacement estimate, valid for all reals. -/
theorem exp_neg_sub_exp_neg_le (y₁ y₂ : ℝ) :
    Real.exp (-y₁) - Real.exp (-y₂) ≤ (y₂ - y₁) * Real.exp (-y₁) := by
  have hfac : Real.exp (-y₁) - Real.exp (-y₂)
      = Real.exp (-y₁) * (1 - Real.exp (-(y₂ - y₁))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    ring_nf
  rw [hfac]
  have hstep : 1 - Real.exp (-(y₂ - y₁)) ≤ y₂ - y₁ := one_sub_exp_neg_le _
  have hpos : (0 : ℝ) < Real.exp (-y₁) := Real.exp_pos _
  nlinarith [hstep, hpos]

/-- **Exponential displacement estimate.**  Sharp, with no restriction on the increment. -/
theorem abs_exp_neg_sub_exp_neg_le (y₁ y₂ : ℝ) :
    |Real.exp (-y₁) - Real.exp (-y₂)| ≤ |y₁ - y₂| * Real.exp (-min y₁ y₂) := by
  rcases le_total y₁ y₂ with h | h
  · have hmin : min y₁ y₂ = y₁ := min_eq_left h
    have hge : Real.exp (-y₂) ≤ Real.exp (-y₁) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.exp (-y₁) - Real.exp (-y₂)), hmin,
      abs_of_nonpos (by linarith : y₁ - y₂ ≤ 0)]
    have := exp_neg_sub_exp_neg_le y₁ y₂
    linarith
  · have hmin : min y₁ y₂ = y₂ := min_eq_right h
    have hge : Real.exp (-y₁) ≤ Real.exp (-y₂) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonpos (by linarith : Real.exp (-y₁) - Real.exp (-y₂) ≤ 0), hmin,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ y₁ - y₂)]
    have := exp_neg_sub_exp_neg_le y₂ y₁
    linarith

/-- **Edge cost.**  A displacement of at most `H` at Gibbs scale `x` costs at most `x · H`. -/
theorem abs_gibbsEdge_le {x H : ℝ} (hx : 0 ≤ x) {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hmn : |m - n| ≤ H) :
    |Real.exp (-(x * m)) - Real.exp (-(x * n))| ≤ x * H := by
  have hmin : Real.exp (-min (x * m) (x * n)) ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    have hxm : (0 : ℝ) ≤ x * m := mul_nonneg hx hm
    have hxn : (0 : ℝ) ≤ x * n := mul_nonneg hx hn
    have : (0 : ℝ) ≤ min (x * m) (x * n) := le_min hxm hxn
    linarith
  refine le_trans (abs_exp_neg_sub_exp_neg_le (x * m) (x * n)) ?_
  have hdiff : |x * m - x * n| = x * |m - n| := by
    rw [show x * m - x * n = x * (m - n) by ring, abs_mul, abs_of_nonneg hx]
  rw [hdiff]
  have hxH : x * |m - n| ≤ x * H := mul_le_mul_of_nonneg_left hmn hx
  have hnn : (0 : ℝ) ≤ x * |m - n| := by positivity
  nlinarith [hmin, hnn, Real.exp_pos (-min (x * m) (x * n))]

/-- **Aggregate cost.**  A matching of `s` source vertices, each moved by at most `H`, has total
first-order Gibbs cost at most `#s · x · H`. -/
theorem sum_abs_gibbsEdge_le {x H : ℝ} (hx : 0 ≤ x) {ι : Type*} (s : Finset ι)
    (m n : ι → ℝ) (hm : ∀ i ∈ s, 0 ≤ m i) (hn : ∀ i ∈ s, 0 ≤ n i)
    (hmn : ∀ i ∈ s, |m i - n i| ≤ H) :
    ∑ i ∈ s, |Real.exp (-(x * m i)) - Real.exp (-(x * n i))| ≤ (s.card : ℝ) * (x * H) := by
  calc ∑ i ∈ s, |Real.exp (-(x * m i)) - Real.exp (-(x * n i))|
      ≤ ∑ _i ∈ s, x * H :=
        Finset.sum_le_sum fun i hi => abs_gibbsEdge_le hx (hm i hi) (hn i hi) (hmn i hi)
    _ = (s.card : ℝ) * (x * H) := by rw [Finset.sum_const, nsmul_eq_mul]

end RHTower
