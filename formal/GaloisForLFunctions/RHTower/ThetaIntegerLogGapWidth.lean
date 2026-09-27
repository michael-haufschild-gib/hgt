import GaloisForLFunctions.RHTower.ThetaGammaPolarKernelOrientation

/-!
# Quantitative width of gaps in the complete integer logarithm mesh

The next integer after `exp(max(t,0))` gives a logarithm within
`exp(-max(t,0))` of that point. Thus an interval above zero avoiding every
`log n`, n >= 2, has exponentially small width. This is the stronger
exclusion used by the existing separated-bump construction. It is not a
bound for gaps avoiding only integers with nonzero von Mangoldt weight.
-/

noncomputable section

open Set

namespace RHTower

def thetaNextIntegerLogIndex (t : ℝ) : ℕ := Nat.floor (Real.exp (max t 0)) + 1

theorem thetaNextIntegerLogIndex_two_le (t : ℝ) : 2 ≤ thetaNextIntegerLogIndex t := by
  have h : 1 ≤ Nat.floor (Real.exp (max t 0)) := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr (le_max_right t 0)
  unfold thetaNextIntegerLogIndex
  omega

theorem thetaNextIntegerLogIndex_lower (t : ℝ) :
    max t 0 < Real.log (thetaNextIntegerLogIndex t) := by
  have hn : 0 < (thetaNextIntegerLogIndex t : ℝ) := by
    exact_mod_cast (show 0 < thetaNextIntegerLogIndex t by
      have := thetaNextIntegerLogIndex_two_le t
      omega)
  apply (Real.lt_log_iff_exp_lt hn).mpr
  simpa only [thetaNextIntegerLogIndex, Nat.cast_add, Nat.cast_one] using
    Nat.lt_floor_add_one (Real.exp (max t 0))

/-- An explicit actual integer logarithm lies within the reciprocal exponential distance. -/
theorem thetaNextIntegerLogIndex_upper (t : ℝ) :
    Real.log (thetaNextIntegerLogIndex t) ≤ max t 0 + Real.exp (-max t 0) := by
  have hn : 0 < (thetaNextIntegerLogIndex t : ℝ) := by
    exact_mod_cast (show 0 < thetaNextIntegerLogIndex t by
      have := thetaNextIntegerLogIndex_two_le t
      omega)
  have he := Real.exp_pos (max t 0)
  have hfloor : (thetaNextIntegerLogIndex t : ℝ) ≤ Real.exp (max t 0) + 1 := by
    rw [thetaNextIntegerLogIndex, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le he.le]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn he)
  rw [Real.log_div hn.ne' he.ne', Real.log_exp] at hlog
  have hratio : (thetaNextIntegerLogIndex t : ℝ) / Real.exp (max t 0) ≤
      1 + (Real.exp (max t 0))⁻¹ := by
    rw [div_le_iff₀ he]
    simpa only [add_mul, one_mul, inv_mul_cancel₀ he.ne'] using hfloor
  rw [Real.exp_neg]
  linarith

theorem integerLogFree_interval_width_le {l r : ℝ} (hl : 0 ≤ l)
    (hfree : ∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo l r) :
    r - l ≤ Real.exp (-l) := by
  have hlo := thetaNextIntegerLogIndex_lower l
  have hhi := thetaNextIntegerLogIndex_upper l
  rw [max_eq_left hl] at hlo hhi
  have hr : r ≤ Real.log (thetaNextIntegerLogIndex l) := by
    by_contra hn
    exact hfree _ (thetaNextIntegerLogIndex_two_le l) ⟨hlo, lt_of_not_ge hn⟩
  linarith

theorem integerLogFree_interval_scaled_width_le_one {l r : ℝ} (hl : 0 ≤ l)
    (hfree : ∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo l r) :
    (r - l) * Real.exp l ≤ 1 := by
  have h := mul_le_mul_of_nonneg_right (integerLogFree_interval_width_le hl hfree)
    (Real.exp_pos l).le
  simpa only [Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos l).ne'] using h

/-- Equal-radius components whose entire difference interval avoids integer logs must shrink. -/
theorem integerLogFree_equalRadius_width_le {d r : ℝ} (hl : 0 ≤ d - 2 * r)
    (hfree : ∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo (d - 2 * r) (d + 2 * r)) :
    4 * r ≤ Real.exp (-(d - 2 * r)) := by
  have h := integerLogFree_interval_width_le hl hfree
  linarith

/-- Excluding logarithms on every pair of points in two balls excludes their full difference
interval. In particular, this applies to bumps positive throughout their supporting balls. -/
theorem integerLogFree_of_ball_pairs {c₁ c₂ r : ℝ}
    (hfree : ∀ x ∈ Metric.ball c₂ r, ∀ y ∈ Metric.ball c₁ r,
      ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n) :
    ∀ n : ℕ, 2 ≤ n → Real.log n ∉
      Ioo (c₂ - c₁ - 2 * r) (c₂ - c₁ + 2 * r) := by
  intro n hn hs
  let x := (c₁ + c₂ + Real.log n) / 2
  let y := (c₁ + c₂ - Real.log n) / 2
  have hx : x ∈ Metric.ball c₂ r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [x]
    constructor <;> linarith [hs.1, hs.2]
  have hy : y ∈ Metric.ball c₁ r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [y]
    constructor <;> linarith [hs.1, hs.2]
  exact hfree x hx y hy n hn (by dsimp [x, y]; ring)

/-- The interval-width factor defeats exponential growth of the pole kernel for this
stronger, complete-integer-log-free family. The lower endpoint controls the decay. -/
theorem integerLogFree_equalRadius_coupling_le {d r : ℝ}
    (hl : 0 ≤ d - 2 * r)
    (hfree : ∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo (d - 2 * r) (d + 2 * r)) :
    2 * r * Real.exp ((d + 2 * r) / 2) ≤
      Real.exp (1 / 2) / 2 * Real.exp (-(d - 2 * r) / 2) := by
  have hw := integerLogFree_equalRadius_width_le hl hfree
  have he : Real.exp (-(d - 2 * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hr' : r ≤ 1 / 4 := by linarith
  calc
    2 * r * Real.exp ((d + 2 * r) / 2) ≤
        (Real.exp (-(d - 2 * r)) / 2) * Real.exp ((d + 2 * r) / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = Real.exp (-(d - 2 * r) + (d + 2 * r) / 2) / 2 := by
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp (1 / 2 - (d - 2 * r) / 2) / 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; simp only [neg_div]; ring

end RHTower
