import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The first two exponential divided differences

`expDivOne x = (exp x - 1)/x` and `expDivTwo x = (exp x - 1 - x)/x^2`, both defined by the
parameter integrals `∫₀¹ exp (t x) dt` and `∫₀¹ (1-t) exp (t x) dt`, which remove the apparent
poles at `x = 0`.  On the closed negative half line both are Lipschitz with explicit constants
and are trapped between `exp x` and `1` (resp. `exp x / 2` and `1/2`).
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory intervalIntegral

noncomputable section

/-- `∫₀¹ exp (t x) dt`, the pole-free form of `(exp x - 1)/x`. -/
def expDivOne (x : ℝ) : ℝ := ∫ t in (0:ℝ)..1, Real.exp (t * x)

/-- `∫₀¹ (1-t) exp (t x) dt`, the pole-free form of `(exp x - 1 - x)/x^2`. -/
def expDivTwo (x : ℝ) : ℝ := ∫ t in (0:ℝ)..1, (1 - t) * Real.exp (t * x)

/-- `exp` is `exp M`-Lipschitz on the half line `Iic M`, by the tangent line inequality. -/
theorem abs_exp_sub_exp_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  rcases le_total b a with hba | hab
  · have hkey : Real.exp a - Real.exp b ≤ Real.exp M * (a - b) := by
      have h1 : (b - a) + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp _
      have h2 : ((b - a) + 1) * Real.exp a ≤ Real.exp (b - a) * Real.exp a :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos a).le
      have h3 : Real.exp (b - a) * Real.exp a = Real.exp b := by
        rw [← Real.exp_add]; ring_nf
      have h4 : Real.exp a ≤ Real.exp M := Real.exp_le_exp.mpr ha
      nlinarith [Real.exp_pos a]
    have hnn : 0 ≤ Real.exp a - Real.exp b := by
      have := Real.exp_le_exp.mpr hba
      linarith
    rw [abs_of_nonneg hnn, abs_of_nonneg (by linarith)]
    exact hkey
  · have hkey : Real.exp b - Real.exp a ≤ Real.exp M * (b - a) := by
      have h1 : (a - b) + 1 ≤ Real.exp (a - b) := Real.add_one_le_exp _
      have h2 : ((a - b) + 1) * Real.exp b ≤ Real.exp (a - b) * Real.exp b :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos b).le
      have h3 : Real.exp (a - b) * Real.exp b = Real.exp a := by
        rw [← Real.exp_add]; ring_nf
      have h4 : Real.exp b ≤ Real.exp M := Real.exp_le_exp.mpr hb
      nlinarith [Real.exp_pos b]
    have hnn : 0 ≤ Real.exp b - Real.exp a := by
      have := Real.exp_le_exp.mpr hab
      linarith
    rw [abs_sub_comm, abs_of_nonneg hnn, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact hkey

/-- Two nonpositive exponentials differ by at most the difference of their arguments. -/
theorem abs_exp_sub_exp_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  simpa using abs_exp_sub_exp_le ha hb

theorem continuous_expMul (x : ℝ) : Continuous fun t : ℝ => Real.exp (t * x) := by
  fun_prop

theorem intervalIntegrable_expMul (x : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (t * x)) volume a b :=
  (continuous_expMul x).intervalIntegrable a b

theorem intervalIntegrable_expMulTwo (x : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (1 - t) * Real.exp (t * x)) volume a b := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- Closed form of `expDivOne` away from the origin. -/
theorem expDivOne_eq_of_ne {x : ℝ} (hx : x ≠ 0) :
    expDivOne x = (Real.exp x - 1) / x := by
  have hderiv : ∀ t ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.exp (t * x) / x) (Real.exp (t * x)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t * x) x t := by
      simpa using (hasDerivAt_id t).mul_const x
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (t * x)) (Real.exp (t * x) * x) t := h1.exp
    have := h2.div_const x
    simpa [mul_div_assoc, mul_div_cancel_right₀ _ hx] using this
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_expMul x 0 1)
  rw [expDivOne, this]
  simp [sub_div]

theorem expDivOne_zero : expDivOne 0 = 1 := by
  simp [expDivOne]

/-- Closed form of `expDivTwo` away from the origin. -/
theorem expDivTwo_eq_of_ne {x : ℝ} (hx : x ≠ 0) :
    expDivTwo x = (Real.exp x - 1 - x) / x ^ 2 := by
  have hderiv : ∀ t ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => (1 - t) * Real.exp (t * x) / x + Real.exp (t * x) / x ^ 2)
        ((1 - t) * Real.exp (t * x)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t * x) x t := by
      simpa using (hasDerivAt_id t).mul_const x
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (t * x)) (Real.exp (t * x) * x) t := h1.exp
    have h3 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1:ℝ)
    have h4 : HasDerivAt (fun t : ℝ => (1 - t) * Real.exp (t * x))
        (-1 * Real.exp (t * x) + (1 - t) * (Real.exp (t * x) * x)) t := h3.mul h2
    have h5 : HasDerivAt (fun t : ℝ => (1 - t) * Real.exp (t * x) / x + Real.exp (t * x) / x ^ 2)
        ((-1 * Real.exp (t * x) + (1 - t) * (Real.exp (t * x) * x)) / x
          + Real.exp (t * x) * x / x ^ 2) t := (h4.div_const x).add (h2.div_const (x ^ 2))
    convert h5 using 1
    field_simp
    ring
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_expMulTwo x 0 1)
  rw [expDivTwo, this]
  simp only [Real.exp_zero, one_mul, zero_mul, sub_self, zero_div, sub_zero]
  field_simp
  ring

theorem expDivTwo_zero : expDivTwo 0 = 1 / 2 := by
  have h : expDivTwo 0 = ∫ t in (0:ℝ)..1, (1 - t) := by
    simp [expDivTwo]
  rw [h, intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_id]
  simp [integral_id]
  norm_num

/-- On the negative half line the first divided difference is at most `1`. -/
theorem expDivOne_le_one {x : ℝ} (hx : x ≤ 0) : expDivOne x ≤ 1 := by
  have h : expDivOne x ≤ ∫ _t in (0:ℝ)..1, (1:ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (intervalIntegrable_expMul x 0 1)
      intervalIntegrable_const
    intro t ht
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.1 hx)
  simpa using h

/-- On the negative half line the first divided difference dominates `exp`. -/
theorem exp_le_expDivOne {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ expDivOne x := by
  have h : (∫ _t in (0:ℝ)..1, Real.exp x) ≤ expDivOne x := by
    apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (intervalIntegrable_expMul x 0 1)
    intro t ht
    apply Real.exp_le_exp.mpr
    nlinarith [ht.1, ht.2]
  simpa using h

theorem expDivOne_pos {x : ℝ} (hx : x ≤ 0) : 0 < expDivOne x :=
  lt_of_lt_of_le (Real.exp_pos x) (exp_le_expDivOne hx)

/-- On the negative half line the second divided difference is at most `1/2`. -/
theorem expDivTwo_le_half {x : ℝ} (hx : x ≤ 0) : expDivTwo x ≤ 1 / 2 := by
  have h : expDivTwo x ≤ ∫ t in (0:ℝ)..1, (1 - t) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (intervalIntegrable_expMulTwo x 0 1)
      ((continuous_const.sub continuous_id).intervalIntegrable 0 1)
    intro t ht
    simp only [Pi.sub_apply, id_eq]
    have h1 : Real.exp (t * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.1 hx)
    nlinarith [ht.2, Real.exp_pos (t * x)]
  calc expDivTwo x ≤ ∫ t in (0:ℝ)..1, (1 - t) := h
    _ = 1 / 2 := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_id]
        norm_num

/-- On the negative half line the second divided difference dominates `exp x / 2`. -/
theorem exp_div_two_le_expDivTwo {x : ℝ} (hx : x ≤ 0) : Real.exp x / 2 ≤ expDivTwo x := by
  have h : (∫ t in (0:ℝ)..1, (1 - t) * Real.exp x) ≤ expDivTwo x := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 1)
      (intervalIntegrable_expMulTwo x 0 1)
    intro t ht
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
    have h1 : Real.exp x ≤ Real.exp (t * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ht.1, ht.2]
    nlinarith [ht.2]
  have h2 : (∫ t in (0:ℝ)..1, (1 - t) * Real.exp x) = Real.exp x / 2 := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_id]
    norm_num
    ring
  linarith [h, h2.ge, h2.le]

theorem expDivTwo_pos {x : ℝ} (hx : x ≤ 0) : 0 < expDivTwo x :=
  lt_of_lt_of_le (by positivity) (exp_div_two_le_expDivTwo hx)

/-- The first divided difference is `1`-Lipschitz on the negative half line. -/
theorem abs_expDivOne_sub_le {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |expDivOne x - expDivOne y| ≤ |x - y| := by
  have hsub : expDivOne x - expDivOne y
      = ∫ t in (0:ℝ)..1, (Real.exp (t * x) - Real.exp (t * y)) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_expMul x 0 1)
      (intervalIntegrable_expMul y 0 1)]
    rfl
  rw [hsub]
  have hbound : |∫ t in (0:ℝ)..1, (Real.exp (t * x) - Real.exp (t * y))|
      ≤ ∫ t in (0:ℝ)..1, |Real.exp (t * x) - Real.exp (t * y)| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  refine hbound.trans ?_
  have hmono : (∫ t in (0:ℝ)..1, |Real.exp (t * x) - Real.exp (t * y)|)
      ≤ ∫ _t in (0:ℝ)..1, |x - y| := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (Continuous.intervalIntegrable (by fun_prop) 0 1)
    · exact intervalIntegrable_const
    intro t ht
    have h1 : t * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 hx
    have h2 : t * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 hy
    have h3 := abs_exp_sub_exp_le_of_nonpos h1 h2
    have h4 : |t * x - t * y| ≤ |x - y| := by
      have : t * x - t * y = t * (x - y) := by ring
      rw [this, abs_mul, abs_of_nonneg ht.1]
      nlinarith [abs_nonneg (x - y), ht.2]
    exact h3.trans h4
  simpa using hmono

/-- The second divided difference is `1`-Lipschitz on the negative half line. -/
theorem abs_expDivTwo_sub_le {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |expDivTwo x - expDivTwo y| ≤ |x - y| := by
  have hsub : expDivTwo x - expDivTwo y
      = ∫ t in (0:ℝ)..1, ((1 - t) * Real.exp (t * x) - (1 - t) * Real.exp (t * y)) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_expMulTwo x 0 1)
      (intervalIntegrable_expMulTwo y 0 1)]
    rfl
  rw [hsub]
  have hbound : |∫ t in (0:ℝ)..1, ((1 - t) * Real.exp (t * x) - (1 - t) * Real.exp (t * y))|
      ≤ ∫ t in (0:ℝ)..1, |(1 - t) * Real.exp (t * x) - (1 - t) * Real.exp (t * y)| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  refine hbound.trans ?_
  have hmono : (∫ t in (0:ℝ)..1, |(1 - t) * Real.exp (t * x) - (1 - t) * Real.exp (t * y)|)
      ≤ ∫ _t in (0:ℝ)..1, |x - y| := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (Continuous.intervalIntegrable (by fun_prop) 0 1)
    · exact intervalIntegrable_const
    intro t ht
    have h1 : t * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 hx
    have h2 : t * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 hy
    have h3 := abs_exp_sub_exp_le_of_nonpos h1 h2
    have h4 : |t * x - t * y| ≤ |x - y| := by
      have hxy : t * x - t * y = t * (x - y) := by ring
      rw [hxy, abs_mul, abs_of_nonneg ht.1]
      nlinarith [abs_nonneg (x - y), ht.2]
    have hfac : (1 - t) * Real.exp (t * x) - (1 - t) * Real.exp (t * y)
        = (1 - t) * (Real.exp (t * x) - Real.exp (t * y)) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)]
    nlinarith [abs_nonneg (Real.exp (t * x) - Real.exp (t * y)), ht.1, ht.2, h3.trans h4,
      abs_nonneg (x - y)]
  simpa using hmono

end

end GaloisForLFunctions.HTGeometry
