/-
The linear exponential sum bound.

For `e(x) = exp(2πix)` and `α` real,

    ‖Σ_{n < N} e(αn)‖ ≤ 1 / (2‖α‖),

where `‖α‖` is the distance from `α` to the nearest integer.  The geometric series gives
`Σ_{n<N} e(αn) = (e(α)^N - 1)/(e(α) - 1)` when `e(α) ≠ 1`; the numerator has modulus at most `2`,
and the denominator has modulus `2|sin(πα)| ≥ 4‖α‖` by Jordan's inequality.

This is the base case of the exponential-sum theory: composed with the van der Corput correlation
bound it yields Weyl's inequality for polynomial phases, hence the exponent pairs.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace HTGeometry

open Finset Complex Real

/-- The additive character `e(x) = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  exact Complex.norm_exp_ofReal_mul_I _

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_natMul (x : ℝ) (n : ℕ) : ee (n * x) = (ee x) ^ n := by
  induction n with
  | zero => simp [ee]
  | succ k ih =>
      have hx : ((k : ℝ) + 1) * x = k * x + x := by ring
      rw [Nat.cast_succ, hx, ee_add, ih, pow_succ]

/-- The distance from a real number to the nearest integer. -/
noncomputable def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

theorem distToInt_nonneg (x : ℝ) : 0 ≤ distToInt x := abs_nonneg _

theorem distToInt_le_half (x : ℝ) : distToInt x ≤ 1/2 := by
  unfold distToInt
  have := abs_sub_round x
  linarith

/-- `e(x)` written in real and imaginary parts. -/
theorem ee_eq (x : ℝ) :
    ee x = ((Real.cos (2 * Real.pi * x) : ℝ) : ℂ)
      + ((Real.sin (2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by
  unfold ee
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **The modulus of `e(x) - 1`.**  Equals `2|sin(πx)|`. -/
theorem norm_ee_sub_one (x : ℝ) : ‖ee x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have hstep : ee x - 1
      = ((Real.cos (2 * Real.pi * x) - 1 : ℝ) : ℂ)
        + ((Real.sin (2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by
    rw [ee_eq]
    push_cast
    ring
  rw [hstep, Complex.norm_add_mul_I]
  have hcos : Real.cos (2 * Real.pi * x) = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
    have h2 : Real.cos (2 * (Real.pi * x)) = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
      rw [Real.cos_two_mul' (Real.pi * x)]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
    calc Real.cos (2 * Real.pi * x) = Real.cos (2 * (Real.pi * x)) := by ring_nf
      _ = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := h2
  have hsin : Real.sin (2 * Real.pi * x)
      = 2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) := by
    calc Real.sin (2 * Real.pi * x) = Real.sin (2 * (Real.pi * x)) := by ring_nf
      _ = 2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) := Real.sin_two_mul (Real.pi * x)
  rw [hcos, hsin]
  have hpyth := Real.sin_sq_add_cos_sq (Real.pi * x)
  have habs : |Real.sin (Real.pi * x)| ^ 2 = Real.sin (Real.pi * x) ^ 2 := sq_abs _
  have hval : (1 - 2 * Real.sin (Real.pi * x) ^ 2 - 1) ^ 2
      + (2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x)) ^ 2
      = (2 * |Real.sin (Real.pi * x)|) ^ 2 := by nlinarith [hpyth, habs]
  rw [hval]
  exact Real.sqrt_sq (by positivity)


/-- `|sin|` is invariant under integer multiples of `π`. -/
theorem abs_sin_add_int_mul_pi (x : ℝ) (n : ℤ) :
    |Real.sin (x + n * Real.pi)| = |Real.sin x| := by
  rw [Real.sin_add, Real.sin_int_mul_pi, mul_zero, add_zero, abs_mul]
  have hcos : |Real.cos ((n : ℝ) * Real.pi)| = 1 := by
    rw [Real.cos_int_mul_pi]
    rcases Int.even_or_odd n with he | ho
    · rw [he.neg_one_zpow]
      simp
    · simp [ho.neg_one_zpow]
  rw [hcos, mul_one]

/-- **Jordan's inequality in the form needed for exponential sums.**
`2‖x‖ ≤ |sin(πx)|`, where `‖x‖` is the distance to the nearest integer. -/
theorem two_mul_distToInt_le_abs_sin (x : ℝ) :
    2 * distToInt x ≤ |Real.sin (Real.pi * x)| := by
  set k : ℤ := round x with hk
  set r : ℝ := x - (k : ℝ) with hr
  have hxr : x = r + (k : ℝ) := by rw [hr]; ring
  have hd : distToInt x = |r| := rfl
  have hhalf : |r| ≤ 1/2 := by
    rw [← hd]; exact distToInt_le_half x
  have hper : |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * r)| := by
    rw [hxr, mul_add]
    have : Real.pi * (k : ℝ) = (k : ℝ) * Real.pi := by ring
    rw [this, abs_sin_add_int_mul_pi]
  rw [hper, hd]
  rcases abs_cases r with ⟨hrabs, hrsign⟩ | ⟨hrabs, hrsign⟩
  · have h0 : 0 ≤ Real.pi * r := by positivity
    have h1 : Real.pi * r ≤ Real.pi / 2 := by
      have := Real.pi_pos
      nlinarith [hhalf, hrabs]
    have hj := Real.mul_le_sin h0 h1
    have hsinnn : 0 ≤ Real.sin (Real.pi * r) := le_trans (by positivity) hj
    rw [abs_of_nonneg hsinnn, hrabs]
    have hpi := Real.pi_pos
    calc 2 * r = (2 / Real.pi) * (Real.pi * r) := by field_simp
      _ ≤ Real.sin (Real.pi * r) := hj
  · have hrneg : r ≤ 0 := by linarith [hrsign]
    have h0 : 0 ≤ Real.pi * (-r) := by
      have := Real.pi_pos; nlinarith
    have h1 : Real.pi * (-r) ≤ Real.pi / 2 := by
      have := Real.pi_pos
      nlinarith [hhalf, hrabs]
    have hj := Real.mul_le_sin h0 h1
    have hsinnn : 0 ≤ Real.sin (Real.pi * (-r)) := le_trans (by positivity) hj
    have hodd : Real.sin (Real.pi * r) = - Real.sin (Real.pi * (-r)) := by
      rw [show Real.pi * (-r) = -(Real.pi * r) by ring, Real.sin_neg]
      ring
    rw [hodd, abs_neg, abs_of_nonneg hsinnn, hrabs]
    have hpi := Real.pi_pos
    calc 2 * (-r) = (2 / Real.pi) * (Real.pi * (-r)) := by field_simp
      _ ≤ Real.sin (Real.pi * (-r)) := hj

/-- Lower bound for the modulus of `e(α) - 1`. -/
theorem four_mul_distToInt_le_norm_ee_sub_one (x : ℝ) :
    4 * distToInt x ≤ ‖ee x - 1‖ := by
  rw [norm_ee_sub_one]
  have := two_mul_distToInt_le_abs_sin x
  linarith

/-- **The linear exponential sum bound.**  If `α` is at distance `d > 0` from the integers, then
`‖Σ_{n<N} e(αn)‖ ≤ 1/(2d)`, uniformly in `N`. -/
theorem norm_sum_ee_le (α : ℝ) (N : ℕ) (hd : 0 < distToInt α) :
    ‖∑ n ∈ range N, ee ((n : ℝ) * α)‖ ≤ 1 / (2 * distToInt α) := by
  have hne : ee α - 1 ≠ 0 := by
    intro h
    have := four_mul_distToInt_le_norm_ee_sub_one α
    rw [h, norm_zero] at this
    linarith
  have hne1 : ee α ≠ 1 := fun h => hne (by rw [h]; ring)
  have hgeom : ∑ n ∈ range N, ee ((n : ℝ) * α) = ((ee α) ^ N - 1) / (ee α - 1) := by
    rw [← geom_sum_eq hne1 N]
    exact Finset.sum_congr rfl fun n _ => ee_natMul α n
  rw [hgeom, norm_div]
  have hnum : ‖(ee α) ^ N - 1‖ ≤ 2 := by
    calc ‖(ee α) ^ N - 1‖ ≤ ‖(ee α) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_ee, one_pow, norm_one]; norm_num
  have hden : 4 * distToInt α ≤ ‖ee α - 1‖ := four_mul_distToInt_le_norm_ee_sub_one α
  have hdenpos : (0:ℝ) < ‖ee α - 1‖ := by linarith
  rw [div_le_div_iff₀ hdenpos (by linarith)]
  nlinarith [hnum, hden, hdenpos, hd]

end HTGeometry
