import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Lee–Yang zero set of a two-prime self-reciprocal Dirichlet polynomial

For real `a` with `|a| < 1` put

`Y_a(s) = cosh((s − ½) log 6) + a cosh((s − ½) log(3/2))`,

so that `6^s P_a(s) = 2√6 · Y_a(s)` for the Dirichlet polynomial
`P_a(s) = 1 + 2a·4^{−s} + 3a·9^{−s} + 6·36^{−s}`.  On the critical line
`Y_a(½ + it) = cos(t log 6) + a cos(t log(3/2))`.  For `a ≠ 0` its zero set is the set of times at
which the Kronecker line `(2t log 2, 2t log 3)` meets a curve on the 2-torus, not a union of
arithmetic progressions.

This file contains the elementary analysis of `Y_a`:

* **Lee–Yang** (`re_eq_half_of_leeYang_eq_zero`): every zero of `Y_a` lies on `Re s = ½`.
  With `u = 4^{½−s}`, `v = 9^{½−s}`, `Y_a = ½ 6^{s−½}(1 + a(u + v) + uv)`, and
  `|1 + au|² − |a + u|² = (1 − a²)(1 − |u|²)` forbids a zero with `|u|, |v|` on the same side of `1`.
* **Edge bounds**: `|Y_a| ≥ 11/6` on `Re s = 3/2` and `Re s = −½`
  (`norm_leeYang_ge_of_re`), and `|Y_a| ≥ 1 − |a|` at the heights `Im s = 2πk/log 6`
  (`norm_leeYang_ge_of_im`), for every real part.
-/

open Complex

noncomputable section

namespace RHTower.LeeYang

/-- `L₁ = log 6`. -/
def L₁ : ℝ := Real.log 6

/-- `L₂ = log(3/2)`. -/
def L₂ : ℝ := Real.log (3 / 2)

theorem L₁_pos : 0 < L₁ := Real.log_pos (by norm_num)

theorem L₂_pos : 0 < L₂ := Real.log_pos (by norm_num)

theorem L₂_le_L₁ : L₂ ≤ L₁ := Real.log_le_log (by norm_num) (by norm_num)

/-- `Y_a(s) = cosh((s − ½) log 6) + a cosh((s − ½) log(3/2))`. -/
def leeYang (a : ℝ) (s : ℂ) : ℂ :=
  Complex.cosh ((s - 1 / 2) * L₁) + a * Complex.cosh ((s - 1 / 2) * L₂)

theorem differentiable_leeYang (a : ℝ) : Differentiable ℂ (leeYang a) := by
  unfold leeYang
  fun_prop

/-! ## Norms of `cosh` -/

theorem cosh_add_mul_I_eq (x y : ℝ) :
    Complex.cosh ((x : ℂ) + y * I) =
      ((Real.cosh x * Real.cos y : ℝ) : ℂ) + ((Real.sinh x * Real.sin y : ℝ) : ℂ) * I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

theorem norm_cosh_sq (x y : ℝ) :
    ‖Complex.cosh ((x : ℂ) + y * I)‖ ^ 2 = Real.sinh x ^ 2 + Real.cos y ^ 2 := by
  rw [cosh_add_mul_I_eq, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.add_im, Complex.mul_im,
    add_zero, zero_add]
  have h1 := Real.cosh_sq x
  have h2 := Real.sin_sq_add_cos_sq y
  nlinarith [h1, h2]

theorem abs_sinh_le_norm_cosh (x y : ℝ) : |Real.sinh x| ≤ ‖Complex.cosh ((x : ℂ) + y * I)‖ := by
  have h := norm_cosh_sq x y
  have : |Real.sinh x| ^ 2 ≤ ‖Complex.cosh ((x : ℂ) + y * I)‖ ^ 2 := by
    rw [sq_abs]; nlinarith [sq_nonneg (Real.cos y)]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp this

theorem norm_cosh_le (x y : ℝ) : ‖Complex.cosh ((x : ℂ) + y * I)‖ ≤ Real.cosh x := by
  have h := norm_cosh_sq x y
  have hc := Real.cosh_sq x
  have hcos := Real.cos_sq_le_one y
  have : ‖Complex.cosh ((x : ℂ) + y * I)‖ ^ 2 ≤ Real.cosh x ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.cosh_pos x).le two_ne_zero).mp this

theorem sub_half_mul_eq (s : ℂ) (L : ℝ) :
    (s - 1 / 2) * L = (((s.re - 1 / 2) * L : ℝ) : ℂ) + ((s.im * L : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-! ## Lee–Yang: the zeros lie on the critical line -/

theorem normSq_one_add_mul_sub (a : ℝ) (u : ℂ) :
    ‖1 + (a : ℂ) * u‖ ^ 2 - ‖(a : ℂ) + u‖ ^ 2 = (1 - a ^ 2) * (1 - ‖u‖ ^ 2) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.one_im, Complex.mul_im,
    add_zero, zero_add]
  ring

/-- If `1 + a(u + v) + uv = 0` with real `|a| < 1`, then `|u|` and `|v|` are not both `< 1`,
and not both `> 1`. -/
theorem leeYang_two_variable {a : ℝ} (ha : |a| < 1) {u v : ℂ}
    (h : 1 + (a : ℂ) * (u + v) + u * v = 0) :
    ¬ (‖u‖ < 1 ∧ ‖v‖ < 1) ∧ ¬ (1 < ‖u‖ ∧ 1 < ‖v‖) := by
  have hrel : v * ((a : ℂ) + u) = -(1 + (a : ℂ) * u) := by linear_combination h
  have hnorm : ‖v‖ * ‖(a : ℂ) + u‖ = ‖1 + (a : ℂ) * u‖ := by
    rw [← norm_mul, hrel, norm_neg]
  have hid := normSq_one_add_mul_sub a u
  have ha2 : 0 < 1 - a ^ 2 := by
    have : a ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg a]
    linarith
  have hu0 := norm_nonneg u
  have hv0 := norm_nonneg v
  have hau0 := norm_nonneg ((a : ℂ) + u)
  have h1au0 := norm_nonneg (1 + (a : ℂ) * u)
  constructor
  · rintro ⟨hu, hv⟩
    have hpos : 0 < (1 - a ^ 2) * (1 - ‖u‖ ^ 2) := by
      apply mul_pos ha2; nlinarith
    have hle : ‖1 + (a : ℂ) * u‖ ≤ ‖(a : ℂ) + u‖ := by
      rw [← hnorm]; nlinarith
    nlinarith
  · rintro ⟨hu, hv⟩
    have hneg : (1 - a ^ 2) * (1 - ‖u‖ ^ 2) < 0 := by
      apply mul_neg_of_pos_of_neg ha2; nlinarith
    have hlt : ‖1 + (a : ℂ) * u‖ < ‖(a : ℂ) + u‖ := by
      by_contra hc
      push Not at hc
      nlinarith
    rw [← hnorm] at hlt
    have hau : 0 < ‖(a : ℂ) + u‖ := lt_of_le_of_lt (by positivity) hlt
    nlinarith

/-- `2 e^{−L₁ w} Y_a = 1 + a(u + v) + uv` with `u = e^{(L₂−L₁)w}`, `v = e^{−(L₂+L₁)w}`,
`w = s − ½`. -/
theorem two_mul_exp_mul_leeYang (a : ℝ) (s : ℂ) :
    2 * Complex.exp (-((s - 1 / 2) * L₁)) * leeYang a s =
      1 + (a : ℂ) * (Complex.exp ((s - 1 / 2) * (L₂ - L₁)) +
        Complex.exp (-((s - 1 / 2) * (L₂ + L₁)))) +
        Complex.exp ((s - 1 / 2) * (L₂ - L₁)) * Complex.exp (-((s - 1 / 2) * (L₂ + L₁))) := by
  unfold leeYang
  set A := Complex.exp ((s - 1 / 2) * L₁) with hA
  set B := Complex.exp ((s - 1 / 2) * L₂) with hB
  have hA0 : A ≠ 0 := Complex.exp_ne_zero _
  have hB0 : B ≠ 0 := Complex.exp_ne_zero _
  have c1 : Complex.cosh ((s - 1 / 2) * L₁) = (A + A⁻¹) / 2 := by
    have := Complex.two_cosh ((s - 1 / 2) * L₁)
    rw [Complex.exp_neg, ← hA] at this
    linear_combination this / 2
  have c2 : Complex.cosh ((s - 1 / 2) * L₂) = (B + B⁻¹) / 2 := by
    have := Complex.two_cosh ((s - 1 / 2) * L₂)
    rw [Complex.exp_neg, ← hB] at this
    linear_combination this / 2
  have e1 : Complex.exp (-((s - 1 / 2) * L₁)) = A⁻¹ := by rw [Complex.exp_neg]
  have e2 : Complex.exp ((s - 1 / 2) * ((L₂ : ℂ) - L₁)) = B * A⁻¹ := by
    rw [show (s - 1 / 2) * ((L₂ : ℂ) - L₁) = (s - 1 / 2) * L₂ - (s - 1 / 2) * L₁ by ring,
      Complex.exp_sub, div_eq_mul_inv]
  have e3 : Complex.exp (-((s - 1 / 2) * ((L₂ : ℂ) + L₁))) = (A * B)⁻¹ := by
    rw [show -((s - 1 / 2) * ((L₂ : ℂ) + L₁)) = -((s - 1 / 2) * L₁ + (s - 1 / 2) * L₂) by ring,
      Complex.exp_neg, Complex.exp_add]
  rw [c1, c2, e1, e2, e3]
  field_simp
  ring

/-- **Lee–Yang.**  For real `|a| < 1`, every zero of `Y_a` lies on the critical line. -/
theorem re_eq_half_of_leeYang_eq_zero {a : ℝ} (ha : |a| < 1) {s : ℂ}
    (hs : leeYang a s = 0) : s.re = 1 / 2 := by
  have h := two_mul_exp_mul_leeYang a s
  rw [hs, mul_zero] at h
  have hLY := leeYang_two_variable ha h.symm
  set x := s.re - 1 / 2 with hx
  have hu : ‖Complex.exp ((s - 1 / 2) * (L₂ - L₁))‖ = Real.exp (x * (L₂ - L₁)) := by
    rw [Complex.norm_exp]; congr 1; simp [hx]
  have hv : ‖Complex.exp (-((s - 1 / 2) * (L₂ + L₁)))‖ = Real.exp (-(x * (L₂ + L₁))) := by
    rw [Complex.norm_exp]; congr 1; simp [hx]
  rw [hu, hv] at hLY
  have h21 : L₂ - L₁ < 0 := by
    have : L₂ < L₁ := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  have h21' : 0 < L₂ + L₁ := by linarith [L₁_pos, L₂_pos]
  by_contra hne
  rcases lt_or_gt_of_ne (show x ≠ 0 by intro h0; exact hne (by linarith)) with hneg | hpos
  · refine hLY.2 ⟨?_, ?_⟩
    · rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (mul_pos_of_neg_of_neg hneg h21)
    · rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)
  · refine hLY.1 ⟨?_, ?_⟩
    · rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (mul_neg_of_pos_of_neg hpos h21)
    · rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)

/-! ## Edge bounds -/

theorem sinh_L₁ : Real.sinh L₁ = 35 / 12 := by
  rw [L₁, Real.sinh_log (by norm_num)]; norm_num

theorem cosh_L₂ : Real.cosh L₂ = 13 / 12 := by
  rw [L₂, Real.cosh_log (by norm_num)]; norm_num

/-- On `Re s = 3/2` and `Re s = −½`: `|Y_a(s)| ≥ 11/6` for `|a| ≤ 1`. -/
theorem norm_leeYang_ge_of_re {a : ℝ} (ha : |a| ≤ 1) {s : ℂ}
    (hs : s.re = 3 / 2 ∨ s.re = -1 / 2) : 11 / 6 ≤ ‖leeYang a s‖ := by
  have hx : |s.re - 1 / 2| = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  unfold leeYang
  rw [sub_half_mul_eq s L₁, sub_half_mul_eq s L₂]
  have h1 := abs_sinh_le_norm_cosh ((s.re - 1 / 2) * L₁) (s.im * L₁)
  have h2 := norm_cosh_le ((s.re - 1 / 2) * L₂) (s.im * L₂)
  have hs1 : |Real.sinh ((s.re - 1 / 2) * L₁)| = 35 / 12 := by
    rw [Real.abs_sinh, abs_mul, hx, one_mul, abs_of_pos L₁_pos, sinh_L₁]
  have hc2 : Real.cosh ((s.re - 1 / 2) * L₂) = 13 / 12 := by
    rw [← Real.cosh_abs, abs_mul, hx, one_mul, abs_of_pos L₂_pos, cosh_L₂]
  rw [hs1] at h1
  rw [hc2] at h2
  have hn : ‖(a : ℂ) * Complex.cosh ((((s.re - 1 / 2) * L₂ : ℝ) : ℂ) + ((s.im * L₂ : ℝ) : ℂ) * I)‖
      ≤ 13 / 12 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |a| * _ ≤ 1 * (13 / 12) := by gcongr
      _ = 13 / 12 := one_mul _
  have := norm_sub_norm_le
    (Complex.cosh ((((s.re - 1 / 2) * L₁ : ℝ) : ℂ) + ((s.im * L₁ : ℝ) : ℂ) * I))
    (-((a : ℂ) * Complex.cosh ((((s.re - 1 / 2) * L₂ : ℝ) : ℂ) + ((s.im * L₂ : ℝ) : ℂ) * I)))
  rw [sub_neg_eq_add, norm_neg] at this
  linarith

/-- At the heights `Im s = 2πk/log 6`: `|Y_a(s)| ≥ 1 − |a|`, for every real part. -/
theorem norm_leeYang_ge_of_im {a : ℝ} {s : ℂ} (k : ℤ) (hs : s.im = 2 * Real.pi * k / L₁) :
    1 - |a| ≤ ‖leeYang a s‖ := by
  unfold leeYang
  rw [sub_half_mul_eq s L₁, sub_half_mul_eq s L₂]
  have hy : s.im * L₁ = (k : ℝ) * (2 * Real.pi) := by
    rw [hs]; field_simp [L₁_pos.ne']
  have hcosh : Complex.cosh ((((s.re - 1 / 2) * L₁ : ℝ) : ℂ) + ((s.im * L₁ : ℝ) : ℂ) * I) =
      ((Real.cosh ((s.re - 1 / 2) * L₁) : ℝ) : ℂ) := by
    rw [cosh_add_mul_I_eq, hy, Real.cos_int_mul_two_pi,
      show (k : ℝ) * (2 * Real.pi) = ((2 * k : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi]
    simp
  rw [hcosh]
  have h2 := norm_cosh_le ((s.re - 1 / 2) * L₂) (s.im * L₂)
  have hc : Real.cosh ((s.re - 1 / 2) * L₂) ≤ Real.cosh ((s.re - 1 / 2) * L₁) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos L₂_pos, abs_of_pos L₁_pos]
    exact mul_le_mul_of_nonneg_left L₂_le_L₁ (abs_nonneg _)
  have hC1 : 1 ≤ Real.cosh ((s.re - 1 / 2) * L₁) := Real.one_le_cosh _
  have hn : ‖(a : ℂ) * Complex.cosh ((((s.re - 1 / 2) * L₂ : ℝ) : ℂ) + ((s.im * L₂ : ℝ) : ℂ) * I)‖
      ≤ |a| * Real.cosh ((s.re - 1 / 2) * L₁) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (h2.trans hc) (abs_nonneg a)
  have := norm_sub_norm_le (((Real.cosh ((s.re - 1 / 2) * L₁) : ℝ) : ℂ))
    (-((a : ℂ) * Complex.cosh ((((s.re - 1 / 2) * L₂ : ℝ) : ℂ) + ((s.im * L₂ : ℝ) : ℂ) * I)))
  rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _)] at this
  rcases le_or_gt |a| 1 with h | h
  · nlinarith [mul_le_mul_of_nonneg_left hC1 (sub_nonneg.mpr h)]
  · linarith [norm_nonneg (((Real.cosh ((s.re - 1 / 2) * L₁) : ℝ) : ℂ) +
      (a : ℂ) * Complex.cosh ((((s.re - 1 / 2) * L₂ : ℝ) : ℂ) + ((s.im * L₂ : ℝ) : ℂ) * I))]

end RHTower.LeeYang
