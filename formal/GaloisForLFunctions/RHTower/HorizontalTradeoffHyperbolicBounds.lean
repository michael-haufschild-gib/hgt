import GaloisForLFunctions.RHTower.CothInfra

/-!
# Hyperbolic and trigonometric inequalities for the horizontal tradeoff

* `three_mul_cosh_le`: `3t cosh t ≤ (3 + t²) sinh t` for `t ≥ 0`, i.e. `tanh t ≥ 3t/(3 + t²)`.
* `add_cube_div_six_le_sinh`: `x + x³/6 ≤ sinh x` for `x ≥ 0`.
* `pade_ratio_le`: `6(6 + x²)·x(x + sinh x) ≤ (12 + x²)²(cosh x − 1)` for `x ≥ 0`.
* `deficit_sharp`: `(1 − y/24)·y(y + sinh y) ≤ (32/5)(cosh y − 1)` for `y ≥ 0`.
  On `[0,5]` this follows from `pade_ratio_le`. On `[5,24]` it is a quadratic inequality in
  `E = e^y` that holds once `E ≥ y⁴/24`.
* `window_constant_four_fifths`: `4 sin θ ≤ 5θ cos θ` for `0 ≤ θ`, `θ² ≤ 1/2`.
* `sinh_mul_cosh_add_sub_le`: `sinh t·(cosh(t + b) − cosh t) ≤ t` for `0 ≤ t ≤ 12`,
  `0 ≤ b`, `b e²⁵ ≤ 1`.
-/

open Real

namespace RHTower

noncomputable section

/-- **Padé lower bound for `tanh`.** `3t cosh t ≤ (3 + t²) sinh t` for `t ≥ 0`. -/
theorem three_mul_cosh_le {t : ℝ} (ht : 0 ≤ t) :
    3 * t * Real.cosh t ≤ (3 + t ^ 2) * Real.sinh t := by
  have hg : ∀ s, HasDerivAt (fun t => (3 + t * t) * Real.sinh t - 3 * t * Real.cosh t)
      (s * (s * Real.cosh s - Real.sinh s)) s := by
    intro s
    have h : HasDerivAt (fun t => (3 + t * t) * Real.sinh t - 3 * t * Real.cosh t)
        ((1 * s + s * 1) * Real.sinh s + (3 + s * s) * Real.cosh s
          - ((3 * 1) * Real.cosh s + 3 * s * Real.sinh s)) s :=
      ((((hasDerivAt_id' s).mul (hasDerivAt_id' s)).const_add 3).mul
        (Real.hasDerivAt_sinh s)).sub (((hasDerivAt_id' s).const_mul 3).mul (Real.hasDerivAt_cosh s))
    exact h.congr_deriv (by ring)
  have hmono : MonotoneOn (fun t => (3 + t * t) * Real.sinh t - 3 * t * Real.cosh t)
      (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun s _ => (hg s).continuousAt.continuousWithinAt
    · exact fun s _ => (hg s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hg s).deriv]
      have := sinh_le_mul_cosh (le_of_lt hs)
      exact mul_nonneg (le_of_lt hs) (by linarith)
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [Real.sinh_zero, mul_zero, zero_mul, sub_zero] at this
  nlinarith

/-- `1 + s²/2 ≤ cosh s` for `s ≥ 0`. -/
private theorem one_add_sq_div_two_le_cosh_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    1 + s ^ 2 / 2 ≤ Real.cosh s := by
  have h2 : Real.cosh s = 1 + 2 * Real.sinh (s / 2) ^ 2 := by
    have := Real.cosh_two_mul (s / 2)
    rw [show 2 * (s / 2) = s by ring, Real.cosh_sq] at this
    linarith
  have h3 : s / 2 ≤ Real.sinh (s / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have h4 : (s / 2) ^ 2 ≤ Real.sinh (s / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h3 2
  rw [h2]
  nlinarith

/-- `x + x³/6 ≤ sinh x` for `x ≥ 0`. -/
theorem add_cube_div_six_le_sinh {x : ℝ} (hx : 0 ≤ x) : x + x ^ 3 / 6 ≤ Real.sinh x := by
  have hg : ∀ s, HasDerivAt (fun t => Real.sinh t - t - t * t * t / 6)
      (Real.cosh s - 1 - s ^ 2 / 2) s := by
    intro s
    have h : HasDerivAt (fun t => Real.sinh t - t - t * t * t / 6)
        (Real.cosh s - 1 - ((1 * s + s * 1) * s + s * s * 1) / 6) s :=
      ((Real.hasDerivAt_sinh s).sub (hasDerivAt_id' s)).sub
        ((((hasDerivAt_id' s).mul (hasDerivAt_id' s)).mul (hasDerivAt_id' s)).div_const 6)
    exact h.congr_deriv (by ring)
  have hmono : MonotoneOn (fun t => Real.sinh t - t - t * t * t / 6) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun s _ => (hg s).continuousAt.continuousWithinAt
    · exact fun s _ => (hg s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hg s).deriv]
      linarith [one_add_sq_div_two_le_cosh_of_nonneg (le_of_lt hs)]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [Real.sinh_zero, sub_zero, mul_zero, zero_div] at this
  nlinarith

/-- **Padé ratio bound.** `6(6 + x²)·x(x + sinh x) ≤ (12 + x²)²(cosh x − 1)` for `x ≥ 0`. -/
theorem pade_ratio_le {x : ℝ} (hx : 0 ≤ x) :
    6 * (6 + x ^ 2) * (x * (x + Real.sinh x)) ≤ (12 + x ^ 2) ^ 2 * (Real.cosh x - 1) := by
  set S := Real.sinh (x / 2) with hS
  set C := Real.cosh (x / 2) with hC
  have hsh : Real.sinh x = 2 * S * C := by
    rw [hS, hC, ← Real.sinh_two_mul, show 2 * (x / 2) = x by ring]
  have hch : Real.cosh x - 1 = 2 * S ^ 2 := by
    have := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring, Real.cosh_sq] at this
    rw [this]; ring
  have hS0 : 0 ≤ S := Real.sinh_nonneg_iff.mpr (by linarith)
  have hA : x * (6 + x ^ 2) ≤ 12 * (S * C) := by
    have := add_cube_div_six_le_sinh hx
    rw [hsh] at this
    nlinarith
  have hB : 6 * x * C ≤ (12 + x ^ 2) * S := by
    have := three_mul_cosh_le (t := x / 2) (by linarith)
    nlinarith
  have hC1 : (x + 2 * (S * C)) * (6 + x ^ 2) ≤ 2 * (S * C) * (12 + x ^ 2) := by linarith
  have e1 := mul_le_mul_of_nonneg_left hC1 (by positivity : (0:ℝ) ≤ 6 * x)
  have e2 := mul_le_mul_of_nonneg_left hB (by positivity : (0:ℝ) ≤ 2 * S * (12 + x ^ 2))
  rw [hsh, hch]
  nlinarith

/-- `(1 − y/24)·y(y + sinh y) ≤ (32/5)(cosh y − 1)` on `[0, 5]`. -/
theorem deficit_sharp_small {y : ℝ} (h0 : 0 ≤ y) (h5 : y ≤ 5) :
    (1 - y / 24) * (y * (y + Real.sinh y)) ≤ 32 / 5 * (Real.cosh y - 1) := by
  have hp := pade_ratio_le h0
  have hpoly : (1 - y / 24) * (12 + y ^ 2) ^ 2 ≤ 192 / 5 * (6 + y ^ 2) := by
    nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ 5 - y), sq_nonneg (y - 3),
      mul_nonneg (mul_nonneg h0 h0) (by linarith : (0:ℝ) ≤ 5 - y),
      mul_nonneg (mul_nonneg (mul_nonneg h0 h0) h0) (by linarith : (0:ℝ) ≤ 5 - y)]
  have hc : 0 ≤ Real.cosh y - 1 := by linarith [Real.one_le_cosh y]
  have ha : 0 ≤ 1 - y / 24 := by linarith
  have h6 : 0 < 6 * (6 + y ^ 2) := by positivity
  have e1 := mul_le_mul_of_nonneg_left hp ha
  have e2 := mul_le_mul_of_nonneg_right hpoly hc
  have key : (1 - y / 24) * (y * (y + Real.sinh y)) * (6 * (6 + y ^ 2))
      ≤ 32 / 5 * (Real.cosh y - 1) * (6 * (6 + y ^ 2)) := by nlinarith
  exact le_of_mul_le_mul_right key h6

/-- The polynomial step of `deficit_sharp_large`. -/
private theorem deficit_sharp_poly {y : ℝ} (h5 : 5 ≤ y) :
    64 / 5 + 2 * ((1 - y / 24) * y) * y ≤ (32 / 5 - (1 - y / 24) * y) * (y ^ 4 / 24) := by
  nlinarith [sq_nonneg (y - 12), mul_nonneg (by linarith : (0:ℝ) ≤ y - 5) (sq_nonneg (y - 12)),
    mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ y - 5) (by linarith : (0:ℝ) ≤ y - 5))
      (sq_nonneg (y - 12)),
    mul_nonneg (by linarith : (0:ℝ) ≤ y - 5) (by linarith : (0:ℝ) ≤ y - 5),
    mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ y - 5) (by linarith : (0:ℝ) ≤ y - 5))
      (by linarith : (0:ℝ) ≤ y - 5)]

/-- `(1 − y/24)·y(y + sinh y) ≤ (32/5)(cosh y − 1)` on `[5, 24]`. -/
theorem deficit_sharp_large {y : ℝ} (h5 : 5 ≤ y) (h24 : y ≤ 24) :
    (1 - y / 24) * (y * (y + Real.sinh y)) ≤ 32 / 5 * (Real.cosh y - 1) := by
  set a := (1 - y / 24) * y with ha
  have ha6 : a ≤ 6 := by nlinarith [sq_nonneg (y - 12)]
  have ha0 : 0 ≤ a := mul_nonneg (by linarith) (by linarith)
  set E := Real.exp y with hE
  set F := Real.exp (-y) with hF
  have hEF : E * F = 1 := by rw [hE, hF, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hE0 : 0 < E := Real.exp_pos y
  have hF0 : 0 < F := Real.exp_pos _
  have hE4 : y ^ 4 / 24 ≤ E := by
    have := Real.pow_div_factorial_le_exp y (by linarith) 4
    norm_num [Nat.factorial] at this
    exact this
  have hpoly := deficit_sharp_poly h5
  rw [← ha] at hpoly
  have hlead : 64 / 5 + 2 * a * y ≤ (32 / 5 - a) * E :=
    hpoly.trans (mul_le_mul_of_nonneg_left hE4 (by linarith))
  -- the quadratic in `E`
  have hquad : 0 ≤ (32 / 5 - a) * E ^ 2 - (64 / 5 + 2 * a * y) * E + (32 / 5 + a) := by
    nlinarith [mul_le_mul_of_nonneg_left hlead hE0.le]
  rw [Real.sinh_eq, Real.cosh_eq, ← hE, ← hF,
    show (1 - y / 24) * (y * (y + (E - F) / 2)) = a * (y + (E - F) / 2) by rw [ha]; ring]
  have key : 2 * E * (a * (y + (E - F) / 2)) ≤ 2 * E * (32 / 5 * ((E + F) / 2 - 1)) := by
    have e1 : 2 * E * (a * (y + (E - F) / 2)) = a * (2 * y * E + E ^ 2 - 1) := by
      have : E * F = 1 := hEF
      linear_combination (-a) * this
    have e2 : 2 * E * (32 / 5 * ((E + F) / 2 - 1)) = 32 / 5 * (E ^ 2 + 1 - 2 * E) := by
      have : E * F = 1 := hEF
      linear_combination (32 / 5) * this
    rw [e1, e2]
    nlinarith
  exact le_of_mul_le_mul_left key (by positivity : (0:ℝ) < 2 * E)

/-- **The sharp deficit inequality.** `(1 − y/24)·y(y + sinh y) ≤ (32/5)(cosh y − 1)` for
`y ≥ 0`. -/
theorem deficit_sharp {y : ℝ} (h0 : 0 ≤ y) :
    (1 - y / 24) * (y * (y + Real.sinh y)) ≤ 32 / 5 * (Real.cosh y - 1) := by
  rcases le_or_gt y 5 with h5 | h5
  · exact deficit_sharp_small h0 h5
  rcases le_or_gt y 24 with h24 | h24
  · exact deficit_sharp_large h5.le h24
  have h1 : 1 - y / 24 ≤ 0 := by linarith
  have h2 : 0 ≤ y * (y + Real.sinh y) :=
    mul_nonneg h0 (by linarith [Real.sinh_nonneg_iff.mpr h0])
  have h3 : 0 ≤ Real.cosh y - 1 := by linarith [Real.one_le_cosh y]
  nlinarith

/-- **The window constant.** `4 sin θ ≤ 5θ cos θ` for `0 ≤ θ`, `θ² ≤ 1/2`. -/
theorem window_constant_four_fifths {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ^ 2 ≤ 1 / 2) :
    4 * Real.sin θ ≤ 5 * θ * Real.cos θ := by
  have hθ1 : θ ≤ 1 := by nlinarith
  have hcos : 1 - θ ^ 2 / 2 - θ ^ 4 * (5 / 96) ≤ Real.cos θ := by
    have h := Real.cos_bound (x := θ) (by rw [abs_of_nonneg h0]; exact hθ1)
    rw [abs_of_nonneg h0] at h
    linarith [(abs_le.mp h).1]
  have hsin : Real.sin θ ≤ θ - θ ^ 3 / 6 + θ ^ 5 / 100 := by
    have h := Real.sin_bound (x := θ) (by rw [abs_of_nonneg h0]; exact hθ1)
    rw [abs_of_nonneg h0] at h
    linarith [(abs_le.mp h).2]
  have hu : 0 ≤ 1 / 2 - θ ^ 2 := by linarith
  have hpoly : 4 * (θ - θ ^ 3 / 6 + θ ^ 5 / 100) ≤ 5 * θ * (1 - θ ^ 2 / 2 - θ ^ 4 * (5 / 96)) := by
    nlinarith [mul_nonneg h0 hu, mul_nonneg (mul_nonneg h0 hu) (sq_nonneg θ),
      mul_nonneg (mul_nonneg h0 hu) hu, pow_nonneg h0 3, pow_nonneg h0 5]
  nlinarith [mul_le_mul_of_nonneg_left hcos (by positivity : (0:ℝ) ≤ 5 * θ)]

/-- `sinh t·(cosh(t + b) − cosh t) ≤ t` for `0 ≤ t ≤ 12`, `0 ≤ b`, `b e²⁵ ≤ 1`. -/
theorem sinh_mul_cosh_add_sub_le {t b : ℝ} (ht : 0 ≤ t) (ht12 : t ≤ 12) (hb : 0 ≤ b)
    (hbe : b * Real.exp 25 ≤ 1) :
    Real.sinh t * (Real.cosh (t + b) - Real.cosh t) ≤ t := by
  have hb1 : b ≤ 1 := by
    have : 1 ≤ Real.exp 25 := Real.one_le_exp (by norm_num)
    nlinarith
  -- `cosh(t + b) − cosh t ≤ eᵗ (eᵇ − 1)/2 ≤ eᵗ b eᵇ/2`
  have hdiff : Real.cosh (t + b) - Real.cosh t ≤ Real.exp t * (b * Real.exp b) / 2 := by
    rw [Real.cosh_eq, Real.cosh_eq]
    have e1 : Real.exp (-(t + b)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
    have e2 : Real.exp b - 1 ≤ b * Real.exp b := by
      have h := Real.add_one_le_exp (-b)
      have h2 : Real.exp (-b) * Real.exp b = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      nlinarith [Real.exp_pos b]
    have e3 : Real.exp (t + b) = Real.exp t * Real.exp b := Real.exp_add t b
    rw [e3]
    nlinarith [Real.exp_pos t]
  -- `sinh t ≤ t eᵗ`
  have hs : Real.sinh t ≤ t * Real.exp t := by
    have h1 := sinh_le_mul_cosh ht
    have h2 : Real.cosh t ≤ Real.exp t := by
      rw [Real.cosh_eq]
      have : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
      linarith
    nlinarith
  have hs0 : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht
  have hd0 : 0 ≤ Real.cosh (t + b) - Real.cosh t := by
    rw [sub_nonneg, Real.cosh_le_cosh, abs_of_nonneg ht, abs_of_nonneg (by linarith)]
    linarith
  -- `e^{2t + b} ≤ e²⁵`
  have hexp : Real.exp t * Real.exp t * Real.exp b ≤ Real.exp 25 := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h1 : Real.sinh t * (Real.cosh (t + b) - Real.cosh t)
      ≤ t * Real.exp t * (Real.exp t * (b * Real.exp b) / 2) :=
    mul_le_mul hs hdiff hd0 (by positivity)
  have h2 : t * Real.exp t * (Real.exp t * (b * Real.exp b) / 2)
      = t * b * (Real.exp t * Real.exp t * Real.exp b) / 2 := by ring
  have h3 : t * b * (Real.exp t * Real.exp t * Real.exp b) ≤ t * b * Real.exp 25 :=
    mul_le_mul_of_nonneg_left hexp (mul_nonneg ht hb)
  have h4 : t * b * Real.exp 25 ≤ t := by nlinarith
  linarith

end

end RHTower
