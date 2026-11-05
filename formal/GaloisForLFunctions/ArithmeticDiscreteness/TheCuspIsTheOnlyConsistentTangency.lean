import Mathlib

/-!
# The cusp is the only consistent tangency

For the cusp carrier `D(s) = (1 − 2^{−s})² − (1 − 3^{−s})³` the Bohr lift is
`G(x, y) = (1 − x)² − (1 − y)³` and the tangency form is
`H(x, y) = 2(1 − x) log 2 · x − 3(1 − y)² log 3 · y`. A point is **consistent** if
`|x| = 2^{−σ}`, `|y| = 3^{−σ}` for one real `σ`.

* **Only the cusp** (`cusp_consistent_tangency_eq`). A consistent point with `G = H = 0` is
  `(1, 1)`. With `a = 1 − x`, `b = 1 − y`, `a² = b³` gives `a = τ³`, `b = τ²`, and `H = 0` becomes
  `τ³ (τ − 1)(Pτ² + Pτ − 2 log 2) = 0`, `P = 3 log 3 − 2 log 2`. The root `τ = 1` has `x = 0`. The
  quadratic has the real roots `τ_± = −½ ± √(κ + ¼)`, `κ = 2 log 2/P < 1`:
  * `τ_− < −1` gives `x > 2` but `|y| < 3`, impossible for one `σ`;
  * `0 < τ_+ < log 2/log 3`, and consistency would force `log 3 · f = log 2 · g` with
    `f = −log(1 − τ³) ≤ τ g` (`neg_log_one_sub_cube_le`, termwise on the logarithm series),
    hence `τ ≥ log 2/log 3`. The bound `τ_+ < log 2/log 3` is
    `(log 3 − log 2)(log 3 + 2 log 2) > 0`.

No numerical value of a logarithm is used: only `log 2 < log 3` and positivity.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- **The logarithm series inequality** `−log(1 − u³) ≤ u · (−log(1 − u²))` on `[0, 1)`. -/
theorem neg_log_one_sub_cube_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    -Real.log (1 - u ^ 3) ≤ u * -Real.log (1 - u ^ 2) := by
  have h3 : |u ^ 3| < 1 := by
    rw [abs_of_nonneg (by positivity)]; exact pow_lt_one₀ hu0 hu1 (by norm_num)
  have h2 : |u ^ 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]; exact pow_lt_one₀ hu0 hu1 (by norm_num)
  have hs3 := Real.hasSum_pow_div_log_of_abs_lt_one h3
  have hs2 := (Real.hasSum_pow_div_log_of_abs_lt_one h2).mul_left u
  refine hasSum_le (fun n => ?_) hs3 hs2
  rw [mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [← pow_mul, ← pow_mul, ← pow_succ']
  exact pow_le_pow_of_le_one hu0 hu1.le (by omega)

/-- The root `τ_− ∈ (−2, −1)` is inconsistent: `|1 − τ³| > 2` forces `σ < −1`, but `|1 − τ²| < 3`. -/
theorem minus_root_inconsistent {u σ : ℝ} (hum1 : u < -1) (hum2 : -2 < u)
    (hx : |1 - u ^ 3| = (2 : ℝ) ^ (-σ)) (hy : |1 - u ^ 2| = (3 : ℝ) ^ (-σ)) : False := by
  have hx2 : 2 < 1 - u ^ 3 := by nlinarith
  have hy3 : |1 - u ^ 2| < 3 := by
    rw [abs_lt]; constructor <;> nlinarith
  rw [abs_of_pos (by linarith)] at hx
  have hσ : 1 < -σ := by
    by_contra hle
    rw [not_lt] at hle
    have : (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    rw [Real.rpow_one] at this
    linarith
  have : (3 : ℝ) ^ (1 : ℝ) < (3 : ℝ) ^ (-σ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hσ
  rw [Real.rpow_one] at this
  linarith

/-- **The cusp is the only consistent tangency.** -/
theorem cusp_consistent_tangency_eq {x y : ℂ} {σ : ℝ}
    (hx : ‖x‖ = (2 : ℝ) ^ (-σ)) (hy : ‖y‖ = (3 : ℝ) ^ (-σ))
    (hG : (1 - x) ^ 2 - (1 - y) ^ 3 = 0)
    (hH : 2 * (1 - x) * (((Real.log 2 : ℝ) : ℂ) * x) -
      3 * (1 - y) ^ 2 * (((Real.log 3 : ℝ) : ℂ) * y) = 0) :
    x = 1 ∧ y = 1 := by
  set L₂ := Real.log 2 with hL₂
  set L₃ := Real.log 3 with hL₃
  have hl2 : 0 < L₂ := Real.log_pos (by norm_num)
  have hl23 : L₂ < L₃ := Real.log_lt_log (by norm_num) (by norm_num)
  obtain ⟨a, ha⟩ : ∃ a, a = 1 - x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = 1 - y := ⟨_, rfl⟩
  have hab : a ^ 2 = b ^ 3 := by rw [ha, hb]; linear_combination hG
  have hH' : 2 * a * ((L₂ : ℂ) * x) - 3 * b ^ 2 * ((L₃ : ℂ) * y) = 0 := by rw [ha, hb]; exact hH
  by_cases hb0 : b = 0
  · have ha0 : a = 0 := by
      have : a ^ 2 = 0 := by rw [hab, hb0]; ring
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    exact ⟨by rw [ha] at ha0; linear_combination -ha0, by rw [hb] at hb0; linear_combination -hb0⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = a / b := ⟨_, rfl⟩
  have hτ2 : τ ^ 2 = b := by
    rw [hτ, div_pow, hab]; field_simp
  have hτ3 : τ ^ 3 = a := by
    rw [show τ ^ 3 = τ * τ ^ 2 by ring, hτ2, hτ]; field_simp
  have hτ0 : τ ≠ 0 := by rintro h; rw [h] at hτ2; exact hb0 (by rw [← hτ2]; ring)
  have hxτ : x = 1 - τ ^ 3 := by rw [hτ3, ha]; ring
  have hyτ : y = 1 - τ ^ 2 := by rw [hτ2, hb]; ring
  have hHτ : 2 * τ ^ 3 * ((L₂ : ℂ) * (1 - τ ^ 3)) - 3 * (τ ^ 2) ^ 2 * ((L₃ : ℂ) * (1 - τ ^ 2)) = 0 := by
    rw [hxτ, hyτ, ← hτ3, ← hτ2] at hH'
    exact hH'
  -- the tangency equation in `τ`
  set P : ℝ := 3 * L₃ - 2 * L₂ with hP
  have hP0 : 0 < P := by rw [hP]; linarith
  have hcubic : (τ - 1) * ((P : ℂ) * τ ^ 2 + (P : ℂ) * τ - 2 * (L₂ : ℂ)) = 0 := by
    have h1 : τ ^ 3 * ((τ - 1) * ((P : ℂ) * τ ^ 2 + (P : ℂ) * τ - 2 * (L₂ : ℂ))) = 0 := by
      rw [hP]; push_cast
      linear_combination hHτ
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 3 hτ0)
  have hσx : 0 < (2 : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by norm_num) _
  rcases mul_eq_zero.mp hcubic with h1 | hq
  · -- `τ = 1` gives `x = 0`
    exfalso
    have : x = 0 := by rw [hxτ, sub_eq_zero.mp h1]; ring
    rw [this, norm_zero] at hx
    linarith
  -- the quadratic: `(τ + ½)² = κ + ¼`
  set κ : ℝ := 2 * L₂ / P with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ < 2 := by rw [hκ, div_lt_iff₀ hP0, hP]; linarith
  set v : ℝ := Real.sqrt (κ + 1 / 4) with hv
  have hv2 : v ^ 2 = κ + 1 / 4 := Real.sq_sqrt (by linarith)
  have hvhalf : 1 / 2 < v := by
    rw [hv, Real.lt_sqrt (by norm_num)]; linarith
  have hv32 : v < 3 / 2 := by
    rw [hv, Real.sqrt_lt' (by norm_num)]; linarith
  have hsq : (τ + 1 / 2) ^ 2 = ((v : ℝ) : ℂ) ^ 2 := by
    have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP0.ne'
    have hτsum : τ ^ 2 + τ = (2 * (L₂ : ℂ)) / (P : ℂ) := by
      rw [eq_div_iff hPc]; linear_combination hq
    have : (τ + 1 / 2) ^ 2 = ((κ + 1 / 4 : ℝ) : ℂ) := by
      rw [hκ]; push_cast; linear_combination hτsum
    rw [this, ← Complex.ofReal_pow, hv2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hpl | hmi
  · -- `τ = −½ + v ∈ (0, log 2/log 3)`
    exfalso
    set u : ℝ := -1 / 2 + v with hu
    have hτu : τ = (u : ℂ) := by rw [hu]; push_cast; linear_combination hpl
    have hu0 : 0 < u := by rw [hu]; linarith
    have hu1 : u < 1 := by rw [hu]; linarith
    -- `u < log 2 / log 3`
    have hl3 : 0 < L₃ := by linarith
    have hur : u * L₃ < L₂ := by
      have hr : κ < (L₂ / L₃) ^ 2 + L₂ / L₃ := by
        have hnum : 0 < L₂ * ((L₃ - L₂) * (L₃ + 2 * L₂)) := by
          have : 0 < (L₃ - L₂) * (L₃ + 2 * L₂) := mul_pos (by linarith) (by linarith)
          positivity
        rw [hκ, hP, div_lt_iff₀ (by linarith)]
        have e : ((L₂ / L₃) ^ 2 + L₂ / L₃) * (3 * L₃ - 2 * L₂) - 2 * L₂ =
            L₂ * ((L₃ - L₂) * (L₃ + 2 * L₂)) / L₃ ^ 2 := by field_simp; ring
        have : 0 < L₂ * ((L₃ - L₂) * (L₃ + 2 * L₂)) / L₃ ^ 2 := by positivity
        linarith
      -- `v < L₂/L₃ + ½`
      have hvlt : v < L₂ / L₃ + 1 / 2 := by
        rw [hv, Real.sqrt_lt' (by positivity)]; nlinarith
      have : u < L₂ / L₃ := by rw [hu]; linarith
      rwa [lt_div_iff₀ hl3] at this
    -- consistency
    have hxr : x = ((1 - u ^ 3 : ℝ) : ℂ) := by rw [hxτ, hτu]; push_cast; ring
    have hyr : y = ((1 - u ^ 2 : ℝ) : ℂ) := by rw [hyτ, hτu]; push_cast; ring
    have hx1 : 0 < 1 - u ^ 3 := by nlinarith [pow_lt_one₀ hu0.le hu1 (by norm_num : 3 ≠ 0)]
    have hy1 : 0 < 1 - u ^ 2 := by nlinarith [pow_lt_one₀ hu0.le hu1 (by norm_num : 2 ≠ 0)]
    rw [hxr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx1] at hx
    rw [hyr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy1] at hy
    have hlx : Real.log (1 - u ^ 3) = -σ * L₂ := by
      rw [hx, Real.log_rpow (by norm_num)]
    have hly : Real.log (1 - u ^ 2) = -σ * L₃ := by
      rw [hy, Real.log_rpow (by norm_num)]
    have hkey := neg_log_one_sub_cube_le hu0.le hu1
    rw [hlx, hly] at hkey
    -- `σ L₂ ≤ u σ L₃` with `σ > 0`
    have hσ : 0 < σ := by
      have : Real.log (1 - u ^ 2) < 0 :=
        Real.log_neg hy1 (by nlinarith)
      rw [hly] at this; nlinarith
    nlinarith
  · -- `τ = −½ − v < −1`
    exfalso
    set u : ℝ := -1 / 2 - v with hu
    have hτu : τ = (u : ℂ) := by rw [hu]; push_cast; linear_combination hmi
    have hum1 : u < -1 := by rw [hu]; linarith
    have hum2 : -2 < u := by rw [hu]; linarith
    have hxr : x = ((1 - u ^ 3 : ℝ) : ℂ) := by rw [hxτ, hτu]; push_cast; ring
    have hyr : y = ((1 - u ^ 2 : ℝ) : ℂ) := by rw [hyτ, hτu]; push_cast; ring
    rw [hxr, Complex.norm_real, Real.norm_eq_abs] at hx
    rw [hyr, Complex.norm_real, Real.norm_eq_abs] at hy
    exact minus_root_inconsistent hum1 hum2 hx hy

end GaloisForLFunctions.ArithmeticDiscreteness
