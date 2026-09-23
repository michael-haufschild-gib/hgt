import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodHeight
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlData

/-!
# The balanced height when the depth grows with the height

At a fixed depth `A` the contour balance puts the truncation height at `exp(2√(A log x))`.  When
the depth is `c·log log T/log T` the balance is a fixed point: the left edge saves
`c·log log T/log T·log x` and the truncation costs `1/T`, so `log T` must solve
`log²T ≍ c·log x·log log T`.  Taking

```text
chebHeightLl c x = exp(√(c·log x·log log x))
```

solves it up to a factor two, because `log log T = ½log(c·log x·log log x)` is between
`½log log x` and `log log x` in the relevant range.  The saving is then

```text
chebSavingLl c x = ½√(c·log x·log log x) ,
```

which is Littlewood's exponent: at `x = N` it is `≍ √(log N·log log N)`.
-/

namespace RHTower.Sieve

/-- The quantity the balance equates: `c·log x·log log x`. -/
noncomputable def chebQuadLl (c x : ℝ) : ℝ := c * (Real.log x * Real.log (Real.log x))

/-- The balanced truncation height when the depth grows with the height. -/
noncomputable def chebHeightLl (c x : ℝ) : ℝ := Real.exp (Real.sqrt (chebQuadLl c x))

/-- Half the height's logarithm: the exponent of the saving. -/
noncomputable def chebSavingLl (c x : ℝ) : ℝ := Real.sqrt (chebQuadLl c x) / 2

theorem chebHeightLl_pos (c x : ℝ) : 0 < chebHeightLl c x := Real.exp_pos _

theorem one_le_chebHeightLl (c x : ℝ) : 1 ≤ chebHeightLl c x := by
  rw [chebHeightLl]
  exact Real.one_le_exp (Real.sqrt_nonneg _)

theorem chebSavingLl_nonneg (c x : ℝ) : 0 ≤ chebSavingLl c x := by
  rw [chebSavingLl]; positivity

theorem log_chebHeightLl (c x : ℝ) :
    Real.log (chebHeightLl c x) = 2 * chebSavingLl c x := by
  rw [chebHeightLl, Real.log_exp, chebSavingLl]; ring

/-- The height's logarithm squared is four times the saving squared. -/
theorem sq_log_chebHeightLl (c x : ℝ) :
    Real.log (chebHeightLl c x) ^ (2 : ℕ) = 4 * chebSavingLl c x ^ (2 : ℕ) := by
  rw [log_chebHeightLl]; ring

/-- The saving, squared. -/
theorem sq_chebSavingLl {c x : ℝ} (hQ : 0 ≤ chebQuadLl c x) :
    chebSavingLl c x ^ (2 : ℕ) = chebQuadLl c x / 4 := by
  rw [chebSavingLl, div_pow, Real.sq_sqrt hQ]
  norm_num

/-- Eight is cleared by the height's logarithm once the balanced quantity is at least `256`. -/
theorem sixteen_le_log_chebHeightLl {c x : ℝ} (hQ : 256 ≤ chebQuadLl c x) :
    16 ≤ Real.log (chebHeightLl c x) := by
  rw [chebHeightLl, Real.log_exp]
  have h : Real.sqrt 256 ≤ Real.sqrt (chebQuadLl c x) := Real.sqrt_le_sqrt hQ
  have h256 : Real.sqrt 256 = 16 := by
    rw [show (256 : ℝ) = 16 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]
  linarith [h, h256]

theorem eight_le_chebSavingLl {c x : ℝ} (hQ : 256 ≤ chebQuadLl c x) :
    8 ≤ chebSavingLl c x := by
  have h := sixteen_le_log_chebHeightLl hQ
  rw [log_chebHeightLl] at h
  linarith

/-- **The height's own `log log` is at least half the cutoff's.**  This is the fixed-point step:
`log log T = ½log(c·log x·log log x) ≥ ½log log x` as soon as `c·log log x ≥ 1`. -/
theorem half_logLog_le_logLog_chebHeightLl {c x : ℝ} (hlogx : 0 < Real.log x)
    (hc : Real.log x ≤ chebQuadLl c x) :
    Real.log (Real.log x) / 2 ≤ Real.log (Real.log (chebHeightLl c x)) := by
  have hQ0 : (0 : ℝ) < chebQuadLl c x := by linarith
  rw [chebHeightLl, Real.log_exp, Real.log_sqrt hQ0.le]
  have h := Real.log_le_log hlogx hc
  linarith

/-- **The left edge's saving at the balanced height.**  The depth `c·log log T/log T` applied over
`log x` saves at least `chebSavingLl c x`. -/
theorem chebSavingLl_le_left_saving {c x : ℝ} (hc0 : 0 < c) (hlogx : 0 < Real.log x)
    (hQ : 256 ≤ chebQuadLl c x) (hcx : Real.log x ≤ chebQuadLl c x) :
    chebSavingLl c x
      ≤ c * Real.log (Real.log (chebHeightLl c x)) / Real.log (chebHeightLl c x)
          * Real.log x := by
  have hQ0 : (0 : ℝ) < chebQuadLl c x := by linarith
  have hs8 : (8 : ℝ) ≤ chebSavingLl c x := eight_le_chebSavingLl hQ
  have hLg : Real.log (chebHeightLl c x) = 2 * chebSavingLl c x := log_chebHeightLl c x
  have hLg0 : (0 : ℝ) < Real.log (chebHeightLl c x) := by rw [hLg]; linarith
  have hhalf := half_logLog_le_logLog_chebHeightLl hlogx hcx
  -- `c·log x·log log x = 4·saving²`
  have hsq : chebSavingLl c x ^ (2 : ℕ) = chebQuadLl c x / 4 := sq_chebSavingLl hQ0.le
  have hQeq : chebQuadLl c x = c * (Real.log x * Real.log (Real.log x)) := rfl
  rw [div_mul_eq_mul_div, le_div_iff₀ hLg0]
  have hstep : c * (Real.log (Real.log x) / 2) * Real.log x
      ≤ c * Real.log (Real.log (chebHeightLl c x)) * Real.log x := by
    have h1 : c * (Real.log (Real.log x) / 2) ≤ c * Real.log (Real.log (chebHeightLl c x)) :=
      mul_le_mul_of_nonneg_left hhalf hc0.le
    exact mul_le_mul_of_nonneg_right h1 hlogx.le
  have hval : c * (Real.log (Real.log x) / 2) * Real.log x = 2 * chebSavingLl c x ^ (2 : ℕ) := by
    rw [hsq, hQeq]; ring
  have hgoal : chebSavingLl c x * Real.log (chebHeightLl c x) = 2 * chebSavingLl c x ^ (2 : ℕ) := by
    rw [hLg]; ring
  linarith [hstep, hval, hgoal]

/-- **The right line's cost at the balanced height** is under the saving. -/
theorem right_cost_le_chebSavingLl {c x : ℝ}
    (hQ : 256 ≤ chebQuadLl c x) (h2 : 2 * Real.log x ≤ chebQuadLl c x) :
    1 / Real.log (chebHeightLl c x) * Real.log x ≤ chebSavingLl c x := by
  have hs8 : (8 : ℝ) ≤ chebSavingLl c x := eight_le_chebSavingLl hQ
  have hLg : Real.log (chebHeightLl c x) = 2 * chebSavingLl c x := log_chebHeightLl c x
  have hLg0 : (0 : ℝ) < Real.log (chebHeightLl c x) := by rw [hLg]; linarith
  have hsq : chebSavingLl c x ^ (2 : ℕ) = chebQuadLl c x / 4 := sq_chebSavingLl (by linarith)
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hLg0, hLg]
  nlinarith [hsq, h2, hs8]

/-! ### The effective depth

The rectangle at height `T = chebHeightLl c x` has left abscissa `1 - A/log T` with
`A = c·log log T`.  The coefficient step needs `1 ≤ A` and `8A ≤ log T`. -/

/-- The effective depth of the rectangle at the balanced height. -/
noncomputable def chebDepthLl (c x : ℝ) : ℝ := c * Real.log (Real.log (chebHeightLl c x))

/-- The rectangle at the balanced height has depth at least one. -/
theorem one_le_chebDepthLl {c x : ℝ} (hc0 : 0 < c) (hlogx : 0 < Real.log x)
    (hcx : Real.log x ≤ chebQuadLl c x) (hdepth : 2 ≤ c * Real.log (Real.log x)) :
    1 ≤ chebDepthLl c x := by
  have hhalf := half_logLog_le_logLog_chebHeightLl hlogx hcx
  have hstep : c * (Real.log (Real.log x) / 2) ≤ c * Real.log (Real.log (chebHeightLl c x)) :=
    mul_le_mul_of_nonneg_left hhalf hc0.le
  rw [chebDepthLl]
  nlinarith [hstep, hdepth]

/-- `log u ≤ u/8 + 11/10` for positive `u`. -/
theorem log_le_eighth_add {u : ℝ} (hu : 0 < u) : Real.log u ≤ u / 8 + 11 / 10 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < u / 8 by positivity)
  rw [Real.log_div (ne_of_gt hu) (by norm_num)] at h
  have h8 : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [h8] at h
  linarith

/-- The rectangle at the balanced height clears the coefficient step's depth condition. -/
theorem eight_mul_chebDepthLl_le {c x : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 2)
    (hQ : 256 ≤ chebQuadLl c x) :
    8 * chebDepthLl c x ≤ Real.log (chebHeightLl c x) := by
  have hs8 : (8 : ℝ) ≤ chebSavingLl c x := eight_le_chebSavingLl hQ
  have hLg : Real.log (chebHeightLl c x) = 2 * chebSavingLl c x := log_chebHeightLl c x
  have hD : Real.log (Real.log (chebHeightLl c x)) = Real.log (2 * chebSavingLl c x) := by
    rw [hLg]
  have hbound := log_le_eighth_add (show (0 : ℝ) < 2 * chebSavingLl c x by linarith)
  have hlogpos : (0 : ℝ) ≤ Real.log (2 * chebSavingLl c x) :=
    Real.log_nonneg (by linarith)
  have hshrink : 8 * (c * Real.log (2 * chebSavingLl c x))
      ≤ 4 * Real.log (2 * chebSavingLl c x) := by nlinarith [hc, hlogpos]
  rw [chebDepthLl, hD, hLg]
  linarith [hshrink, hbound, hs8]

end RHTower.Sieve
