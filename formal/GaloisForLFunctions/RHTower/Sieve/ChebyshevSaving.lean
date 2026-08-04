import GaloisForLFunctions.RHTower.Sieve.ChebyshevHeight

/-!
# The saving and the growth at the balanced height

At the balanced height the strip half-width is `w = A/(log x)^{9/10}`, so the two abscissae move the
cutoff's size by

    Y^{1-w} ≤ Y·exp(-A(log x)^{1/10})      (left edge, a saving)
    Y^{1+w} ≤ Y·exp( A(log Y)/(log x)^{9/10})   (right edge, a growth).

Both exponents are governed by the same quantity `w·log Y`.  On the left it is bounded below by
`A(log x)^{1/10}` and on the right above by the same shape, so the saving is genuine and the growth
is subexponential in `(log x)^{1/10}` — which is what the truncation height `exp((log x)^{1/10})`
divides away, since `A ≤ 1/2 < 1`.
-/

namespace RHTower.Sieve

open RHTower

/-- The exponent arithmetic behind the balanced choice. -/
theorem div_rpow_nine_tenths {u : ℝ} (hu : 0 < u) :
    u / u ^ ((9 : ℝ) / 10) = u ^ ((1 : ℝ) / 10) := by
  rw [show ((1 : ℝ) / 10) = 1 - 9 / 10 by norm_num, Real.rpow_sub hu, Real.rpow_one]

/-- **The left abscissa saves an exponential.** -/
theorem rpow_left_le_saving {x Y : ℝ} (hx : 0 < Real.log x) (hx0 : 0 < x) (hxY : x ≤ Y) :
    Y ^ (1 - zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10))
      ≤ Y * Real.exp (-(zetaLowerA * (Real.log x) ^ ((1 : ℝ) / 10))) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le hx0 hxY
  have hlogY : Real.log x ≤ Real.log Y := Real.log_le_log hx0 hxY
  have hw0 : (0 : ℝ) < zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10) := by
    have : (0 : ℝ) < (Real.log x) ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos hx _
    positivity
  have hsplit : Y ^ (1 - zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10))
      = Y * Y ^ (-(zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10))) := by
    rw [show (1 : ℝ) - zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)
        = 1 + -(zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)) by ring,
      Real.rpow_add hY0, Real.rpow_one]
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ hY0.le
  rw [Real.rpow_def_of_pos hY0]
  refine Real.exp_le_exp.2 ?_
  have hkey : zetaLowerA * (Real.log x) ^ ((1 : ℝ) / 10)
      ≤ zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10) * Real.log Y := by
    have hxx : zetaLowerA * (Real.log x) ^ ((1 : ℝ) / 10)
        = zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10) * Real.log x := by
      rw [← div_rpow_nine_tenths hx]
      field_simp
    rw [hxx]
    exact mul_le_mul_of_nonneg_left hlogY hw0.le
  nlinarith [hkey]

/-- **The right abscissa grows by at most the same shape.** -/
theorem rpow_right_le_growth {x Y : ℝ} (hY0 : 0 < Y) :
    Y ^ (1 + zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10))
      ≤ Y * Real.exp (zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10) * Real.log Y) := by
  have hsplit : Y ^ (1 + zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10))
      = Y * Y ^ (zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)) := by
    rw [Real.rpow_add hY0, Real.rpow_one]
  rw [hsplit, Real.rpow_def_of_pos hY0, mul_comm (Real.log Y)]

end RHTower.Sieve
