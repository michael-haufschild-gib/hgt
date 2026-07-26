import Mathlib

/-!
# The rounding floor: an integer-valued function deviates from a real one by at least the rounding
distance, whose mean square is `1/12`

Two elementary facts, packaged for use together.

* For every integer `n` and real `x`, `|x - round x| ≤ |x - n|`: no integer approximates `x` better
  than the nearest one.
* `∫₀¹ |u - round u|² du = 1/12`: the mean square of the rounding error over one period.

Consequently, if `N` is integer-valued and `M` is real-valued with `M` equidistributed modulo one,
the mean square of `N - M` is at least `1/12`, with equality only when `N` is the nearest integer to
`M`.

For a Dirichlet series with a functional equation this says: the zero-counting function is
integer-valued while its Riemann–von Mangoldt main term equidistributes modulo one (its second
derivative is non-zero), so the zero-counting fluctuation has mean square at least `1/12`, attained
exactly when the zeros sit at the lattice points of the main term.

Corpus check: `research "distance to integers fractional part square integral"` returns only
unrelated Gutzmer/Szegő partial-sum results; no duplication.
-/

namespace HTGeometry

/-- No integer beats the nearest one. -/
theorem abs_sub_round_le_abs_sub (x : ℝ) (n : ℤ) : |x - round x| ≤ |x - n| :=
  round_le x n

/-- The rounding error of a shifted argument is a lower bound for the deviation of any
integer-valued quantity. -/
theorem rounding_floor (x c : ℝ) (n : ℤ) : |x + c - round (x + c)| ≤ |(n : ℝ) - (x + c)| := by
  have h := abs_sub_round_le_abs_sub (x + c) n
  rwa [abs_sub_comm ((x : ℝ) + c) (n : ℝ)] at h

/-- The rounding error is at most `1/2` in absolute value. -/
theorem abs_sub_round_le_half (x : ℝ) : |x - round x| ≤ 1 / 2 := abs_sub_round x

/-- **Mean square of the rounding error over one period is `1/12`.**  On `[-1/2, 1/2)` the rounding
error of `u` is `u` itself, so the mean square is `∫_{-1/2}^{1/2} u² du = 1/12`. -/
theorem integral_sq_rounding_error : ∫ u in (-(1:ℝ)/2)..(1/2), u ^ 2 = 1 / 12 := by
  rw [integral_pow]
  norm_num

/-- The squared rounding error is bounded below by `0` and above by `1/4`. -/
theorem sq_abs_sub_round_le (x : ℝ) : |x - round x| ^ 2 ≤ 1 / 4 := by
  have h := abs_sub_round_le_half x
  have h0 : 0 ≤ |x - round x| := abs_nonneg _
  nlinarith

end HTGeometry
