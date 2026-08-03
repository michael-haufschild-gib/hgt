import GaloisForLFunctions.RHTower.Sieve.CircleSeparation

/-!
# Distance to the nearest integer

A large sieve hypothesis separates frequencies in `ℝ/ℤ`, so the quantity it controls is the distance
from a real number to the nearest integer,

`‖x‖ = |x - round x|`.

The four facts that a separation argument needs are proved here: the distance never exceeds `1/2`,
it is unchanged by an integer shift, it agrees with `|x|` whenever `|x| < 1/2`, and — the form used
in the counting — two reals whose reduced representatives are within `δ ≤ 1/2` of each other are
within `δ` on the circle.  The last is what converts "two points in a short arc" into "two points
that violate the separation hypothesis".

The chord bound of `CircleSeparation.lean` is restated in these terms: `4‖α‖ ≤ ‖e(α) - 1‖`.
-/

namespace RHTower.Sieve

open Real

/-- Distance from a real number to the nearest integer. -/
noncomputable def toIntDist (x : ℝ) : ℝ := |x - (round x : ℝ)|

theorem toIntDist_nonneg (x : ℝ) : 0 ≤ toIntDist x := abs_nonneg _

theorem toIntDist_le_half (x : ℝ) : toIntDist x ≤ 1 / 2 := abs_sub_round x

/-- A real number of absolute value less than a half rounds to zero. -/
theorem round_eq_zero_of_abs_lt_half {x : ℝ} (h : |x| < 1 / 2) : round x = 0 := by
  have hlt := abs_lt.mp h
  rw [round_eq, Int.floor_eq_zero_iff, Set.mem_Ico]
  constructor <;> linarith [hlt.1, hlt.2]

/-- On the short range the circle distance is the ordinary one. -/
theorem toIntDist_eq_abs_of_abs_lt_half {x : ℝ} (h : |x| < 1 / 2) : toIntDist x = |x| := by
  rw [toIntDist, round_eq_zero_of_abs_lt_half h]
  norm_num

/-- The circle distance is invariant under integer shifts. -/
theorem toIntDist_add_int (x : ℝ) (n : ℤ) : toIntDist (x + (n : ℝ)) = toIntDist x := by
  rw [toIntDist, toIntDist, round_add_intCast]
  congr 1
  push_cast
  ring

/-- **Reduced representatives control the circle distance.**  If the reduced representatives of `u`
and `v` are within `δ ≤ 1/2`, then `u` and `v` are within `δ` on the circle. -/
theorem toIntDist_sub_lt {u v δ : ℝ} (hδ : δ ≤ 1 / 2)
    (h : |(u - (round u : ℝ)) - (v - (round v : ℝ))| < δ) :
    toIntDist (u - v) < δ := by
  set a : ℝ := u - (round u : ℝ) with ha
  set b : ℝ := v - (round v : ℝ) with hb
  have hshift : u - v = (a - b) + ((round u - round v : ℤ) : ℝ) := by
    rw [ha, hb]
    push_cast
    ring
  rw [hshift, toIntDist_add_int, toIntDist_eq_abs_of_abs_lt_half (lt_of_lt_of_le h hδ)]
  exact h

/-- **Chord bound in circle-distance form.** -/
theorem four_mul_toIntDist_le (α : ℝ) :
    4 * toIntDist α ≤ ‖Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) - 1‖ :=
  four_mul_round_dist_le α

end RHTower.Sieve
