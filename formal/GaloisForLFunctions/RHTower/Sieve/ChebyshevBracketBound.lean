import GaloisForLFunctions.RHTower.Sieve.ChebyshevWidthOne

/-!
# The main term's bracket, quantitatively

The contour's main term is `mellin w 1` times

```text
2 arctan(T/(d-1)) - 2 arctan(T/(c-1)),
```

which tends to `2π` as the rectangle is truncated ever higher.  The corpus proves that
qualitatively (`tendsto_bracket_at_choice`); an error term needs a rate.

Since `π/2 - arctan u = arctan(1/u) ≤ 1/u`, each half is within `(d-1)/T` resp. `(1-c)/T` of `π/2`,
so the bracket is within `2(d-c)/T` of `2π` — the width of the rectangle divided by its height.  No
mean value theorem is needed: `arctan z ≤ tan (arctan z) = z` does it.
-/

namespace RHTower.Sieve

/-- **The arctangent is below the diagonal.**  From `x < tan x` on `(0, π/2)`. -/
theorem arctan_le_self {z : ℝ} (hz : 0 ≤ z) : Real.arctan z ≤ z := by
  rcases eq_or_lt_of_le hz with rfl | hpos
  · simp
  · have h1 : 0 < Real.arctan z := Real.arctan_pos.mpr hpos
    have h2 : Real.arctan z < Real.pi / 2 := Real.arctan_lt_pi_div_two z
    have h3 := Real.lt_tan h1 h2
    rw [Real.tan_arctan] at h3
    linarith

/-- **The arctangent's approach to `π/2`.** -/
theorem pi_div_two_sub_arctan_le {u : ℝ} (hu : 0 < u) :
    Real.pi / 2 - Real.arctan u ≤ 1 / u := by
  rw [← Real.arctan_inv_of_pos hu, inv_eq_one_div]
  exact arctan_le_self (z := 1 / u) (by positivity)

/-- **The bracket is within the rectangle's aspect ratio of `2π`.** -/
theorem abs_bracket_sub_two_pi_le {c d T : ℝ} (hc : c < 1) (hd : 1 < d) (hT : 0 < T) :
    |2 * Real.arctan (T / (d - 1)) - 2 * Real.arctan (T / (c - 1)) - 2 * Real.pi|
      ≤ 2 * ((d - c) / T) := by
  have hd1 : (0 : ℝ) < d - 1 := by linarith
  have hc1 : (0 : ℝ) < 1 - c := by linarith
  have hu1 : (0 : ℝ) < T / (d - 1) := div_pos hT hd1
  have hu2 : (0 : ℝ) < T / (1 - c) := div_pos hT hc1
  have harc : Real.arctan (T / (c - 1)) = -Real.arctan (T / (1 - c)) := by
    rw [show T / (c - 1) = -(T / (1 - c)) by
      rw [show c - 1 = -(1 - c) by ring, div_neg], Real.arctan_neg]
  have hb1 := pi_div_two_sub_arctan_le hu1
  have hb2 := pi_div_two_sub_arctan_le hu2
  rw [one_div_div] at hb1 hb2
  have hTne : T ≠ 0 := ne_of_gt hT
  have hsum : (d - 1) / T + (1 - c) / T = (d - c) / T := by
    field_simp
    ring
  have hlt1 := Real.arctan_lt_pi_div_two (T / (d - 1))
  have hlt2 := Real.arctan_lt_pi_div_two (T / (1 - c))
  have hpos : (0 : ℝ) ≤ (d - c) / T := div_nonneg (by linarith) hT.le
  rw [harc, abs_le]
  constructor
  · linarith [hb1, hb2, hsum]
  · linarith [hlt1, hlt2, hpos]

/-- **The bracket at the width-`1/log` rectangle.** -/
theorem abs_bracket_kappa_one_le {T : ℝ} (hT : 8 ≤ Real.log T) (hT0 : 0 < T) :
    |2 * Real.arctan (T / (chebRightTwo T - 1))
        - 2 * Real.arctan (T / (chebLeftTwo T - 1)) - 2 * Real.pi|
      ≤ 2 * ((chebRightTwo T - chebLeftTwo T) / T) :=
  abs_bracket_sub_two_pi_le (chebLeftTwo_lt_one hT) (one_lt_chebRightTwo hT) hT0

/-- The width of the rectangle. -/
theorem chebRightTwo_sub_chebLeftTwo (T : ℝ) :
    chebRightTwo T - chebLeftTwo T = (1 + 1 / 40000) / Real.log T := by
  rw [chebRightTwo, chebLeftTwo]
  ring

end RHTower.Sieve
