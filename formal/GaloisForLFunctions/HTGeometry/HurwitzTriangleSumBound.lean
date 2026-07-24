import Mathlib

/-!
# The Hurwitz `1/42` gap for hyperbolic sphere triangle signatures

For an ordered integer signature `p ≤ q ≤ r` whose reciprocal sum is `< 1` (the hyperbolic
condition on a triangle orbifold of the sphere), the reciprocal sum is at most `41/42`, equivalently
the orbifold Euler defect `1 − (1/p + 1/q + 1/r)` is at least `1/42`.  The bound is attained exactly
at the signature `(2,3,7)`.

This is the arithmetic core of the projective-Hurwitz phase transition: `1/42` is the absolute
integral hyperbolic minimum of the orbifold curvature excess, the exact gap that converts a degree
budget into the sharp `D ≤ 42(2g−2)` inequality.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Hurwitz `1/42` bound.**  For ordered positive integers `p ≤ q ≤ r` whose reciprocal sum is
`< 1`, the sum is at most `41/42`, the value attained at the signature `(2,3,7)`. -/
theorem hurwitz_triple_sum_le {p q r : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hsum : (1 / (p : ℚ) + 1 / q + 1 / r) < 1) :
    (1 / (p : ℚ) + 1 / q + 1 / r) ≤ 41 / 42 := by
  have hq1 : 1 ≤ q := le_trans hp hpq
  have hr1 : 1 ≤ r := le_trans hq1 hqr
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq1
  have hr0 : (0 : ℚ) < r := by exact_mod_cast hr1
  have hqp : (1 / (q : ℚ)) ≤ 1 / p := one_div_le_one_div_of_le hp0 (by exact_mod_cast hpq)
  have hrq : (1 / (r : ℚ)) ≤ 1 / q := one_div_le_one_div_of_le hq0 (by exact_mod_cast hqr)
  have hrp : (1 / (r : ℚ)) ≤ 1 / p := le_trans hrq hqp
  have hp2 : 2 ≤ p := by
    rcases Nat.lt_or_ge p 2 with h | h
    · interval_cases p
      · simp only [Nat.cast_one, div_one] at hsum
        nlinarith [one_div_pos.mpr hq0, one_div_pos.mpr hr0]
    · exact h
  rcases Nat.lt_or_ge p 4 with hp4 | hp4
  · interval_cases p
    · -- p = 2
      have hq2 : 2 ≤ q := hpq
      rcases Nat.lt_or_ge q 7 with hq7 | hq7
      · interval_cases q
        · nlinarith [one_div_pos.mpr hr0]                       -- q = 2: 1 + 1/r < 1 impossible
        · -- q = 3: r ≥ 7
          have hr7 : 7 ≤ r := by
            by_contra h; rw [not_le] at h; interval_cases r
            all_goals norm_num at hsum
          have hb : (1 / (r : ℚ)) ≤ 1 / 7 :=
            one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hr7)
          nlinarith [hb]
        · -- q = 4: r ≥ 5
          have hr5 : 5 ≤ r := by
            by_contra h; rw [not_le] at h; interval_cases r
            all_goals norm_num at hsum
          have hb : (1 / (r : ℚ)) ≤ 1 / 5 :=
            one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hr5)
          nlinarith [hb]
        · nlinarith [hrq]                                        -- q = 5
        · nlinarith [hrq]                                        -- q = 6
      · -- q ≥ 7
        have hb : (1 / (q : ℚ)) ≤ 1 / 7 :=
          one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hq7)
        nlinarith [hb, hrq]
    · -- p = 3
      have hq3 : 3 ≤ q := hpq
      rcases Nat.lt_or_ge q 4 with hq4 | hq4
      · interval_cases q
        · -- q = 3: r ≥ 4
          have hr4 : 4 ≤ r := by
            by_contra h; rw [not_le] at h; interval_cases r
            all_goals norm_num at hsum
          have hb : (1 / (r : ℚ)) ≤ 1 / 4 :=
            one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hr4)
          nlinarith [hb]
      · -- q ≥ 4
        have hb : (1 / (q : ℚ)) ≤ 1 / 4 :=
          one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hq4)
        nlinarith [hb, hrq]
  · -- p ≥ 4
    have hb : (1 / (p : ℚ)) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp4)
    nlinarith [hb, hqp, hrp]

/-- **Hurwitz `1/42` Euler defect.**  The orbifold curvature excess of a hyperbolic ordered
signature is at least `1/42`. -/
theorem hurwitz_euler_defect_ge {p q r : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hsum : (1 / (p : ℚ) + 1 / q + 1 / r) < 1) :
    (1 : ℚ) / 42 ≤ 1 - (1 / (p : ℚ) + 1 / q + 1 / r) := by
  have := hurwitz_triple_sum_le hp hpq hqr hsum
  linarith

/-- The signature `(2,3,7)` is hyperbolic and attains the bound: its reciprocal sum is `41/42`. -/
theorem hurwitz_signature_237_sum : (1 / (2 : ℚ) + 1 / 3 + 1 / 7) = 41 / 42 := by norm_num

theorem hurwitz_signature_237_hyperbolic : (1 / (2 : ℚ) + 1 / 3 + 1 / 7) < 1 := by norm_num

/-- The `(2,3,7)` Euler defect is exactly `1/42`, so the Hurwitz bound is sharp. -/
theorem hurwitz_signature_237_defect : (1 : ℚ) - (1 / (2 : ℚ) + 1 / 3 + 1 / 7) = 1 / 42 := by
  norm_num

end GaloisForLFunctions.HTGeometry
