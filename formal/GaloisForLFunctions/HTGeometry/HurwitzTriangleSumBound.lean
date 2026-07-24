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

/-- **Symmetric Hurwitz `1/42` bound.**  For *any* positive integers `p, q, r` (no ordering
assumed) whose reciprocal sum is `< 1`, the sum is at most `41/42`.  Reduces to the ordered bound by
sorting the triple; the reciprocal sum is permutation invariant. -/
theorem hurwitz_triple_sum_le_symm {p q r : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hsum : (1 / (p : ℚ) + 1 / q + 1 / r) < 1) :
    (1 / (p : ℚ) + 1 / q + 1 / r) ≤ 41 / 42 := by
  rcases le_total p q with hpq | hpq
  · rcases le_total q r with hqr | hqr
    · exact hurwitz_triple_sum_le hp hpq hqr hsum
    · rcases le_total p r with hpr | hpr
      · have e : (1 / (p : ℚ) + 1 / q + 1 / r) = 1 / (p : ℚ) + 1 / r + 1 / q := by ring
        rw [e]; exact hurwitz_triple_sum_le hp hpr hqr (by rw [← e]; exact hsum)
      · have e : (1 / (p : ℚ) + 1 / q + 1 / r) = 1 / (r : ℚ) + 1 / p + 1 / q := by ring
        rw [e]; exact hurwitz_triple_sum_le hr hpr hpq (by rw [← e]; exact hsum)
  · rcases le_total p r with hpr | hpr
    · have e : (1 / (p : ℚ) + 1 / q + 1 / r) = 1 / (q : ℚ) + 1 / p + 1 / r := by ring
      rw [e]; exact hurwitz_triple_sum_le hq hpq hpr (by rw [← e]; exact hsum)
    · rcases le_total q r with hqr | hqr
      · have e : (1 / (p : ℚ) + 1 / q + 1 / r) = 1 / (q : ℚ) + 1 / r + 1 / p := by ring
        rw [e]; exact hurwitz_triple_sum_le hq hqr hpr (by rw [← e]; exact hsum)
      · have e : (1 / (p : ℚ) + 1 / q + 1 / r) = 1 / (r : ℚ) + 1 / q + 1 / p := by ring
        rw [e]; exact hurwitz_triple_sum_le hr hqr hpq (by rw [← e]; exact hsum)

/-- **Uniqueness of the Hurwitz minimizer.**  For an ordered hyperbolic signature `p ≤ q ≤ r`,
equality `1/p+1/q+1/r = 41/42` holds only at `(2,3,7)`. -/
theorem hurwitz_ordered_eq_237 {p q r : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hsum : (1 / (p : ℚ) + 1 / q + 1 / r) < 1)
    (heq : (1 / (p : ℚ) + 1 / q + 1 / r) = 41 / 42) : p = 2 ∧ q = 3 ∧ r = 7 := by
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
  have hp3 : p ≤ 3 := by
    by_contra h; rw [not_le] at h
    have hb : (1 / (p : ℚ)) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h)
    nlinarith [hb, hqp, hrp, heq]
  interval_cases p
  · -- p = 2
    have hq2 : 2 ≤ q := hpq
    have hq6 : q ≤ 6 := by
      by_contra h; rw [not_le] at h
      have hb : (1 / (q : ℚ)) ≤ 1 / 7 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h)
      nlinarith [hb, hrq, heq]
    interval_cases q
    · exfalso; nlinarith [one_div_pos.mpr hr0]                     -- q = 2
    · -- q = 3: force r = 7
      have hr7 : 7 ≤ r := by
        by_contra h; rw [not_le] at h; interval_cases r
        all_goals norm_num at hsum
      have hr8 : r < 8 := by
        by_contra h; rw [not_lt] at h
        have hb : (1 / (r : ℚ)) ≤ 1 / 8 :=
          one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h)
        nlinarith [hb, heq]
      exact ⟨rfl, rfl, by omega⟩
    · -- q = 4
      exfalso
      have hr5 : 5 ≤ r := by
        by_contra h; rw [not_le] at h; interval_cases r
        all_goals norm_num at hsum
      have hb : (1 / (r : ℚ)) ≤ 1 / 5 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hr5)
      nlinarith [hb, heq]
    · exfalso; nlinarith [hrq, heq]                                 -- q = 5
    · exfalso; nlinarith [hrq, heq]                                 -- q = 6
  · -- p = 3
    have hq3 : 3 ≤ q := hpq
    have hq3' : q ≤ 3 := by
      by_contra h; rw [not_le] at h
      have hb : (1 / (q : ℚ)) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h)
      nlinarith [hb, hrq, heq]
    interval_cases q
    · -- q = 3
      exfalso
      have hr4 : 4 ≤ r := by
        by_contra h; rw [not_le] at h; interval_cases r
        all_goals norm_num at hsum
      have hb : (1 / (r : ℚ)) ≤ 1 / 4 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hr4)
      nlinarith [hb, heq]

/-- Ordered characterization: on a hyperbolic ordered signature, the reciprocal sum equals `41/42`
iff the signature is `(2,3,7)`. -/
theorem hurwitz_ordered_sum_eq_iff {p q r : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hsum : (1 / (p : ℚ) + 1 / q + 1 / r) < 1) :
    (1 / (p : ℚ) + 1 / q + 1 / r) = 41 / 42 ↔ (p = 2 ∧ q = 3 ∧ r = 7) := by
  constructor
  · exact hurwitz_ordered_eq_237 hp hpq hqr hsum
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

end GaloisForLFunctions.HTGeometry
