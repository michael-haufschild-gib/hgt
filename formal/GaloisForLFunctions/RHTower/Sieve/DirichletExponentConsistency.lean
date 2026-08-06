import GaloisForLFunctions.RHTower.Sieve.DirichletExponentShape

/-!
# Consistency of the exponent sandwich

The two bounds on `t` in the exponent form are powers of two, so they are compatible exactly when

```text
2 + R/3  ≤  K + (S+1)(K-1) - (S+1)/3,
```

and then the lower bound itself is an admissible value of `t`.  A concrete choice of exponents
satisfies every hypothesis of the shape at once, so the estimate is not vacuous.
-/

namespace RHTower.Sieve

open Finset

/-- **Compatibility of the sandwich.**  The exponent inequality is exactly what makes the lower
bound on `t` no larger than the upper bound. -/
theorem exponent_sandwich_nonempty {S R K : ℕ}
    (hcompat : 2 + (R : ℝ) / 3
      ≤ (K : ℝ) + (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3)) :
    8 * Real.pi * (2 : ℝ) ^ ((R : ℝ) / 3)
      ≤ 2 * Real.pi * (2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3)
        * (2 : ℝ) ^ K := by
  have hπ := Real.pi_pos
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
  have hL : 8 * Real.pi * (2 : ℝ) ^ ((R : ℝ) / 3)
      = 2 * Real.pi * (2 : ℝ) ^ (2 + (R : ℝ) / 3) := by
    rw [Real.rpow_add h2pos, h4]
    ring
  have hR : 2 * Real.pi * (2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3)
        * (2 : ℝ) ^ K
      = 2 * Real.pi
        * (2 : ℝ) ^ ((((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3) + (K : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) K, mul_assoc (2 * Real.pi), ← Real.rpow_add h2pos]
  rw [hL, hR]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  linarith

/-- The lower endpoint is itself an admissible `t`. -/
theorem exists_t_in_exponent_sandwich {S R K : ℕ}
    (hcompat : 2 + (R : ℝ) / 3
      ≤ (K : ℝ) + (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3)) :
    ∃ t : ℝ, 0 < t ∧ 8 * Real.pi * (2 : ℝ) ^ ((R : ℝ) / 3) ≤ t ∧
      t ≤ 2 * Real.pi * (2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3)
        * (2 : ℝ) ^ K := by
  refine ⟨8 * Real.pi * (2 : ℝ) ^ ((R : ℝ) / 3), ?_, le_refl _, exponent_sandwich_nonempty hcompat⟩
  have hπ := Real.pi_pos
  positivity

/-- **Non-vacuity.**  The exponents `S = 1`, `R = 2`, `K = 3` with `ε = 2560` satisfy every
hypothesis of the exponent form, for an explicit `t`. -/
theorem exists_littlewood_exponent_instance :
    ∃ (S R K : ℕ) (ε t : ℝ), 0 < t ∧ 2 ≤ K ∧ S < R ∧ 0 < ε ∧ ε ≤ 2560 ∧
      Nat.factorial (K - 1) ≤ 2 ^ (S + 1) ∧
      8 * Real.pi * (2 : ℝ) ^ ((R : ℝ) / 3) ≤ t ∧
      t ≤ 2 * Real.pi * (2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3)
        * (2 : ℝ) ^ K ∧
      3 * (2 : ℝ) ^ K * Real.log (2560 / ε) ≤ ((S : ℝ) + 1) * Real.log 2 := by
  have hcompat : 2 + ((2 : ℕ) : ℝ) / 3
      ≤ ((3 : ℕ) : ℝ) + ((((1 : ℕ) : ℝ) + 1) * (((3 : ℕ) : ℝ) - 1) - (((1 : ℕ) : ℝ) + 1) / 3) := by
    norm_num
  obtain ⟨t, ht0, htlow, hthigh⟩ := exists_t_in_exponent_sandwich hcompat
  refine ⟨1, 2, 3, 2560, t, ht0, by norm_num, by norm_num, by norm_num, le_refl _, ?_, htlow,
    hthigh, ?_⟩
  · norm_num [Nat.factorial]
  · have hone : (2560 : ℝ) / 2560 = 1 := by norm_num
    rw [hone, Real.log_one, mul_zero]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    push_cast
    linarith

end RHTower.Sieve
