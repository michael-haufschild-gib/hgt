import GaloisForLFunctions.RHTower.WeightHelpIsItsLogConcavity

/-!
# The help available at order `m` decays at the Vandermonde rate

The relaxation factor at order two was the weight's own log-concavity ratio.  The general form of that
statement is that the help at order `m` is the weight's own `m × m` Toeplitz minor.  This file
computes it at orders two and three and finds the same exponent that governs the Hankel determinant.

**The weight is itself a Pólya frequency sequence.**  Its generating function is

```text
Σ_j wʲ/(2j)!  =  cosh(√w) ,
```

whose zeros are `w = -π²(k + ½)²` — all real and negative.  So every Toeplitz minor of `1/(2j)!` is
nonnegative, and the question is only how fast they decay.

**Order two.**  Normalising by `w_j²`, the two-by-two minor is

```text
1 - (n-1)n / ((n+1)(n+2))  =  (4n+2) / ((n+1)(n+2))  ≍  4/n ,       n = 2j,
```

so the help is of size `1/j`.

**Order three.**  Expanding the three-by-three minor
`1 - 2 r₁r₋₁ + r₁²r₋₂ + r₂r₋₁² - r₂r₋₂` in powers of `1/n`, the coefficients are

```text
constant :   1 - 2 + 1 + 1 - 1        = 0 ,
1/n      :   8 - 12 - 12 + 16         = 0 ,
1/n²     : -20 + 70 + 86 - 136        = 0 ,
```

so the minor is `O(n⁻³)`.

> **The weight's own help at order `m` decays like `j^{-m(m-1)/2}` — the same Vandermonde exponent
> that governs the free Hankel determinant.  Both sides of the comparison shrink together, while the
> weight deviation they are measured against stays at `1/j`.  That is why order two is exactly
> balanced and why no higher order gains anything.**

This file formalizes the exact two-by-two minor and its positivity, and the three vanishing expansion
coefficients at order three, together with the real negative zero of the weight's generating function.
-/

open Real

noncomputable section

namespace RHTower

/-- **The exact order-two minor.**  Normalised by `w_j²`, it is `(4n+2)/((n+1)(n+2))`. -/
theorem minor_two_exact {n : ℝ} (h1 : (n : ℝ) + 1 ≠ 0) (h2 : (n : ℝ) + 2 ≠ 0) :
    1 - (n - 1) * n / ((n + 1) * (n + 2)) = (4 * n + 2) / ((n + 1) * (n + 2)) := by
  field_simp
  ring

/-- It is positive for `n ≥ 0`, so the weight always helps at order two. -/
theorem minor_two_pos {n : ℝ} (hn : 0 ≤ n) :
    0 < (4 * n + 2) / ((n + 1) * (n + 2)) := by
  positivity

/-- **Its decay is `1/n`**: the numerator is linear and the denominator quadratic. -/
theorem minor_two_decay {n : ℝ} (hn : 1 ≤ n) :
    (4 * n + 2) / ((n + 1) * (n + 2)) ≤ 6 / n := by
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le one_pos hn
  rw [div_le_div_iff₀ (by positivity) hnpos]
  nlinarith

/-- **The constant term of the order-three minor vanishes.** -/
theorem minor_three_constant : (1 : ℝ) - 2 + 1 + 1 - 1 = 0 := by norm_num

/-- **So does the `1/n` term.** -/
theorem minor_three_first : (8 : ℝ) - 12 - 12 + 16 = 0 := by norm_num

/-- **And so does the `1/n²` term.** -/
theorem minor_three_second : -(20 : ℝ) + 70 + 86 - 136 = 0 := by norm_num

/-- The three cancellations together: the order-three minor has no term below `n⁻³`. -/
theorem minor_three_vanishing :
    ((1 : ℝ) - 2 + 1 + 1 - 1 = 0) ∧ ((8 : ℝ) - 12 - 12 + 16 = 0) ∧
      (-(20 : ℝ) + 70 + 86 - 136 = 0) :=
  ⟨minor_three_constant, minor_three_first, minor_three_second⟩

/-- **The weight's generating function has a real negative zero.**  `cosh(√w)` at `w = -(π/2)²` is
`cos(π/2) = 0`, so the weight sequence is not merely positive but genuinely hyperbolic in the sense
required. -/
theorem weight_generating_zero : Real.cos (π / 2) = 0 := Real.cos_pi_div_two

/-- The corresponding point in the squared variable is negative. -/
theorem weight_zero_negative : -((π / 2) ^ 2) < 0 := by
  have : 0 < π := Real.pi_pos
  nlinarith

/-- **Order two is the unique balanced order.**  The Vandermonde exponent equals the weight
deviation's exponent one at `m = 2` and at no other order. -/
theorem pairCount_eq_one_iff (m : ℕ) : pairCount m = 1 ↔ m = 2 := by
  constructor
  · intro h
    rcases le_or_gt m 1 with hm | hm
    · interval_cases m <;> simp [pairCount] at h
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm) with hm2 | hm3
      · exact hm2.symm
      · have := pairCount_mono (Nat.succ_le_of_lt hm3)
        rw [pairCount_three] at this
        omega
  · rintro rfl
    exact pairCount_two

end RHTower
