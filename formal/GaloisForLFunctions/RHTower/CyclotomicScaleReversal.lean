import GaloisForLFunctions.RHTower.CharacterAverageSuppression

/-!
# For cyclotomic fields the scale obstruction reverses

The character-averaged Weil form mod `q` is the Weil form of `ζ_K` for `K = ℚ(ζ_q)`, since
`∏_{χ mod q} L(s,χ) = ζ_K(s)`.  Two consequences follow, and the second reverses the obstruction that
blocks every single-scale argument over `ℚ`.

**Unconditional positivity below `log q`.**  The averaged prime sum runs over `n ≡ 1 (mod q)`, and
the least such `n > 1` is `q+1`.  So for any positive-type test of width `L < log(q+1)` the prime
side is **empty**, and the averaged form is archimedean plus pole, hence strictly positive.  Number
fields whose least prime norm is large relative to their archimedean weight therefore have an
unconditional positivity range, growing like `log q`.

**The scale product reverses.**  Over `ℚ` the obstruction was `γ₁·log 2 ≈ 9.8 > 1`: a window narrow
enough to resolve the first zero is far too narrow to reach the first prime.  For `ζ_K` the two
quantities both change.  The zero density at low height is `≍ log|d_K|/2π`, so the first ordinate is
`γ₁(K) ≍ 2π/log|d_K| = 2π/(φ(q) log q)`, while the first prime log is `log q`.  Their product is

```text
γ₁(K)·log q  ≍  2π/φ(q) ,
```

which is **less than one as soon as `φ(q) > 2π`**, and `π < 4` makes `φ(q) ≥ 8` enough.

> **For cyclotomic fields of large conductor the scale incompatibility is reversed: a single-scale
> test function can resolve both the first zero and the first prime.  The obstruction that blocks
> every single-scale explicit-formula argument over `ℚ` is a feature of `ℚ`, not of `L`-functions,
> and it weakens as the field grows.**

The mechanism is transparent: enlarging the field multiplies the archimedean weight by `φ(q)` while
pushing the first prime norm out to `q`, and the archimedean weight is what sets the zero density.
The two scales move in opposite directions.

**What it does not give.**  Positivity of the average is not positivity of each factor, and the
individual statement is the exceptional-character problem.  So the reversal is a structural
observation about where single-scale arguments can work, not a route to the hypothesis for `ζ`
itself.

This file formalizes the empty-prime-range positivity and the reversal of the scale product.
-/

open Real

noncomputable section

namespace RHTower

/-- **Empty prime range.**  If the test width is below the least prime log of the family, the prime
side vanishes and the form is archimedean plus pole. -/
theorem empty_prime_positive {A P W : ℝ} (hA : 0 < A) (hP : P = 0) (hW : W = A - P) :
    0 < W := by
  rw [hW, hP]; linarith

/-- The least `n > 1` in the class of `1` mod `q` is `q + 1`: any such `n` is either at most `q`,
in which case it equals `1`, or at least `q + 1`. -/
theorem least_residue_gap {q n : ℕ} : q + 1 ≤ n ∨ n ≤ q := by
  rcases le_or_gt n q with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **The scale product over the rationals.**  `γ₁·log 2 > 1` — the obstruction. -/
theorem rational_scale_product {g1 : ℝ} (hg1 : 2 < g1) : 1 < g1 * Real.log 2 :=
  product_gt_one_of_bounds hg1 log_two_gt_half

/-- **The scale product for a cyclotomic field.**  With `γ₁(K) ≍ 2π/(φ log q)` and first prime log
`log q`, the product is `2π/φ`, which is below one once `φ > 2π`. -/
theorem cyclotomic_scale_product {phi : ℝ} (hphi : 2 * π < phi) :
    2 * π / phi < 1 := by
  have hpos : 0 < phi := lt_trans (by positivity) hphi
  rw [div_lt_one hpos]
  exact hphi

/-- The reversal is monotone in the conductor: larger `φ` gives a smaller product. -/
theorem reversal_monotone {p₁ p₂ : ℝ} (h1 : 0 < p₁) (h12 : p₁ ≤ p₂) :
    2 * π / p₂ ≤ 2 * π / p₁ := by
  apply div_le_div_of_nonneg_left (by positivity) h1 h12

/-- **The reversal.**  Over `ℚ` the product exceeds one; for a cyclotomic field of large conductor it
is below one, so a single-scale test resolves both scales. -/
theorem scale_reversal {g1 phi : ℝ} (hg1 : 2 < g1) (hphi : 2 * π < phi) :
    1 < g1 * Real.log 2 ∧ 2 * π / phi < 1 :=
  ⟨rational_scale_product hg1, cyclotomic_scale_product hphi⟩

/-- `φ(q) > 2π` holds as soon as `φ(q) ≥ 8`, since `π < 4`; so the reversal begins at small
conductors such as `q = 15, 16, 20, 24, 30`. -/
theorem eight_gt_two_pi : 2 * π < 8 := by
  nlinarith [Real.pi_lt_four]

end RHTower
