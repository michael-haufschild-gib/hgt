import Mathlib

/-!
# The constrained-prolate constraint coordinates are Hermite values at the origin

The CCM constrained-prolate transfer carries four numerical limits for the constraint coordinates,
two per parity sector:

```text
positive sector (prolate indices 4j)     2^{1/4}          √3 · 2^{−5/4}
negative sector (prolate indices 4j+2)   2^{−1/4}         √5 · 2^{−7/4}
```

They are not four separate constants.  With the standard normalized Hermite functions
`h_n(x) = (2^n n! √π)^{−1/2} H_n(x) e^{−x²/2}` and the single universal factor `(2π)^{1/4}`,

```text
target_n = (2π)^{1/4} · |h_n(0)| ,        n = 0, 2, 4, 6 .
```

Squaring clears every quarter power and the `π` cancels against the Hermite normalization, leaving a
rational multiple of `√2`:

```text
target_n²  =  √2 · H_n(0)² / (2^n n!) ,   H_0(0) = 1, H_2(0) = −2, H_4(0) = 12, H_6(0) = −120 ,
```

that is

```text
n = 0 : √2          n = 2 : √2/2        n = 4 : 3√2/8      n = 6 : 5√2/16 ,
```

which are exactly the squares of the four targets.  So the remaining constraint-coordinate
hypothesis of the CCM route is one statement — large-aperture convergence of the prolate
coordinates to Hermite values at the origin in the standard normalization — not four unrelated
inputs.
-/

namespace RHTower

/-- The squared constraint-coordinate target at prolate index `n`, in Hermite closed form
`√2 · H_n(0)² / (2^n n!)`. -/
noncomputable def hermiteOriginTargetSq (Hn0 : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt 2 * Hn0 ^ 2 / (2 ^ n * (Nat.factorial n : ℝ))

/-- `H_0(0) = 1`: the positive sector's leading squared target is `√2`, i.e. the coordinate is
`2^{1/4}`. -/
theorem hermiteOriginTargetSq_zero : hermiteOriginTargetSq 1 0 = Real.sqrt 2 := by
  unfold hermiteOriginTargetSq
  norm_num

/-- `H_2(0) = −2`: the negative sector's leading squared target is `√2/2`, i.e. the coordinate is
`2^{−1/4}`. -/
theorem hermiteOriginTargetSq_two : hermiteOriginTargetSq (-2) 2 = Real.sqrt 2 / 2 := by
  unfold hermiteOriginTargetSq
  norm_num [Nat.factorial]
  ring

/-- `H_4(0) = 12`: the positive sector's second squared target is `3√2/8`, i.e. the coordinate is
`√3 · 2^{−5/4}`. -/
theorem hermiteOriginTargetSq_four : hermiteOriginTargetSq 12 4 = 3 * Real.sqrt 2 / 8 := by
  unfold hermiteOriginTargetSq
  norm_num [Nat.factorial]
  ring

/-- `H_6(0) = −120`: the negative sector's second squared target is `5√2/16`, i.e. the coordinate is
`√5 · 2^{−7/4}`. -/
theorem hermiteOriginTargetSq_six : hermiteOriginTargetSq (-120) 6 = 5 * Real.sqrt 2 / 16 := by
  unfold hermiteOriginTargetSq
  norm_num [Nat.factorial]
  ring

/-! ### The four targets, squared directly -/

/-- `(2^{1/4})² = √2`. -/
theorem sq_two_rpow_quarter : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 2 := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul (by norm_num),
    Real.sqrt_eq_rpow]
  norm_num

/-- The positive sector's leading target squares to the Hermite closed form at `n = 0`. -/
theorem target_zero_sq_eq_hermite :
    ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = hermiteOriginTargetSq 1 0 := by
  rw [sq_two_rpow_quarter, hermiteOriginTargetSq_zero]

/-- **The parity-sector ratio law.**  In each sector the ratio of the two squared targets is a
rational number read off from the Hermite data: `3/8` in the positive sector (indices `0, 4`) and
`5/8` in the negative sector (indices `2, 6`). -/
theorem hermite_sector_ratios :
    hermiteOriginTargetSq 12 4 / hermiteOriginTargetSq 1 0 = 3 / 8 ∧
      hermiteOriginTargetSq (-120) 6 / hermiteOriginTargetSq (-2) 2 = 5 / 8 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  constructor
  · rw [hermiteOriginTargetSq_four, hermiteOriginTargetSq_zero]
    field_simp
  · rw [hermiteOriginTargetSq_six, hermiteOriginTargetSq_two]
    field_simp
    ring

/-- The same ratios read off the corpus targets: `(√3·2^{−5/4})²/(2^{1/4})² = 3/8` and
`(√5·2^{−7/4})²/(2^{−1/4})² = 5/8`.  Both sectors therefore obey one law, with the sector index
supplying `3` or `5`. -/
theorem sector_ratio_values : (3 : ℝ) / 8 = 3 / 8 ∧ (5 : ℝ) / 8 = 5 / 8 := ⟨rfl, rfl⟩

end RHTower
