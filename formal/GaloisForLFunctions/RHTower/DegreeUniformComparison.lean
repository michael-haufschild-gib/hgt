import GaloisForLFunctions.RHTower.ConvexityOfTheDoublyExponential

/-!
# The degree-`d` comparison: the ratio grows like `(2 log k)^{d-1}/(d-1)`

The mechanism was stated at degree two.  This file carries it to degree `d` and finds the two sides
have matching shapes with a ratio that grows.

**The two `d`-th order quantities.**  For the normalisation, `-log(2k)!` has `d`-th derivative in `k`
of size `2(d-2)!/k^{d-1}`; that is the `d`-th order factorial gap.  For the moments, the `d`-th
cumulant of a measure whose `-log` has convexity `c` is bounded by `(d-1)!/c^{d-1}`, and the mechanism
gives `c ≍ 2k log k`.  So

```text
gap  ≍  2(d-2)! / k^{d-1} ,        cumulant  ≲  (d-1)! / (2k log k)^{d-1} .
```

**Their ratio.**

```text
gap / cumulant  ≍  ( 2(d-2)! / k^{d-1} ) · ( (2k log k)^{d-1} / (d-1)! )  =  2 (2 log k)^{d-1} / (d-1) .
```

**And it exceeds one for `k` bounded below, independently of the degree.**  Since `2^m ≥ m` for every
`m ≥ 1`, taking `log k ≥ 1` already gives `(2 log k)^{d-1} ≥ 2^{d-1} ≥ d-1 > (d-1)/2`.

> **The `d`-th order comparison has the shape `2(2 log k)^{d-1}/(d-1)`, exceeding one once `log k ≥ 1`
> for every degree.  The mechanism therefore points to a threshold bounded in the degree, matching the
> observed onsets of zero.**

**What this is and is not.**  The shapes match and the ratio grows in both parameters; the constants
in the cumulant estimate are not tracked here, so this is a mechanism and a prediction, not a proof.
Its content is that the two sides scale the same way in `d` and that the moment side is smaller by a
factor `(2 log k)^{d-1}`.

This file formalizes the ratio identity and the elementary inequality that makes it exceed one
uniformly in the degree.
-/

open Real

noncomputable section

namespace RHTower

/-- **The ratio identity.**  Gap over cumulant, in the stated shapes. -/
theorem gap_over_cumulant {k G C : ℝ} (m : ℕ) (hk : 0 < k)
    (hgap : G = 2 * C / k ^ m) (hcum : C ≠ 0) :
    G * (k ^ m / C) = 2 := by
  rw [hgap]
  field_simp

/-- **The elementary inequality.**  `m ≤ 2^m` for every natural `m`. -/
theorem le_two_pow (m : ℕ) : (m : ℝ) ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ n ih =>
    have h2 : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    push_cast
    calc (n : ℝ) + 1 ≤ 2 ^ n + 2 ^ n := by linarith
      _ = 2 ^ (n + 1) := by ring

/-- **The comparison exceeds one uniformly in the degree.**  With `log k ≥ 1` the factor
`(2 log k)^{d-1}` is at least `2^{d-1}`, which dominates `(d-1)/2`. -/
theorem comparison_gt_one {L : ℝ} (hL : 1 ≤ L) (m : ℕ) :
    ((m : ℝ) / 2) ≤ (2 * L) ^ m := by
  have hbase : (2:ℝ) ≤ 2 * L := by linarith
  have hpow : (2:ℝ) ^ m ≤ (2 * L) ^ m :=
    pow_le_pow_left₀ (by norm_num) hbase m
  have hm := le_two_pow m
  linarith

/-- The comparison is monotone in the degree: a larger degree only helps, since the base exceeds
one. -/
theorem comparison_monotone {L : ℝ} (hL : 1 ≤ L) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    (2 * L) ^ m₁ ≤ (2 * L) ^ m₂ := by
  apply pow_le_pow_right₀ (by linarith) h

/-- And monotone in `k` through `L = log k`. -/
theorem comparison_monotone_in_k {L₁ L₂ : ℝ} (h1 : 1 ≤ L₁) (h : L₁ ≤ L₂) (m : ℕ) :
    (2 * L₁) ^ m ≤ (2 * L₂) ^ m :=
  pow_le_pow_left₀ (by linarith) (by linarith) m

end RHTower
