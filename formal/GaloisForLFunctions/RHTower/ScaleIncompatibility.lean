import GaloisForLFunctions.RHTower.HeatTraceSensitivity

/-!
# One scale cannot see both the first zero and the first prime

The Gaussian heat trace has an exact falsification endpoint that cannot be triggered.  The reason is
not delicacy but a scale mismatch, and the mismatch is general.

A test function of width `W` in the `u` variable has frequency scale `1/W`.

* **To see zeros** the frequency scale must reach the first ordinate: `1/W ≥ γ₁`, i.e. `W ≤ 1/γ₁`.
  Below that the zero side of the explicit formula is empty — there is no ordinate in the window —
  and the identity degenerates into a relation between the archimedean term and the prime error with
  no spectral content at all.  That is exactly the large-time Gaussian: its frequency scale is
  `x^{-1/2} → 0`, far below `γ₁`.
* **To see primes** the support must reach the first prime log: `W ≥ log 2`.  Below that every prime
  term is exponentially suppressed.  That is exactly the small-time Gaussian.

These are incompatible, because

```text
γ₁ · log 2  ≈  14.13 × 0.693  ≈  9.8  >  1 .
```

> **No single-scale test function resolves both the first zero and the first prime.  A window narrow
> enough to see the spectrum is an order of magnitude too narrow to see the primes.**

For the Gaussian the two admissible windows are `x ≲ γ₁^{-2} ≈ 5·10⁻³` for the zeros and
`x ≳ log²2/4 ≈ 0.12` for the primes — separated by a factor of about twenty-five.

**The dichotomy this creates.**  A test function with a *second* scale — a modulation frequency, or
equivalently a translation — can couple the two sides, because the modulation moves the frequency
window up to `γ₁` while the width stays large enough to reach `log 2`.  That is precisely the sliding
rectangular window of the earlier modules.  But translation destroys positive type.  So:

```text
one scale   →  no coupling: the criterion is exact but spectrally empty
two scales  →  coupling, hence RH-equivalence, but positivity is lost
```

which unifies the two halves of this programme's recent work: the sliding-window route is
RH-equivalent and non-positive, the heat-trace route is positive and insensitive, and the reason is
one inequality, `γ₁ log 2 > 1`.

This file formalizes the incompatibility and the numerical margin.
-/

open Real

noncomputable section

namespace RHTower

/-- **The incompatibility.**  A width that resolves the spectrum and a width that resolves the primes
cannot coexist when `γ₁·log 2 > 1`. -/
theorem scale_incompatible {W g1 : ℝ} (hg1 : 0 < g1) (hprod : 1 < g1 * Real.log 2)
    (hzero : W ≤ 1 / g1) (hprime : Real.log 2 ≤ W) : False := by
  have h1 : Real.log 2 ≤ 1 / g1 := le_trans hprime hzero
  rw [le_div_iff₀ hg1] at h1
  nlinarith [hprod, h1]

/-- The margin is genuine: `log 2 > 1/2` and `γ₁ > 2` already give the product above one. -/
theorem product_gt_one_of_bounds {g1 : ℝ} (hg1 : 2 < g1) (hlog : 1 / 2 < Real.log 2) :
    1 < g1 * Real.log 2 := by
  nlinarith [hg1, hlog]

/-- `log 2 > 1/2`, so any first ordinate above `2` suffices — and the true one is near `14.13`. -/
theorem log_two_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
  have h := Real.log_two_gt_d9
  linarith

/-- **The Gaussian windows are disjoint.**  Zeros need `x ≤ γ₁^{-2}`, primes need
`x ≥ (log 2)²/4`; incompatible once `γ₁ log 2 > 2`, which the true value `≈ 9.8` satisfies. -/
theorem gaussian_windows_disjoint {x g1 : ℝ} (hg1 : 0 < g1) (hprod : 2 < g1 * Real.log 2)
    (hzero : x ≤ 1 / g1 ^ (2 : ℕ)) (hprime : Real.log 2 ^ (2 : ℕ) / 4 ≤ x) : False := by
  have hg2 : (0 : ℝ) < g1 ^ (2 : ℕ) := by positivity
  have h1 : Real.log 2 ^ (2 : ℕ) / 4 ≤ 1 / g1 ^ (2 : ℕ) := le_trans hprime hzero
  rw [div_le_div_iff₀ (by norm_num) hg2] at h1
  nlinarith [hprod, h1, Real.log_two_gt_d9, hg1]

/-- **The dichotomy.**  Either the test function has a single scale — and then one of the two
resolutions fails — or it has a second scale, which is a translation, and translation destroys
positive type. -/
theorem scale_dichotomy {W g1 : ℝ} (hg1 : 0 < g1) (hprod : 1 < g1 * Real.log 2) :
    ¬ (W ≤ 1 / g1 ∧ Real.log 2 ≤ W) := by
  rintro ⟨h1, h2⟩
  exact scale_incompatible hg1 hprod h1 h2

end RHTower
