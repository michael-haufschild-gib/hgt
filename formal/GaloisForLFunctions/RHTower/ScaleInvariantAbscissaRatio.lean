import GaloisForLFunctions.RHTower.DilationFrobeniusShift

/-!
# The critical-to-convergence ratio is a scale invariant

The dilation direction supplies genuine noncommutativity, and dilations shift the archimedean symbol
by `-2 log λ`.  It is tempting to use that to carry the criterion into the half-plane of absolute
convergence, where positivity is free.  It cannot be done, and the reason is a one-line invariance.

**Correction.**  An earlier reading of the dilation action claimed that dilating by `λ = 1/k` turns
the prime weight `Λ(n) n^{-1/2}` into `Λ(n) n^{-k/2}`, i.e. moves the abscissa **up** to `k/2`.  That
is false: the weight is attached to `n`, and re-indexing the frequency does not change it.  What
actually happens is

```text
Σ_n Λ(n) n^{-1/2} δ_{log n}   ↦   Σ_n Λ(n) n^{-1/2} δ_{k log n}
                               =   Σ_{m = n^k} Λ(m) m^{-1/(2k)} δ_{log m} ,
```

using `n^{-1/2} = (n^k)^{-1/(2k)}`.  So the dilated form sits at abscissa `1/(2k) < 1/2`, supported on
perfect `k`-th powers: the dilation moves the abscissa **down**, away from convergence, and thins the
support.

**And the general reason.**  Rescaling `s ↦ s/k` sends the zeros of `ζ` to the line `Re s = k/2` and
the abscissa of absolute convergence from `1` to `k`.  Both move by the same factor, so

```text
(critical abscissa) / (convergence abscissa)  =  (k/2) / k  =  1/2 ,
```

independently of `k`.

> **The ratio of the critical abscissa to the abscissa of absolute convergence is a scale invariant.
> No dilation can bring the critical line into the region of absolute convergence, because the two
> move together.  The `ax + b` noncommutativity is real, but it acts trivially on the only quantity
> that matters.**

This is why every rescaling argument fails at once, and it is a genuine constraint on the dilation
lane rather than a failure of a particular attempt.

This file formalizes the weight identity, the downward abscissa motion, and the scale invariance of
the ratio.
-/

open Real

noncomputable section

namespace RHTower

/-- **The weight identity.**  Re-indexing the frequency by `m = n^k` rewrites the weight exponent as
`1/(2k)`, not `k/2`: `n^{-1/2} = (n^k)^{-1/(2k)}`. -/
theorem dilated_weight_identity {n : ℝ} (hn : 0 < n) {k : ℝ} (hk : 0 < k) :
    n ^ (-(1:ℝ) / 2) = (n ^ k) ^ (-(1:ℝ) / (2 * k)) := by
  rw [← Real.rpow_mul (le_of_lt hn)]
  congr 1
  field_simp

/-- **The abscissa moves down.**  For `k ≥ 2` the dilated abscissa `1/(2k)` is below `1/2`. -/
theorem dilated_abscissa_lt {k : ℝ} (hk : 2 ≤ k) : 1 / (2 * k) < 1 / 2 := by
  have hkpos : (0:ℝ) < k := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- The dilated abscissa is also below the convergence threshold, so nothing is gained. -/
theorem dilated_abscissa_lt_one {k : ℝ} (hk : 2 ≤ k) : 1 / (2 * k) < 1 := by
  have := dilated_abscissa_lt hk
  linarith [this]

/-- **The scale invariant.**  Under `s ↦ s/k` the critical abscissa becomes `k/2` and the abscissa of
absolute convergence becomes `k`; their ratio is `1/2` for every `k`. -/
theorem abscissa_ratio_invariant {k : ℝ} (hk : k ≠ 0) : (k / 2) / k = 1 / 2 := by
  field_simp

/-- The invariance is exact at every scale, so no choice of scale improves the configuration. -/
theorem ratio_independent_of_scale {k₁ k₂ : ℝ} (h1 : k₁ ≠ 0) (h2 : k₂ ≠ 0) :
    (k₁ / 2) / k₁ = (k₂ / 2) / k₂ := by
  rw [abscissa_ratio_invariant h1, abscissa_ratio_invariant h2]

/-- **No dilation reaches convergence.**  The rescaled critical abscissa is always strictly below the
rescaled convergence abscissa, by exactly a factor two. -/
theorem critical_below_convergence {k : ℝ} (hk : 0 < k) : k / 2 < k := by linarith

end RHTower
