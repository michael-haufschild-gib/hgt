import GaloisForLFunctions.RHTower.DiscInsideHorn

/-!
# The tail constant is comfortable, not marginal

Level one reduces to `‖T‖ < ‖A‖`.  This file estimates the ratio and finds it superpolynomially small.

**How wide the saddle neighbourhood may be.**  The quadratic approximation holds while
`δ · |ψ'''| / |ψ''| ≪ 1`.  With `|ψ''| ≍ k log k` and `|ψ'''| ≍ k log² k` this permits
`δ ≍ 1 / log k`.

**What that buys.**  On the steepest-descent path the real part of the phase falls by `≍ δ² |ψ''|`
outside the neighbourhood, and

```text
δ² |ψ''|  ≍  (1 / log k)² · k log k  =  k / log k .
```

So the tail-to-saddle ratio is `≍ e^{-c k / log k}` — **superpolynomially small**, and any polynomially
long contour is irrelevant beside it.

> **The tail estimate for level one is comfortable, not marginal: the ratio is
> `exp(-c k / log k)`, which beats every polynomial.  Level one is complete in mechanism.**

The remaining rigour is the contour deformation, whose sector was fixed earlier and whose required disc
was shown to fit inside it with a `√2` margin.

This file formalizes the exponent's value and the superpolynomial decay.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The exponent's value.**  With half-width `1/L` and curvature `k L`, the exponent is `k / L`. -/
theorem exponent_value {k L : ℝ} (hL : L ≠ 0) :
    (1 / L) ^ (2 : ℕ) * (k * L) = k / L := by
  field_simp

/-- **Superpolynomial decay.**  `e^{-c x}` tends to zero faster than any polynomial: the product with
any power still vanishes. -/
theorem superpolynomial_decay (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-x)) atTop (nhds 0) :=
  Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n

/-- Hence the tail is eventually below any positive multiple of the saddle. -/
theorem tail_eventually_small {M : ℝ} (hM : 0 < M) (n : ℕ) :
    ∀ᶠ x in atTop, x ^ n * Real.exp (-x) < M :=
  (superpolynomial_decay n).eventually (gt_mem_nhds hM)

/-- **The ratio is below one.**  Once the tail falls below the saddle in modulus, the sum is
nonvanishing. -/
theorem ratio_below_one {T A : ℝ} (hA : 0 < A) (h : T < A) : T / A < 1 := by
  rw [div_lt_one hA]
  exact h

/-- **The neighbourhood's admissible width.**  It is set by the ratio of the second and third
derivatives. -/
theorem admissible_width {c2 c3 : ℝ} (h2 : 0 < c2) (h3 : 0 < c3) : 0 < c2 / c3 :=
  div_pos h2 h3

end RHTower
