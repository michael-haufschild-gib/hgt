# Estermann's zeta function: the analytic layer

**Status:** the analytic layer is closed through the smoothed twisted divisor sum
(`estermann_smoothed_sum`, MUST-379). Previously: in progress. Definition, functional equation, divisor series, entire completion, exact
principal part, closed form of the character sum, left-half-plane polynomial bound **and the
convexity bound on the closed strip `-1 ≤ Re s ≤ 2`** are proved in Lean and axiom-clean. The
former open core (the middle strip) is closed. The remaining work is the Perron/Mellin step and
the shifted divisor correlation.

## Why this is on the RH critical path

Every route in the corpus that reaches a positive proportion of zeros on the critical line
(Levinson, the mollified criterion, the grid-density route) terminates at one analytic statement:
the **mollified second moment** of `ζ` on the critical line. Its analytic core is the **twisted
second moment** `∫_0^T |ζ(1/2+it)|² (h/k)^{-it} dt`. The corpus owns the diagonal
(`Sieve/TwistedDiagonalAdapted`, `Sieve/BchbDensityIntegral`, `Sieve/TwistedMainTermMerge`); the
off-diagonal is still only the trivial row bound of `Sieve/TwistedOffDiagonalSum`.

The off-diagonal is a shifted divisor correlation, and the generating function of the twisted
divisor sum is Estermann's zeta function

```text
D(s, a/q) = ∑_{N ≥ 1} d(N) e(aN/q) N^{-s}.
```

It is absent from mathlib and was absent from the corpus.

## What is proved

`RHTower/EstermannZeta.lean`
* `estermannZeta q a s = q^{-s} ∑_{c mod q} expZeta(ac/q, s) · hurwitzZeta(c/q, s)`.
* `estermannZeta_one_sub`: the functional equation
  `D(1-s, a/q) = 2 q^{2s-1} (2π)^{-2s} Γ(s)² (D(s, ā/q) + cos(πs) D(s, -ā/q))` for `a` a unit.
* `hasSum_estermannZeta`: the absolutely convergent double series for `Re s > 1`.
* `estermannZeta_eq_polar_add_regular`, holomorphy off `s = 1`,
  `tendsto_sq_sub_one_mul_estermannZeta` (leading Laurent coefficient `1/q`).

`RHTower/EstermannDivisorSeries.lean`
* `hasSum_divisorCount`: a general regrouping of a double series by the product of its indices
  (the fibre of `(m,n) ↦ mn` over `N` is `N.divisorsAntidiagonal`).
* `hasSum_estermannZeta_divisor`, `LSeries_estermannCoeff`: `D(s,a/q) = ∑ d(N) e(aN/q) N^{-s}`.

`RHTower/EstermannEntire.lean`
* `estermannEntire`, `differentiable_estermannEntire`, `estermannEntire_eq`:
  `(s-1)² D(s, a/q)` is entire.

`RHTower/EstermannPrincipalPart.lean`
* `dft_const_one`, `sum_expZeta_eq`: `∑_{c mod q} expZeta(c/q, s) = q^{1-s} ζ(s)`.
* `estermannCharSum_eq`: for `a` a unit, `∑_{c ≠ 0} expZeta(ac/q, s) = (q^{1-s} - 1) ζ(s)`.
* `estermannZeta_eq_zetaSq_add`: **the character sum disappears**,
  `D(s, a/q) = q^{1-2s} ζ(s)² + q^{-s} R_a(s)` with `R_a` entire.
* `zetaEntire_eq_riemannZeta₁`, `estermannEntire_eq_reduced`.
* `estermannEntire_one : (s-1)²D → 1/q` and
  `deriv_estermannEntire_one : = (2γ - 2 log q)/q`.
  So the whole principal part is
  `D(s, a/q) = (1/q)(s-1)^{-2} + ((2γ - 2 log q)/q)(s-1)^{-1} + O(1)`, **independent of `a`**.

`RHTower/EstermannGrowth.lean`, `RHTower/EstermannLeftGrowth.lean`
* `norm_estermannZeta_le`: the right edge, `‖D(s,a/q)‖ ≤ (∑' (n+1)^{-σ})²` for `σ > 1`.
* `exists_bound_norm_estermannZeta_one_sub`: **polynomial growth on the left**. For `2 ≤ Re s ≤ M`
  and `|Im s| ≥ 1`, `‖D(1-s, a/q)‖ ≤ C |t|^N`. The `Γ(s)²` decay `e^{-π|t|}` cancels the `cos(πs)`
  growth `e^{π|t|}` exactly.

`RHTower/HurwitzFiniteExpansion.lean`
* `sum_stdAddChar_mul`: orthogonality of `ZMod.stdAddChar`.
* `hurwitzZeta_eq_sum_expZeta`: **the finite additive expansion**
  `ζ(s, c/q) = q^{s-1} ∑_{j mod q} e(cj/q) expZeta(-j/q, s)` for `s ≠ 1`.
  Dual to `sum_expZeta_eq`; it reduces every growth question for the Hurwitz zeta at rational
  argument to one for `expZeta`.

## The middle strip is closed

A contour shift for the off-diagonal needs `‖D(s, a/q)‖` on a strip containing `Re s = 1`. This is
now proved, through a Phragmén–Lindelöf interpolation whose a priori input required four new
pieces of analysis, none of them in mathlib.

`HTGeometry/MellinMajorant.lean`
* `mellinMajorant f σ = ∫_0^∞ t^{σ-1}‖f t‖ dt` and `norm_mellin_le : ‖mellin f s‖ ≤ mellinMajorant f (Re s)`
  — the majorant depends only on the abscissa.
* `mellinMajorant_le`: `t^{σ-1} ≤ t^{σ₀-1} + t^{σ₁-1}`, so the majorant is bounded on a strip by
  the sum of its two endpoint values.
* `exists_bound_norm_WeakFEPair_Λ₀`: **every weak functional-equation pair's `Λ₀` is bounded on
  every vertical strip, uniformly in the height**, since `Λ₀ = mellin f_modif` and `f_modif` is
  Mellin convergent everywhere (`IsStrongFEPair.hasMellin`).

`HTGeometry/GammaReciprocalExpBound.lean`, `HTGeometry/GammaReciprocalStripBound.lean`
* `norm_Gamma_le_Gamma_re : ‖Γ(s)‖ ≤ Γ(Re s)` for `Re s > 0`, from the Euler integral.
* `inv_Gamma_eq : 1/Γ(z) = Γ(1-z) sin(πz)/π` — valid with mathlib's junk conventions at the poles.
* `norm_inv_Gamma_le : ‖1/Γ(z)‖ ≤ Γ(1-Re z) e^{π|Im z|}/π` for `Re z < 1`.
* `norm_inv_Gamma_le_shift`: one step of `Γ(z) = (z-1)Γ(z-1)` moves this to `Re z < 2`.
* `exists_bound_norm_inv_Gammaℝ : ‖1/Gammaℝ(s)‖ ≤ C e^{π|t|/2}` on every strip with `Re s < 4`,
  `|t| ≥ 2`.

`HTGeometry/HurwitzZetaStripExpBound.lean`
* Strip bounds for `completedHurwitzZetaEven`, `completedCosZeta`, `completedHurwitzZetaOdd`,
  `completedSinZeta` (the two simple poles cost `1/2` each above height two).
* **`exists_bound_norm_hurwitzZeta_strip`, `exists_bound_norm_expZeta_strip`:**
  `‖ζ(s,a)‖, ‖expZeta(a,s)‖ ≤ C e^{π|t|/2}` for `σ₀ ≤ Re s ≤ σ₁ < 3`, `|t| ≥ 2`.
  Mathlib records no size estimate for these functions at all.

`RHTower/EstermannStripExpBound.lean`
* `exists_bound_norm_estermannZeta_strip_exp : ‖D(s,a/q)‖ ≤ C e^{π|t|}` on the strip.

`RHTower/EstermannEdgeBounds.lean`
* `exists_bound_norm_estermannEntire_right` (at `Re s = 2`, from absolute convergence) and
  `exists_bound_norm_estermannEntire_left` (at `Re s = -1`, from the functional equation at
  reflected abscissa `2`), both extended across `|t| ≤ 1` by continuity.

`RHTower/EstermannStripPolynomialBound.lean`, `RHTower/EstermannConvexity.lean`
* `exists_bound_norm_estermannEntire_strip`: **the convexity bound.** Applying
  `PhragmenLindelof.vertical_strip` to `g(s) = (s-1)²D(s)/(s+2)^N` on the strip of width three
  (admissible exponent `c = 1/2 < π/3`) gives one constant and one exponent for the whole closed
  strip `-1 ≤ Re s ≤ 2`.
* `exists_bound_norm_estermannZeta_strip : ‖D(s,a/q)‖ ≤ C(1+|t|)^N` for `-1 ≤ Re s ≤ 2`, `|t| ≥ 1`.

## The Perron step

`RHTower/ExponentialMellinPerron.lean`
* `mellinInv_gamma_mul_LSeries_eq_tsum_exp`: **exponentially smoothed Perron inversion for an
  arbitrary Dirichlet series.** For `c > 0`, `a 0 = 0` and `∑ ‖a n‖ n^{-c} < ∞`,
  `∑_n a n e^{-nx} = (1/2π)∫_ℝ x^{-(c+it)} Γ(c+it) L(a, c+it) dt`.
  No boundedness of the coefficients is assumed (the corpus's earlier
  `mellinInv_two_gamma_mul_LSeries_eq_coeffLaplaceProfile` needs `‖f n‖ ≤ B`), and the line is
  arbitrary. Built from the corpus's Cahen–Mellin integral
  `SelbergClass.mellinInv_line_Gamma_eq_exp_neg` and `gamma_verticalIntegrable_of_pos`, with the
  sum/integral interchange by `hasSum_integral_of_summable_integral_norm`.

`RHTower/EstermannExponentialMellin.lean`
* `summable_divisorCount_rpow`: `∑ d(n) n^{-c} < ∞` for `c > 1`, via the divisor regrouping
  `hasSum_divisorCount` applied to the shifted `p`-series.
* `estermann_exponential_mellin`: **the exact starting identity**
  `∑_{N} d(N) e(aN/q) e^{-Nx} = (1/2π)∫_ℝ x^{-(c+it)} Γ(c+it) D(c+it, a/q) dt` for every `c > 1`.

The Gamma factor decays like `e^{-π|t|/2}`, which beats the polynomial growth of `D` on the whole
closed strip, so the same integral converges absolutely on every line in `-1 ≤ Re s ≤ 2`.

## The double-pole residue calculus

`HTGeometry/RectangleDoublePole.lean`
* `rectIntegral_cauchyKernelSq`: **the rectangle boundary integral of `(z-p)^{-2}` is zero.** The
  squared Cauchy kernel has the single-valued antiderivative `-(z-p)^{-1}`, so the four edges
  telescope; a second-order pole carries no winding.
* `rectIntegral_eq_double_pole_residue_on`: if `F = A (z-p)^{-2} + B (z-p)^{-1} + R` off `p`, with
  `R` analytic on a neighbourhood of the closed rectangle and `p` strictly inside, then
  `rectIntegral F z₁ z₂ = 2πi B` — only the residue survives.

This is the missing case in the corpus's rectangle residue calculus, which covered simple poles
only (`rectIntegral_eq_two_pole_residues`, `RectangleIntegral'_eq_sumResiduesIn` both assume
`HasSimplePolesOn`). It is what a contour shift past the double pole of `ζ²`, of Estermann's zeta,
or of any Rankin–Selberg square consumes.

## Cauchy's derivative formula on a rectangle

`HTGeometry/AnalyticDoublePoleSplit.lean`
* `slopeExt f p` — the difference quotient of `f` at `p`, extended by `deriv f p`;
  `differentiableOn_slopeExt` proves it holomorphic, from the removable singularity theorem and
  `hasDerivAt_iff_tendsto_slope`. No second derivative, no power series.
* `exists_doublePole_split`: `f s = f p + f'(p)(s−p) + (s−p)² G s` with `G` holomorphic, by
  applying the slope extension twice.
* `exists_doublePole_principalPart`: the same in the normal form
  `f s/(s−p)² = f p (s−p)^{-2} + (f'(p)(s−p)^{-1} + G s)`.

`HTGeometry/RectangleDerivativeFormula.lean`
* `rectIntegral_div_sub_sq_eq_deriv`: **`∮_{∂R} f(s)/(s−p)² ds = 2πi f'(p)`** for `f` holomorphic
  on a neighbourhood of the closed rectangle and `p` strictly inside. Mathlib has the circle
  version; the corpus's rectangle residue calculus covered simple poles only.

This is the last missing tool for the contour shift: the integrand is
`x^{-s}Γ(s)D(s,a/q) = g(s)/(s−1)²` with `g = x^{-s}Γ(s)·estermannEntire(s)` holomorphic on
`Re s > 0`, and the shift's residue is `g'(1)`.

## The rectangle identity is closed

`RHTower/EstermannMellinNumerator.lean`
* `estermannMellinNumerator q a x s = x^{-s} Γ(s) · (s-1)² D(s, a/q)`, holomorphic on `Re s > 0`
  (`differentiableOn_estermannMellinNumerator`), with
  `estermannMellinNumerator_div : N(s)/(s-1)² = x^{-s} Γ(s) D(s, a/q)` off `s = 1`.
* `deriv_Gamma_one : Γ'(1) = -γ`, from `Complex.digamma_one` and `Γ(1) = 1`.
* **`deriv_estermannMellinNumerator_one`:** the residue,

```text
N'(1) = (γ - log x - 2 log q)/(q x).
```

  The three factors contribute `-log x`, `Γ'(1) = -γ` and the Estermann residue `(2γ-2 log q)/q`.

`RHTower/EstermannRectangleIdentity.lean`
* **`rectIntegral_estermannMellinIntegrand`:** for `x, T > 0`,

```text
∮_{∂([½,2]×[-T,T])} x^{-s} Γ(s) D(s, a/q) ds = 2πi (γ - log x - 2 log q)/(q x).
```

  Exact, at every finite height, by Cauchy's derivative formula on a rectangle.

With `x = 1/X` the residue is `(X/q)(log(X/q²) + γ)` — the main term of the smoothed twisted
divisor sum.

## The horizontal edges vanish

`RHTower/EstermannHorizontalDecay.lean`
* `tendsto_poly_mul_exp_neg_zero K hc : (1+T)^K e^{-cT} → 0` for `c > 0`, by the substitution
  `w = c(1+T)` into `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`.
* `rpow_neg_le_of_mem : x^{-u} ≤ x^{-1/2} + x^{-2}` for `u ∈ [½,2]` (both monotonicity cases).
* `exists_bound_norm_estermannMellinIntegrand_horizontal`: on `Re s ∈ [½,2]`, `|Im s| ≥ 1`,

```text
‖x^{-s} Γ(s) D(s,a/q)‖ ≤ C (1+|t|)^N e^{-π|t|/2},
```

  from the three factor bounds: the constant weight, `exists_bound_norm_Gamma_vertical_strip`, and
  the convexity bound `exists_bound_norm_estermannZeta_strip`.
* **`tendsto_horizontal_estermannMellin`:** both horizontal edge integrals
  `∫_{1/2}^{2} x^{-s}Γ(s)D(s,a/q) du` at height `±T` tend to `0` as `T → ∞`.

The Gamma decay `e^{-π|t|/2}` beats the polynomial convexity bound, which is exactly what the
Phragmén–Lindelöf work earlier in this card was for.

## The contour shift is closed

`RHTower/EstermannVerticalIntegrable.lean`
* `integrable_estermannMellinIntegrand_vertical`: on a line `0 < Re s ≤ 2`, `Re s ≠ 1`, the
  integrand `x^{-s}Γ(s)D(s,a/q)` is integrable. Continuity comes from `Γ` (right half plane) and
  `D` (off `s = 1`); above unit height the tail bound is `C(1+|t|)^N e^{-π|t|/2}`, and raising the
  constant absorbs the compact part `|t| ≤ 1`, so a single majorant
  `K(1+|t|)^N e^{-(π/2)|t|}` dominates the whole line.

`RHTower/EstermannContourShift.lean`
* **`estermannMellin_vertical_difference`:**

```text
∫_ℝ x^{-(2+iv)} Γ(2+iv) D(2+iv, a/q) dv - ∫_ℝ x^{-(½+iv)} Γ(½+iv) D(½+iv, a/q) dv
  = 2π · (γ - log x - 2 log q)/(q x).
```

  The rectangle identity holds at every height; the horizontals vanish and the verticals converge
  (`MeasureTheory.intervalIntegral_tendsto_integral`), so the limit is exact.

Since `mellinInv σ (Γ·D) x = (1/2π)·(the vertical integral at `Re s = σ`)`, this is

```text
mellinInv 2 (Γ·D) x - mellinInv (1/2) (Γ·D) x = (γ - log x - 2 log q)/(q x),
```

and with `estermann_exponential_mellin` at `c = 2`,

```text
∑_N d(N) e(aN/q) e^{-Nx} = (γ - log x - 2 log q)/(qx) + mellinInv (1/2) (Γ·D) x,
```

the remaining integral being `O(x^{-1/2})` by the same line bound.

## Earlier framing of the same step

Combine: the vertical edges converge to the full vertical integrals (by integrability of
`Γ(σ+it)D(σ+it)` on each line, from the same three bounds), so the rectangle identity passes to
the limit and gives

```text
mellinInv 2 (Γ·D) x - mellinInv (1/2) (Γ·D) x = (γ - log x - 2 log q)/(q x),
```

i.e. `∑_N d(N) e(aN/q) e^{-Nx} = (γ - log x - 2 log q)/(qx) + O(x^{-1/2})`.

## Earlier framing of the same step

Let `T → ∞` in the rectangle identity. The horizontal edges decay like `T^N e^{-πT/2}` (the Gamma
factor beats the convexity bound for `D` on `[½,2]`), and the vertical edges converge to the full
vertical integrals, giving

```text
mellinInv 2 (Γ·D) x - mellinInv (1/2) (Γ·D) x = (γ - log x - 2 log q)/(q x),
```

i.e. `∑_N d(N) e(aN/q) e^{-Nx} = (γ - log x - 2 log q)/(q x) + O(x^{-1/2})`.
Then the shifted divisor correlation, then the BCHB off-diagonal.

## Superseded next step

Move the contour of `x^{-s}Γ(s)D(s,a/q)` from `Re s = 2` to `Re s = 1/2` (staying right of the
pole of `Γ` at `s = 0`), using `rectIntegral_eq_double_pole_residue_on` with `U = {Re z > 0}` and
the polynomial strip bound for the vanishing of the horizontal edges. The residue at the
double pole is

```text
Res_{s=1} x^{-s} Γ(s) D(s, a/q) = (1/(qx)) (log(1/(x q²)) + γ),
```

so with `x = 1/X`,
`∑_N d(N) e(aN/q) e^{-N/X} = (X/q)(log(X/q²) + γ) + O(X^{-1/2})`.
The horizontal edges vanish because `‖Γ‖ ≪ |t|^N e^{-π|t|/2}` beats the polynomial bound for `D`.
Then the shifted divisor correlation, then the BCHB off-diagonal.

## A repository fix made on the way

`SelbergClass/ComplexRayMellinInversionGeneralLine.lean` referenced `RHTower.mellin_exp_neg_mul`,
which had been renamed to `mellin_exp_neg_mul_finiteExponentialSumMellin` (the name now resolves
only to a `private` lemma in `HasseSondowRowMellin`). The module therefore did not build, which
also broke `GaloisForLFunctions.SelbergClass` and `MainTheorems`. The reference is corrected.

## What this does not do

Nothing here proves or refutes RH. The twisted second moment is a *known* theorem
(Balasubramanian–Conrey–Heath-Brown 1985); what is new is that it becomes available to the corpus
unconditionally and in Lean, unblocking the Levinson consumer chain whose only missing input is the
mollified second moment.
