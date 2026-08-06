# Chebyshev at the width-`1/log` rectangle: the exponent-`1/2` route

**Status:** in progress.  The contour bound is proved; the choice of height and width, and the
assembly of the rate, remain.

## Why this is a different route, not a re-tuning

`docs/drafts/pipeline/1-in-progress/moebius-exponent-upgrade.md` established that the Möbius
contour stops at saving exponent `1/3`, because its integrand carries `1/ζ` and the corpus can
bound `1/ζ` polynomially in the logarithm only on a strip of width `log^{-2}|γ|`.

The Chebyshev contour's integrand carries `ζ'/ζ`.  Its regular part
`zetaLogDerivReg s = -(logDeriv zetaResidueUnit s)` is bounded by `C log²|γ|` on the **full width**
of the exponent-one region — `exists_logDeriv_zeta_bound_explicit` already proved that, with width
`(1/40000)/log|γ|`.  Width `≍ 1/log` is `w = 1`, and the saving exponent is `1/(w+1) = 1/2`: the
classical `exp(-c√(log x))`.

No new analytic input is needed.  Only the contour has to be instantiated.

## Proved this session

1. `RHTower/Sieve/ZetaLogDerivRegUniform.lean`
   - `exists_bound_zetaLogDerivReg_box` — the compact-box bound at **arbitrary** height,
     generalising `exists_bound_zetaLogDerivReg_low_box` (which was hard-coded to `|Im| ≤ 9`).
   - `exists_zeta_uniform_kappa_one_zero_free` — the width-`(1/40000)/log K` strip is zero-free,
     with **no height restriction**, and pinned to a contour parameter `K ≥ |Im s|`.
   - `exists_bound_zetaLogDerivReg_uniform` — likewise `‖zetaLogDerivReg s‖ ≤ C log²K` on that
     strip.  The pole term is split off with `neg_logDeriv_riemannZeta_eq` and costs `≤ 1/4`,
     because `‖s-1‖ ≥ |Im s| ≥ 4` on the region branch.

2. `RHTower/Sieve/ChebyshevKappaOneData.lean` — `chebLeftTwo T = 1 - (1/40000)/log T`,
   `chebRightTwo T = 1 + 1/log T`, and `exists_cheb_kappa_one_data`: all five hypotheses of
   `norm_tsum_vonMangoldt_sub_full_main_le_explicit` at that rectangle, with the single bound
   `C log²T` for the left edge and both horizontal edges.

3. `RHTower/Sieve/ChebyshevKappaOneContour.lean` —
   `exists_norm_tsum_vonMangoldt_kappa_one_general`: the five-term contour estimate at the
   width-`1/log` rectangle, with cutoff-uniform constants.

All unconditional (`[propext, Classical.choice, Quot.sound]`).

## Traps

- **`8 ≤ Real.log T` does not imply `T > 0`.**  Mathlib's `Real.log x = Real.log |x|`, so
  `T = -e^8` satisfies it.  Carry `1 ≤ T` as a separate hypothesis.
- `rw [hsplit]` with `hsplit : s = ↑s.re + ↑s.im * I` rewrites `s` inside `|s.im|` on the
  right-hand side too.  Apply the lemma first and `rwa [← hsplit] at h` instead.
- `linarith` cannot see through `chebLeftTwo`; unfold it in the membership hypothesis
  (`rw [Set.uIoc_of_le hcd, chebLeftTwo] at hx`).
- `smoothWeight` in `RHTower.Sieve` shadows `GaloisForLFunctions.HTGeometry.smoothWeight` once
  enough modules are imported.  Fully qualify it in statements.

## Next

1. **The height.**  `d(T) - 1 = 1/log T` and `c(T) - 1 = -(1/40000)/log T`, so the left edge is
   `(N+H)^{1 - (1/40000)/log T} = (N+H)·exp(-log(N+H)/(40000 log T))` and the truncation error is
   `(N+H)^{d}/T ≈ (N+H)·exp(log(N+H)/log T)/T`.  Balancing gives `log T ≍ √(log x)`, hence
   `exp(-c√(log x))`.  Choose `chebHeightTwo x = exp(A√(log x))` with `A` large enough to separate
   the two edges — the same lesson as the Möbius parameter's factor `2`.
2. **The width.**  `Λ(n) ≤ log n`, so the smooth-versus-sharp comparison costs `(H+1)·log(N+H)`,
   one logarithm more than the Möbius case (`ChebyshevSmoothVsSharp.lean` already states this).
   The ratio should be `exp(√(log x)/c)` for a suitable `c`, a fraction of the same power.
3. **The main term.**  Unlike the Möbius case there is a main term:
   `mellin w 1 · (2 arctan(T/(d-1)) - 2 arctan(T/(c-1)))`, which tends to `2π·(N+H-N)`-ish.  The
   corpus's `ChebyshevMainTerm*` modules handle it at κ=9 and should transfer.

## Payoff

The vendored `PNTPlus.MediumPNT` proves `ψ - id =O[atTop] x·exp(-c(log x)^{1/10})`.  The corpus's
own `Chebyshev*` chain reaches only `ψ(N)/N → 1`.  A completed κ=1 chain beats both and matches the
classical exponent.

## Step 1 done: the balanced height, with exact identities

`RHTower/Sieve/ChebyshevHeightOne.lean`:

```
chebHeightOne x = exp( 2 √(log x) )
```

Because the height is a *real* exponential rather than a natural-number ceiling, both balance
conditions come out as **exact identities**, not inequalities:

- `saving_exponent_one` : `(1/40000)/log T · log x = √(log x)/80000`
- `right_exponent_one`  : `(1/log T) · log x = √(log x)/2`
- `exp_right_le_chebHeightOne` : `exp((1/log T)·log x) = exp(-(3/2)√(log x)) · T`

`RHTower/Sieve/ChebyshevRatePowersOne.lean` turns them into the two edge powers, again exactly:

- `rpow_chebLeftTwo_at`  : `x^{c(T)} = x · exp(-√(log x)/80000)`
- `rpow_chebRightTwo_at` : `x^{d(T)} = x · exp(-(3/2)√(log x)) · T`

**Why the factor `2` in the height.**  At `log T = √(log x)` the truncation term's growth
`x^{1/log T} = exp(√(log x))` exactly cancels `1/T`, and nothing at all is saved.  Doubling splits
them: `1/80000` to the left edge, `3/2` to the right.  This is the same phenomenon as the Möbius
parameter's factor `2`, and it is the third time it has appeared — it is a property of the balance,
not of the particular chain.

**Contrast with the Möbius chain.**  There the parameter was `⌈exp(2(log x)^{1/3})⌉₊` and every
balance was an inequality, because the ceiling only gives `2t ≤ log K ≤ 2t+1`.  Here `T` is real,
so no squeeze is needed at all.

## Still to do

- the smoothing width (ratio `exp(√(log x)/c)`, a fraction of the same power);
- the main term `mellin w 1 · (2 arctan(T/(d-1)) - 2 arctan(T/(c-1)))` — the corpus's
  `ChebyshevMainTerm*` modules handle it at κ=9;
- `∑' Λ(n) n^{-d(T)}`, which is `≍ 1/(d-1) = log T`;
- the smooth-versus-sharp comparison, costing `(H+1)·log(N+H)`;
- the assembly.

## Step 2 done: the smoothing width

`RHTower/Sieve/ChebyshevWidthOne.lean`:

```
chebRatioOne N = exp( √(log N) / 240000 ),      chebWidthOne N = N / chebRatioOne N
```

The denominator is forced from both sides.  The contour coefficient carries `(N/H)²`, so a ratio
`exp(√(log N)/α)` costs `exp(2√(log N)/α)` against the left edge's saving `exp(-√(log N)/80000)`;
that needs `α > 2·80000`.  The comparison with the sharp sum costs `(H+1)·log(N+H)`, i.e.
`N·log N·exp(-√(log N)/α)`, which needs `α` not too large.  `α = 240000` leaves
`exp(-√(log N)/240000)` on both sides.

Also proved here, and reusable:

```
sq_le_exp_div_gen : 0 ≤ t → 0 < k → t² ≤ 4k²·exp(t/k)
```

the general "absorb a polynomial into an exponential" step, from `x + 1 ≤ exp x` squared.  The
Möbius chain's `sq_le_exp_div` is exactly the case `k = 108` (`4·108² = 46656`).

## Note on the lint gate

A `formal lint` run during this session reported
`owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry:
GaloisForLFunctions.HTGeometry.AdjoinFractionTransport`.  That module belongs to another agent's
concurrent HTGeometry work, not to this chain; every module of this chain is registered in
`GaloisForLFunctions/RHTower.lean` and the RHTower umbrella builds clean.

## Step 3 done: the main term's bracket, quantitatively

`RHTower/Sieve/ChebyshevBracketBound.lean`.  The corpus proves the bracket
`2 arctan(T/(d-1)) - 2 arctan(T/(c-1))` tends to `2π` only qualitatively
(`tendsto_bracket_at_choice`, and only for a *symmetric* rectangle).  The κ=1 rectangle is
asymmetric, and an error term needs a rate:

```
abs_bracket_sub_two_pi_le :
  c < 1 → 1 < d → 0 < T →
  |2 arctan(T/(d-1)) - 2 arctan(T/(c-1)) - 2π| ≤ 2·((d-c)/T)
```

— the rectangle's aspect ratio.  No mean value theorem is needed:

- `arctan_le_self` : `0 ≤ z → arctan z ≤ z`, from `Real.lt_tan` and `Real.tan_arctan`.
  **Mathlib has no `arctan z ≤ z`** (checked: `Real.arctan_le_self` and `Real.arctan_le_arctan` do
  not exist); `Real.lt_tan (0 < x) (x < π/2) : x < tan x` is the way in.
- `pi_div_two_sub_arctan_le` : `0 < u → π/2 - arctan u ≤ 1/u`, via `Real.arctan_inv_of_pos`.

At the κ=1 rectangle the width is `chebRightTwo T - chebLeftTwo T = (1 + 1/40000)/log T`, so the
bracket error is `≤ 3/(T log T)` — utterly negligible against the saving.

Also added to `ChebyshevKappaOneData.lean`: `one_sub_chebLeftTwo_inv` (`(1-c)⁻¹ = 40000 log T`) and
`half_le_chebLeftTwo` (so dividing by `c` costs at most a factor two).

## The size of each of the five terms, at the balanced choice

With `x ≈ N+H`, `t = √(log x)`, `T = exp(2t)`, `N/H = exp(t/240000)`:

| term | size |
|---|---|
| `2(S·Cd)/T` | `x·t²·exp(-(3/2)t + t/120000)` |
| `(1-c)⁻¹(2(N+H)^c/c + 2Cc)` | `t·x·exp(-t/240000)` ← **dominant** |
| `2(d-c)((Cd/T² + ‖mellin w 1‖)/T)` | `x·exp(-2t)/t` |
| `M(2(N+H)^c/c + 2Cc)` | `t²·x·exp(-t/240000)` |
| `2(d-c)(R·Cd/T²)` | tiny |

`-1/80000 + 1/120000 = -1/240000` is the balance.  Total `O(x·t²·exp(-t/240000))`; absorbing `t²`
with `sq_le_exp_div_gen` gives `O(x·exp(-t/480000))`.  The smooth-versus-sharp comparison
`(H+1)·log(N+H) ≈ x·t²·exp(-t/240000)` is the same size.

Expected capstone: `|ψ(N) - N| ≪ N·exp(-√(log N)/480000)`.

Remaining: `∑' Λ(n)n^{-d}` is already covered (`tsum_vonMangoldt_rpow_neg_le`, giving
`8/(d-1)² = 8log²T`); `‖mellin w 1‖` via `mellin_smoothWeight_one_eq_ofReal`; then the assembly and
the sharp comparison.

## Step 4 done: the remaining shape data

`RHTower/Sieve/ChebyshevKappaOneShape.lean` closes the last unknowns of the plan:

- `chebRightTwo_sub_chebLeftTwo_le` : the rectangle's width is `≤ 2/log T`;
- `chebRightTwo_sub_chebLeftTwo_pos`;
- `tsum_vonMangoldt_chebRightTwo_le` : `∑' Λ(n)n^{-d(T)} ≤ 8 log²T`, from the corpus's
  `tsum_vonMangoldt_rpow_neg_le` (`≤ 8/(d-1)²`) at `d-1 = 1/log T`.

The cutoff's mass needed nothing new: `norm_mellin_smoothWeight_one_le` already gives
`‖mellin w 1‖ ≤ N + H` (and `le_integral_smoothWeight` gives `N ≤ ∫ w`, so the mass is pinned
between `N` and `N+H`).

**Every input of the assembly now exists.**  What is left is purely the assembly: bound the five
terms plus the bracket correction at `T = chebHeightOne (N+H+1)` and `H = chebWidthOne N`, then
transfer to the sharp sum with `norm_tsum_vonMangoldt_smoothWeight_sub_sum_le`.

Follow the Möbius pattern exactly: abstract per-term lemmas as **top-level** declarations (the
200000-heartbeat limit is per-declaration), each proved by `mul_le_mul_of_nonneg_*` plus `linarith`,
never `nlinarith` on a degree-five product.

## Step 5 done: the five terms against a common shape

`RHTower/Sieve/ChebyshevKappaOneTerms.lean` — purely arithmetic, no zeta, no contour:

- `cheb_trunc_term_le` : `2(S·(W·Zd))/T ≤ 2(S·(W·(Z·E)))` — the height cancels the right line's
  growth, using `Zd ≤ Z·E·T`.
- `cheb_left_bracket_le` : `2(Yc/c) + 2(W·Zc) ≤ 4(Z·E) + 2(W·(Z·E))` — dividing by the left
  abscissa costs at most a factor two, since `c ≥ 1/2`.
- `cheb_horiz_pole_le` : the pole term, using `T ≥ 1`.
- `cheb_horiz_reg_le` : the regular term, using `Zd ≤ Z·E·T` and `T ≥ 1` again.

**Trap.**  `nlinarith` does **not** ring-normalise `T ^ (1 + 1)` when the exponent is an unreduced
natural-numeral sum: the hypothesis `0 ≤ W(ZE)T(T-1)` and the goal `W·Zd ≤ W(ZE)·T^(1+1)` were
treated as involving unrelated atoms.  Rewriting with `have hTT : T ^ (1 + 1) = T * T := by ring`
first makes it immediate.  The exponent shape `(1+1)` comes from the contour lemma's `j + 1` with
`j = 1`, so it appears throughout this chain.

**Also:** `div_le_div_of_nonneg_right` takes `0 ≤ c`, not `0 < c`, for the denominator.

## What is left

Only the concrete assembly: instantiate `exists_norm_tsum_vonMangoldt_kappa_one_general` at
`T = chebHeightOne (N+H+1)` and `H = chebWidthOne N`, feed the four term lemmas plus
`abs_bracket_kappa_one_le`, absorb `s²` with `sq_le_exp_div_gen`, and transfer to the sharp sum with
`norm_tsum_vonMangoldt_smoothWeight_sub_sum_le`.

## Step 6 done: the three edge powers against one exponential factor

`RHTower/Sieve/ChebyshevPowersAtHeight.lean`.  All three powers of the contour bound are bounded by
the single factor

```text
E = exp( -√(log(N+H+1)) / 160000 ),
```

the right line carrying an extra `T` that the truncation height cancels:

- `rpow_chebLeftTwo_at_shift` : `Y^{c(T)} ≤ Y·E`, with `T = chebHeightOne (Y+1)`.  The exponent
  `1/160000` is the *shifted* one: the height is chosen at `Y+1` while the left edge's trivial size
  is `Y`, and since `Y + 1 ≤ Y²` the saving `1/80000` merely halves.
- `rpow_chebLeftTwo_at_le`  : `Z^{c(T)} ≤ Z·E`.
- `rpow_chebRightTwo_at_le` : `Z^{d(T)} ≤ Z·E·T`.

The last two are weakenings of the *exact* identities of `ChebyshevRatePowersOne`; they are stated
against the same `E` so the four term lemmas of `ChebyshevKappaOneTerms` apply with a single
instantiation.

**Every hypothesis of every term lemma is now discharged.**  The assembly is the only step left.

## Note on concurrent builds

One umbrella build in this session failed inside
`GaloisForLFunctions/RHTower/DivisorReesGradedMetric.lean`, a module of another agent's concurrent
work that was being edited at that moment (file mtime three minutes before the build).  A retry
after they finished built clean.  When an umbrella build fails in a file this chain does not touch,
check the mtime before diagnosing.

## Correction to step 6: the shift must not halve the exponent

The first version of `ChebyshevPowersAtHeight.lean` bounded the shifted left-edge power by
`Y·exp(-√(log Z)/160000)`, obtained from `Z = Y+1 ≤ Y²` hence `log Y ≥ (log Z)/2`.  **That is too
lossy and would have broken the balance.**  The width's price is `exp(√(log N)/120000)` at
`α = 240000`, and

```text
-1/160000 + 1/120000 = +1/480000 > 0,
```

so the smoothing would have swamped the saving rather than the other way round.  The error only
shows up when the two exponents are compared, not in any individual lemma — each was true.

The fix keeps the full exponent.  `Y + 1 ≤ 2Y` gives `log Y ≥ log Z - log 2`, and the reciprocal
logarithm turns that difference into `(1/40000)(log 2)/(2√(log Z)) ≤ 1`, so the shift costs the
**constant** `e ≤ 3`, not half the exponent:

```
chebFactorOne Z = 3 · exp( -√(log Z) / 80000 )

rpow_chebLeftTwo_at_shift : 1 ≤ Y → 16 ≤ log(Y+1) → Y^{c(T)} ≤ Y · chebFactorOne (Y+1)
rpow_chebLeftTwo_at_le    : Z^{c(T)} ≤ Z · chebFactorOne Z
rpow_chebRightTwo_at_le   : Z^{d(T)} ≤ Z · chebFactorOne Z · T
```

With `1/80000` intact, `α = 240000` gives `-1/80000 + 1/120000 = -1/240000` and the plan of step 2
stands unchanged.  General lesson for this chain: a shift from `Y+1` to `Y` is a **constant**, never
a factor in the exponent — reach for `Y+1 ≤ 2Y`, not `Y+1 ≤ Y²`.

(The Möbius chain's `rpow_leftAbscissaTwo_le_shift` does halve its exponent, from `s/9` to `s/18`.
That was harmless there because the width price `exp(2(log N)^{1/6})` is of a strictly smaller
order than the saving `exp(-(log N)^{1/3}/18)`; here both are `exp(c√(log N))` and the constants
have to be compared.)

## Step 7 done: the balance, isolated as one inequality

`RHTower/Sieve/ChebyshevBalanceOne.lean`.  The whole choice of parameters exists to make one
inequality true, and it is now a theorem in its own right:

```
price_mul_factor_le : 0 < N → N ≤ Z →
  9·exp(√(log N)/120000) · chebFactorOne Z ≤ 27·exp(-√(log Z)/240000)
```

The left factor is the smoothing's squared price `(N/H + 2)² ≤ 9 exp(√(log N)/120000)` at
`chebRatioOne N = exp(√(log N)/240000)`; the right is the left edge's saving
`chebFactorOne Z = 3 exp(-√(log Z)/80000)`.  Since `N ≤ Z`, the exponents combine as
`1/120000 - 1/80000 = -1/240000`.  **The denominator `240000` of the smoothing ratio is exactly
what makes this hold**, and nothing else in the chain constrains it.

Also here:

- `one_div_chebHeightOne_le_factor` : `1/T ≤ chebFactorOne Z` — the truncation height is not a
  competitor, `1/T = exp(-2√(log Z))` being already below the saving.  This is what lets the
  `‖mellin w 1‖/T` term of the horizontal edges be absorbed into the common shape.
- `width_price_le` : the corpus's `sq_width_factor_le` composed with `sq_chebRatioOne_le`.
- `sqrt_log_le_sqrt_log`.

## What is left

Only the concrete assembly.  Every ingredient is a named theorem now:

| need | theorem |
|---|---|
| contour bound | `exists_norm_tsum_vonMangoldt_kappa_one_general` |
| five terms → common shape | `cheb_trunc_term_le`, `cheb_left_bracket_le`, `cheb_horiz_pole_le`, `cheb_horiz_reg_le` |
| three edge powers | `rpow_chebLeftTwo_at_shift`, `rpow_chebLeftTwo_at_le`, `rpow_chebRightTwo_at_le` |
| the balance | `price_mul_factor_le`, `one_div_chebHeightOne_le_factor`, `width_price_le` |
| series / width / mass | `tsum_vonMangoldt_chebRightTwo_le`, `chebRightTwo_sub_chebLeftTwo_le`, `norm_mellin_smoothWeight_one_le` |
| bracket | `abs_bracket_kappa_one_le` |
| polynomial absorption | `sq_le_exp_div_gen` |
| sharp transfer | `norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` |
| width facts | `one_le_chebWidthOne`, `chebWidthOne_le`, `div_chebWidthOne`, `chebWidthOne_eq` |

## Step 8 done: the five terms collapse to a single shape

`RHTower/Sieve/ChebyshevKappaOneShaped.lean`:

```
cheb_kappa_one_terms_shaped :
  2(S·(W·Zd))/T
    + (ci·(2(Yc/c) + 2(W·Zc)) + 2(wd·((W·Zd/T² + Mm)/T)))
    + (M·(2(Yc/c) + 2(W·Zc)) + 2(wd·(M·(W·Zd/T²))))
  ≤ ( 2SW + ci(4 + 2W) + 2·wd·(W+1) + M(4 + 2W) + 2·wd·M·W ) · (Z·E)
```

given `Zd ≤ Z·E·T`, `Zc ≤ Z·E`, `Yc ≤ Y·E`, `Mm ≤ Y`, `1/T ≤ E`, `1/2 ≤ c`, `Y ≤ Z`, `1 ≤ T` and
the obvious nonnegativities.  This is the whole right-hand side of
`norm_tsum_vonMangoldt_sub_full_main_le_explicit`, and after it **everything depending on the zeta
function has been discharged** — what remains is a polynomial in `log T` times `Z·E`.

The mass term `‖mellin w 1‖/T` joins the shape because `1/T` is itself below `E`
(`one_div_chebHeightOne_le_factor`): the truncation height decays faster than the left edge saves.
Without that the mass would sit outside the shape and the bound would stall at `Z/T`.

`0 ≤ Zd` has to be carried as its own hypothesis — `Zd ≤ Z·E·T` does not imply it, and at
instantiation it is just `Real.rpow_pos_of_pos`.

## Remaining

Instantiate: `S ≤ 8log²T`, `ci = 40000 log T`, `wd ≤ 2/log T`, `M = Cr log²T`,
`W ≤ Cm·9·exp(√(log N)/120000)`, then `price_mul_factor_le` turns `W·(Z·E)` into
`27·Cm·Z·exp(-√(log Z)/240000)`, `sq_le_exp_div_gen` absorbs the `log T` powers, and
`norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` transfers to the sharp sum.

## Step 9 done: the shape's coefficient

`RHTower/Sieve/ChebyshevKappaOneCoeff.lean`:

```
cheb_kappa_one_coeff_le :
  8 ≤ Λ → 0 ≤ W → W ≤ Wb → 0 ≤ Cr → S ≤ 8Λ² → ci = 40000Λ → 0 ≤ wd → wd ≤ 2/Λ → M = CrΛ² →
    2SW + ci(4 + 2W) + 2·wd·(W+1) + M(4 + 2W) + 2·wd·M·W  ≤  250000·(1+Cr)·(1+Wb)·Λ²
```

with `Λ = log T`.  The largest contribution is `ci·4 = 160000 log T`, which is where the constant
comes from; the reciprocal `wd ≤ 2/log T` is what stops the horizontal edges contributing a *third*
power of the logarithm.

Proved summand by summand — five `have`s bounding each against one of the four monomials
`Λ²`, `Λ²Wb`, `CrΛ²`, `CrΛ²Wb`, then one `nlinarith`.  Supplying the four monomials' nonnegativity
explicitly is what makes the final step go through.

## Remaining

`(2SW + …)·(Z·E) ≤ 250000(1+Cr)(1+Wb)·Λ²·Z·E`, then `price_mul_factor_le` collapses `Wb·E` to
`27·exp(-√(log Z)/240000)`, `sq_le_exp_div_gen` absorbs `Λ² = 4 log Z`, and
`norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` transfers to the sharp sum.

## A false alarm worth recording

A lint run reported `owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower:
GaloisForLFunctions.RHTower.DivisorReesBoundaryGraph`.  That is another agent's new module, not yet
registered; the next lint run passed once they added it.  **The umbrella does not import every
module directly** — over three hundred RHTower modules are reachable only transitively, so
"is `import …X` literally present in RHTower.lean" is not the right check.  Only the lint gate's
reachability computation is.

## Step 10 done: the collapse to a bare exponential

`RHTower/Sieve/ChebyshevCollapseOne.lean` — the two steps that take the shaped bound to its final
form:

```
one_add_width_mul_factor_le : 0 ≤ Cm → 0 < N → N ≤ Z →
  (1 + Cm·(9·exp(√(log N)/120000))) · chebFactorOne Z
    ≤ (3 + 27Cm) · exp(-√(log Z)/240000)

sq_mul_exp_neg_le : 0 ≤ s →
  s² · exp(-s/240000) ≤ 4·480000² · exp(-s/480000)

sq_log_chebHeightOne : 0 ≤ log Z → log²(chebHeightOne Z) = 4 log Z
```

The first splits the coefficient `1 + W`: the constant summand (from the pole term) keeps the full
`exp(-√(log Z)/80000)`, and the price summand is exactly what `price_mul_factor_le` handles.

The second absorbs the polynomial `log²T = 4 log Z = 4(√(log Z))²` at the cost of **one last
halving** of the exponent — this is where `1/240000` becomes `1/480000`, and it is the final
halving in the chain.

## The chain, complete except for one instantiation

Every step from the zero-free region to a bare `Z·exp(-√(log Z)/480000)` is now a named,
unconditional theorem.  What is left is mechanical substitution: apply
`exists_norm_tsum_vonMangoldt_kappa_one_general` at `T = chebHeightOne (N+H+1)`,
`H = chebWidthOne N`, chain `cheb_kappa_one_terms_shaped` → `cheb_kappa_one_coeff_le` →
`one_add_width_mul_factor_le` → `sq_mul_exp_neg_le`, and transfer to the sharp sum with
`norm_tsum_vonMangoldt_smoothWeight_sub_sum_le`.

Target: `|ψ(N) - N| ≪ N·exp(-√(log N)/480000)`, beating `PNTPlus.MediumPNT`'s
`exp(-c(log x)^{1/10})`.

## Steps 11–12 done: final collapse and thresholds

`RHTower/Sieve/ChebyshevFinalCollapse.lean`:

```
cheb_final_collapse : 0 ≤ Cr → 0 ≤ Cm → 0 ≤ Z → 0 ≤ s → log Z = s² →
  (1 + Wb)·E ≤ (3 + 27Cm)·exp(-s/240000) →
  250000(1+Cr)(1+Wb)·(4 log Z)·(Z·E)
    ≤ 250000(1+Cr)(3+27Cm)·(4·(4·480000²))·Z·exp(-s/480000)
```

The order matters: the coefficient `(1+Wb)·E` is replaced **first** — that is where the smoothing's
price meets the left edge's saving — and only then is the polynomial `s²` absorbed.  Doing it the
other way round loses the balance.

`RHTower/Sieve/ChebyshevKappaOneThreshold.lean`:

```
eventually_cheb_kappa_one_conditions (L₀) : ∀ᶠ N in atTop,
  0 < N ∧ 1 ≤ chebWidthOne N ∧ chebWidthOne N ≤ N
    ∧ 16 ≤ log(N + chebWidthOne N + 1)
    ∧ L₀ ≤ log (chebHeightOne (N + chebWidthOne N + 1))
```

All four side conditions of the chain in one package, so the capstone's proof carries no filter
plumbing.  The last is the only one that sees the contour's own threshold `L₀`: since
`log T = 2√(log Z)`, it asks only that `log N` reach `(L₀/2)²`.

## The capstone

Everything is now in place.  The remaining proof is:

1. `obtain ⟨Cm, Cr, L₀, …, hmain⟩ := exists_norm_tsum_vonMangoldt_kappa_one_general`
2. `filter_upwards [eventually_cheb_kappa_one_conditions L₀]`
3. `hbase := hmain N (chebWidthOne N) … (chebHeightOne (N + chebWidthOne N + 1)) …`
4. `cheb_kappa_one_terms_shaped` with `E := chebFactorOne (N + chebWidthOne N + 1)`, its three
   power hypotheses from `ChebyshevPowersAtHeight`, `Mm ≤ Y` from `norm_mellin_smoothWeight_one_le`,
   `1/T ≤ E` from `one_div_chebHeightOne_le_factor`, `1/2 ≤ c` from `half_le_chebLeftTwo`
5. `cheb_kappa_one_coeff_le` with `Λ := log T`, `Wb := Cm·(9·exp(√(log N)/120000))` (via
   `width_price_le`), `S ≤ 8Λ²` from `tsum_vonMangoldt_chebRightTwo_le`, `ci = 40000Λ` from
   `one_sub_chebLeftTwo_inv`, `wd ≤ 2/Λ` from `chebRightTwo_sub_chebLeftTwo_le`
6. `sq_log_chebHeightOne` to turn `Λ²` into `4 log Z`, then `cheb_final_collapse` with
   `one_add_width_mul_factor_le`
7. the bracket correction `abs_bracket_kappa_one_le`, and
   `norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` for the sharp sum.

## CAPSTONE PROVED: the smoothed Chebyshev sum at exponent `1/2`

```
RHTower.Sieve.exists_norm_tsum_vonMangoldt_kappa_one_rate :
  ∃ B ≥ 0, ∀ᶠ N in atTop,
    ‖ 2π ∑' Λ(n)·w(n) - (mellin w 1)·(2 arctan(T/(d-1)) - 2 arctan(T/(c-1))) ‖
      ≤ B · (N + H + 1) · exp( -√(log(N+H+1)) / 480000 )
```

with `H = chebWidthOne N`, `T = chebHeightOne (N+H+1)`, and
`B = 250000(1+Cr)(3+27Cm)·(4·(4·480000²))` explicit in the two analytic constants.
Unconditional: `[propext, Classical.choice, Quot.sound]`.

### Two build traps

- **`Λ` is `ArithmeticFunction.vonMangoldt` notation.**  With `open ArithmeticFunction`, a named
  argument `(Λ := …)` fails to parse (`unexpected token ':='`).  The binder in
  `cheb_kappa_one_coeff_le` had to be renamed `Λ → Lg`.
- **`rw` must be applied to *every* hypothesis that shares an atom.**  Rewriting
  `log²T = 4 log Z` in `hstep` alone left `hbase` and `hshaped` carrying `Real.log(chebHeightOne Z)^2`,
  which `linarith` treats as an atom unrelated to `4·Real.log Z`.  `rw [hlogsq] at hbase hshaped hstep`
  fixes it.  The final step is then a single `linarith` over four hypotheses.

### Remaining for the full PNT-with-error-term

Only the passage from the smoothed sum to `ψ(N)`:

1. the main term `(mellin w 1)·(bracket)` → `2π·(N + O(H))`, using `abs_bracket_kappa_one_le`
   (error `≤ 3/(T log T)`), `le_integral_smoothWeight` and `integral_smoothWeight_le`
   (mass between `N` and `N+H`);
2. `norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` for the sharp sum, costing `(H+1)·log(N+H)`,
   which at `H = N·exp(-√(log N)/240000)` is `N·log N·exp(-√(log N)/240000)` — the same order as
   the contour term after `sq_le_exp_div_gen`.

Expected: `|ψ(N) - N| ≪ N·exp(-√(log N)/480000)`, against `PNTPlus.MediumPNT`'s
`exp(-c(log x)^{1/10})`.

## Step 13: the main term's bracket costs nothing

`RHTower/Sieve/ChebyshevMainTermErrorOne.lean`:

```
cheb_main_term_error_le : 0 < N → 0 < H → 16 ≤ log(N+H+1) →
  ‖mellin w 1‖ · |bracket - 2π| ≤ 2·((N+H+1)·exp(-√(log(N+H+1))/480000))
```

The discrepancy is the rectangle's aspect ratio `2(d-c)/T ≤ (1/2)·(1/T)`, and
`1/T = exp(-2√(log Z))` is far below the saving `exp(-√(log Z)/480000)` — the truncation height
decays like `exp(-2s)` while the saving only needs `exp(-s/480000)`, a factor of nearly a million
in the exponent.  So replacing the bracket by `2π` costs strictly less than the contour bound
itself.

Combined with the capstone this gives, at the same rate,

```
‖ 2π ∑' Λ(n)w(n) - 2π·(mass of w) ‖ ≤ (B + 2)·(N+H+1)·exp(-√(log(N+H+1))/480000),
```

i.e. `∑' Λ(n)w(n) = (mass of w) + O(Z·exp(-√(log Z)/480000))`, and the mass lies in `[N, N+H]`
(`le_integral_smoothWeight`, `integral_smoothWeight_le`).

## Last step

`norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` transfers to `ψ(N) = ∑_{n ≤ N} Λ(n)`, costing
`(H+1)·log(N+H)`.  At `H = N·exp(-√(log N)/240000)` that is `N·log N·exp(-√(log N)/240000)`, the
same order as the contour term once `sq_le_exp_div_gen` absorbs the logarithm.

## Step 14 done: the sharp transfer's cost

`RHTower/Sieve/ChebyshevSharpTransferOne.lean`:

```
sqrt_log_shift_le        : 3 ≤ N → 0 ≤ log N → chebWidthOne N ≤ N →
                             √(log(N + chebWidthOne N + 1)) ≤ 2√(log N)
cheb_sharp_transfer_cost_le : 3 ≤ N → 16 ≤ log N →
  (chebWidthOne N + 1)·log(N + chebWidthOne N)
    ≤ 2·( √(log Z)² · (Z · exp(-√(log Z)/480000)) )
```

The window's own saving is `exp(-√(log N)/240000)`, and the shift from `N` to `Z = N+H+1` at most
doubles the square root (`Z ≤ N²` gives `log Z ≤ 2 log N`), so it survives as
`exp(-√(log Z)/480000)` — exactly the contour's rate.  The factor `√(log Z)² = log Z` is the
polynomial, to be absorbed with `sq_le_exp_div_gen` at the end.

### The trap that cost two build cycles

`rw [chebWidthOne_eq]` rewrites `chebWidthOne N` **everywhere in the goal**, including inside
`N + chebWidthOne N + 1` — the very term the bound is stated against.  The same self-reference bites
`rw [hsq]` with `hsq : log Z = √(log Z)²`, since `√(log Z)` contains `log Z`.  In both cases the fix
is to keep the equation as a hypothesis and let `linarith`/`nlinarith` use it as a relation between
atoms, never to rewrite with it.

## All fourteen steps are proved

What remains is one more assembly: add `cheb_main_term_error_le` and `cheb_sharp_transfer_cost_le`
to `exists_norm_tsum_vonMangoldt_kappa_one_rate`, absorb the last `√(log Z)²` with
`sq_le_exp_div_gen` at `k = 960000`, and state the result for `ψ(N)`:

```text
|ψ(N) - (mass of w)| ≪ N · exp( -√(log N) / 960000 ).
```

## Step 15: the scalar and the bracket come off

`RHTower/Sieve/ChebyshevSharpRateOne.lean`:

```
norm_sub_le_of_scaled : 1 ≤ r → ‖(r:ℂ)·A - M·br‖ ≤ K₁ → ‖M·br - M·(r:ℂ)‖ ≤ K₂ → ‖A - M‖ ≤ K₁ + K₂
norm_mul_sub_mul_ofReal : ‖M·(a:ℂ) - M·(b:ℂ)‖ = ‖M‖·|a - b|
```

The contour bound controls `‖r·A - M·br‖` with `r = 2π` the scalar Perron carries, `A` the smoothed
sum, `M` the mass and `br` the bracket.  A Chebyshev estimate wants `‖A - M‖`.  Since `r ≥ 1` the
scalar only helps (`‖A - M‖ ≤ r‖A - M‖ = ‖r·A - M·r‖`), and the bracket comes off by one triangle
inequality.  Both steps are free of analytic input, so isolating them keeps the final assembly
purely numeric.

### A discarded draft

A first attempt at the whole assembly was written with two `sorry`s standing in for these two
steps.  **It was deleted rather than committed** — the rule is no `sorry` in the tree, ever — and
replaced by the two lemmas above, which are what the `sorry`s were hiding.  The remaining work is
now genuinely numeric.

## The last assembly

```
‖ψ(N) - (mass)‖ ≤ ‖(2π)·Σ' - M·br‖ + ‖M·br - M·(2π)‖ + 2π‖Σ' - ψ(N)‖
```

- first term: `exists_norm_tsum_vonMangoldt_kappa_one_rate` (`≤ B₁·Z·exp(-√(log Z)/480000)`);
- second: `cheb_main_term_error_le` via `norm_mul_sub_mul_ofReal` (`≤ 2·Z·exp(-√(log Z)/480000)`);
- third: `norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` with `cheb_sharp_transfer_cost_le`
  (`≤ 2·log Z·Z·exp(-√(log Z)/480000)`).

Then `sq_le_exp_div_gen` at `k = 960000` absorbs the `log Z`, `Z ≤ 3N`, and
`√(log Z) ≥ √(log N)` turns the rate into `N·exp(-√(log N)/960000)`.

## CAPSTONE 2 PROVED: the sharp Chebyshev sum against the cutoff's mass

```
RHTower.Sieve.exists_norm_sum_vonMangoldt_sub_mass_kappa_one_rate :
  ∃ B ≥ 0, ∀ᶠ N in atTop,
    ‖ ∑_{n ≤ ⌊N⌋} Λ(n) - (mass of the cutoff) ‖
      ≤ B · Z · exp( -√(log Z) / 960000 ),        Z = N + chebWidthOne N + 1
```

with `B = (B₁ + 2) + 8·960000²` explicit in the smoothed rate's constant.  Unconditional:
`[propext, Classical.choice, Quot.sound]`.  `formal lint passed`.

The three contributions, all of the same order:

| piece | source | size |
|---|---|---|
| contour | `exists_norm_tsum_vonMangoldt_kappa_one_rate` | `B₁·Z·exp(-√(log Z)/480000)` |
| bracket | `cheb_main_term_error_le` + `norm_mul_sub_mul_ofReal` | `2·Z·exp(-√(log Z)/480000)` |
| sharp transfer | `norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` + `cheb_sharp_transfer_cost_le` | `2·log Z·Z·exp(-√(log Z)/480000)` |

`sq_mul_exp_neg_le'` absorbs the `log Z`, halving the exponent one final time to `1/960000`.

### Build note

`lake env lean` type-checks a file but does **not** write its `.olean`.  After editing
`ChebyshevSharpRateOne.lean` and checking it that way, the new module importing it failed with
`unknown identifier sq_mul_exp_neg_le'` — the dependency had to be `lake build`-ed first.  This is
the reason the project rule says `lake env lean` for iteration and `lake build` for the audit: a
downstream file needs the olean, not just a successful check.

## Remaining (cosmetic)

`|mass - N| ≤ H` (`le_integral_smoothWeight`, `integral_smoothWeight_le`) and `H ≤ Z·exp(...)`
turn the mass into `N`; `Z ≤ 3N` and `√(log Z) ≥ √(log N)` restate the rate in terms of `N`:

```text
|ψ(⌊N⌋) - N| ≪ N · exp( -√(log N) / 960000 ),
```
against the vendored `PNTPlus.MediumPNT`'s `exp(-c(log x)^{1/10})`.

## CHAIN COMPLETE: the Chebyshev estimate at exponent `1/2`

```
RHTower.Sieve.exists_norm_sum_vonMangoldt_sub_self_kappa_one_rate :
  ∃ B ≥ 0, ∀ᶠ N in atTop,
    ‖ ∑_{n ≤ ⌊N⌋} Λ(n) - N ‖ ≤ B · Z · exp( -√(log Z) / 960000 ),   Z = N + chebWidthOne N + 1
```

Unconditional: `[propext, Classical.choice, Quot.sound]`.  Umbrella builds clean;
`formal lint passed`.

The last step is `RHTower/Sieve/ChebyshevSharpSelfRateOne.lean`:

- `chebWidthOne_le_shape` — the smoothing window is itself below the contour's shape, so replacing
  the cutoff's mass by `N` costs nothing new;
- `norm_mellin_one_sub_ofReal_le` — the mass lies in `[N, N+H]`
  (`le_integral_smoothWeight`, `integral_smoothWeight_le`), so `‖mass - N‖ ≤ H`;
- the capstone, by one triangle inequality against
  `exists_norm_sum_vonMangoldt_sub_mass_kappa_one_rate`.

### The whole ladder (17 modules, all unconditional)

| layer | module |
|---|---|
| `ζ'/ζ` on the full region width | `ZetaLogDerivRegUniform` |
| contour data, contour bound | `ChebyshevKappaOneData`, `ChebyshevKappaOneContour` |
| height, edge powers | `ChebyshevHeightOne`, `ChebyshevRatePowersOne`, `ChebyshevPowersAtHeight` |
| width, absorption | `ChebyshevWidthOne` |
| bracket | `ChebyshevBracketBound` |
| shape data, term reductions | `ChebyshevKappaOneShape`, `ChebyshevKappaOneTerms` |
| balance | `ChebyshevBalanceOne` |
| five→shape, coefficient, collapse | `ChebyshevKappaOneShaped`, `ChebyshevKappaOneCoeff`, `ChebyshevCollapseOne`, `ChebyshevFinalCollapse` |
| thresholds, smoothed capstone | `ChebyshevKappaOneThreshold`, `ChebyshevKappaOneRate` |
| main term, transfer, sharp capstones | `ChebyshevMainTermErrorOne`, `ChebyshevSharpTransferOne`, `ChebyshevSharpRateOne`, `ChebyshevSharpMassRateOne`, `ChebyshevSharpSelfRateOne` |

### Comparison

- vendored `PNTPlus.MediumPNT`: `ψ - id =O[atTop] x·exp(-c(log x)^{1/10})`;
- corpus's own `Chebyshev*` chain: only the qualitative `ψ(N)/N → 1`;
- this chain: `exp(-√(log N)/960000)` — the classical de la Vallée Poussin exponent `1/2`.

### Where the exponent's five halvings happen

`1/40000` (region width) → `1/80000` (left edge) → `1/240000` (balance against the smoothing's
squared price) → `1/480000` (absorbing `log²T`) → `1/960000` (absorbing the transfer's `log Z`).
The `Y+1 → Y` shift costs a **constant**, never a halving.

## The estimate in its usual form

```
RHTower.Sieve.exists_norm_sum_vonMangoldt_sub_self_kappa_one_rate_self :
  ∃ B ≥ 0, ∀ᶠ N in atTop,  ‖ ∑_{n ≤ ⌊N⌋} Λ(n) - N ‖ ≤ B · N · exp( -√(log N) / 960000 )
```

The shifted cutoff `Z = N + chebWidthOne N + 1` is at most `3N` and its logarithm is the larger
one, so the `Z`-form collapses to this in two lines.  This is the statement directly comparable to
the vendored `PNTPlus.MediumPNT` (`ψ - id =O[atTop] x·exp(-c(log x)^{1/10})`).

Unconditional; umbrella clean; `formal lint passed`.

## Card status

Moved to `3-formalized` together with `moebius-exponent-upgrade.md`: both chains are complete in
Lean, at exponents `1/2` (ψ) and `1/3` (μ) respectively.

## Literature sweep (expanded keywords)

Earlier iterations covered: zero-free, Möbius, Bockstein, Deninger, Stokes, descent, Hochschild,
Connes, Selberg, Vinogradov, Hilbert–Pólya, adelic, arctan/formalization, Mertens, explicit
formula, Euler characteristic, Lean formalization.  This iteration added **prismatic**,
**Beurling–Nyman**, **Kloosterman**, **Iwasawa**.  Nothing adoptable:

- prismatic ([2312.13129](https://arxiv.org/abs/2312.13129), [2310.12770](https://arxiv.org/abs/2310.12770)) — p-adic cohomology, no contact with the zero-free-region route;
- Beurling–Nyman — no 2025/26 preprints surfaced; the classical criterion is a reformulation of RH,
  and the corpus's `rh-criterion-reencoding-template` already classifies that family;
- Kloosterman ([2511.08445](https://arxiv.org/html/2511.08445)) — bilinear forms with composite
  moduli; relevant to sieve/Type-II sums, not to the contour;
- Iwasawa ([2603.22483](https://arxiv.org/html/2603.22483v1), [2603.11615](https://arxiv.org/html/2603.11615v1)) — main conjectures for modular forms and function-field elliptic curves.

**Keywords still unused**, for the next sweeps: perfectoid, motivic, condensed, Frobenius, Weyl,
trace formula, large sieve, exponential sums, random matrix, ergodic, entropy, positivity,
de Branges, Berkovich, operad, moduli, Langlands, Eisenstein, theta, crystalline.

## The real-valued statement

```
RHTower.Sieve.exists_abs_sum_vonMangoldt_sub_self_kappa_one_rate :
  ∃ B ≥ 0, ∀ᶠ N in atTop,  |ψ(⌊N⌋) - N| ≤ B · N · exp( -√(log N) / 960000 )
```

with `ψ(⌊N⌋) = ∑_{n ∈ range (⌊N⌋₊ + 1)} Λ(n)` — the same shape the corpus's
`tendsto_sum_vonMangoldt_div` uses, which this refines from a limit to a rate.  One `push_cast`
away from the complex form.

## Sweep, continued

Added keywords **de Branges**, **large sieve**.  Nothing adoptable:

- de Branges — recent work is on vector-valued and Cauchy–de Branges generalisations
  ([2206.02175](https://arxiv.org/abs/2206.02175), [2406.15194](https://arxiv.org/abs/2406.15194));
  the corpus's Suzuki layer already sits on the scalar theory and its ceiling is recorded in
  `suzuki-carrier-model-too-weak-for-rigidity`;
- large sieve — [2605.29470](https://arxiv.org/abs/2605.29470) (Ramaré, May 2026) improves the
  **weighted** large sieve via Parseval.  The corpus's own large sieve is already at the sharp
  `N + δ⁻¹` (`sieve-layer-sharp-2026-08`), so a weighted refinement is orthogonal to the Route E
  bottleneck; noted, not adopted.

Remaining unused keywords: perfectoid, motivic, condensed, Frobenius, Weyl, trace formula,
exponential sums, random matrix, ergodic, entropy, positivity, Berkovich, operad, moduli,
Langlands, Eisenstein, theta, crystalline.

## Downstream: θ and π inherit the exponent

The width-`1/log` contour's conclusion is stated for `ψ`.  Both classical companions now carry the
same error term, unconditionally.

**θ** — `RHTower/Sieve/ChebyshevThetaBigO.lean`:

```
RHTower.Sieve.chebyshevTheta_sub_id_isBigO :
  ∃ c > 0,  (Chebyshev.theta - id)  =O[atTop]  fun x => x · exp( -c · √(log x) )
```

The corpus already owned `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log : |ψ x - θ x| ≤ 2√x·log x`.
What had to be proved is that this correction sits below the contour's own error
(`sqrt_mul_log_le_shape`): writing `L = log x`, `2L·exp(c√L) ≤ √x` splits as `2L ≤ x^{1/4}` (from
`isLittleO_log_rpow_atTop`, which lives at the **root**, not under `Real`) and
`exp(c√L) ≤ exp(L/4) = x^{1/4}` (valid once `L ≥ 16c²`).

**π** — `RHTower/Sieve/PrimeCountingBigO.lean`:

```
RHTower.Sieve.primeCounting_sub_logIntegral_isBigO :
  ∃ c > 0,  (fun x => π(⌊x⌋) - ∫_{[2,x]} dt/log t)
              =O[atTop]  fun x => x · exp( -c · √(log x) )
```

This refines PNTPlus's `pi_asymp` / `pi_alt` / `pi_alt'`, all of which are qualitative
(`c =o[atTop] 1`), to a rate against the logarithmic integral.

Two PNTPlus assets carried the whole passage and must not be rebuilt:

- `pi_asymp_aux : π(⌊x⌋) = θ(x)/log x + ∫_{[2,x]} θ(t)·(t log²t)⁻¹` — the partial summation;
- `integral_log_inv'' : 2/log 2 + ∫_{[2,x]} (log t)⁻¹ = x/log x + ∫_{[2,x]} (log t)⁻²` — the main
  term reassembling into the logarithmic integral.

`chebyshev_asymptotic''` supplies `f` with `θ(x) = x(1 + f(x))` **together with its integrability
on every `[2,x]`**, which is what makes the integral split legitimate; deriving integrability of a
`θ`-based integrand from scratch would have been the expensive part.

## The reusable brick

`RHTower/Sieve/SqrtLogDecayIntegral.lean` is stated for an arbitrary integrand, so any later
`exp(−c√(log t))`-weighted integral can use it:

```
RHTower.Sieve.exists_bound_setIntegral_sqrt_log_decay :
  0 < c → 0 ≤ K →
  (∀ x ≥ 2, IntegrableOn g [2,x]) →
  (∀ᶠ t, |g t| ≤ K·exp(-c√(log t))) →
  ∃ C ≥ 0, ∀ᶠ x,  |∫_{[2,x]} g|  ≤  C · x · exp( -(c/2)·√(log x) )
```

**The halving is intrinsic.**  Split at `√x`: below it the weight is only bounded by `1` and the
interval is `√x` long; above it the weight is at most `exp(−c√(log √x)) = exp(−(c/√2)√(log x))`.
No pure-power majorant `exp(−c'√(log x))·(t/x)^α` can avoid the split — at `t ≈ 2` the left side is
`≈ 1` while the majorant is `≈ 0`, so it fails at the bottom for every `α`.  The bottom's true
contribution is only `√x`, which is why the split is cheap but unavoidable.

Also proved there: `sqrt_log_sqrt_le` (`√(log x)/2 ≤ √(log t)` for `t ≥ √x` — the `√2` at the split
point is spent down to `2`, which keeps the arithmetic rational).
