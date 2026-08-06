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
