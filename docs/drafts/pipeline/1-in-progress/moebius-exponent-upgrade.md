# Upgrading the Möbius contour exponent from 1/10 to 1/3

Status: in progress (opened 2026-08-06)
Depends on: `docs/drafts/pipeline/3-formalized/zero-free-region-exponent-one.md` (complete)

## The finding

The corpus's Möbius twist chain produces a saving

```
exp(-zeroFreeConst * (log x)^(1/10) / 8192)
```

(`RHTower/Sieve/MoebiusTwistMajorantRatio.lean`). **The exponent `1/10` is not intrinsic — it is
`1/(κ+1)` with `κ = 9`**, inherited from the only zero-free region the chain had when it was built.
The κ dependence is *localised* in four definitions in
`RHTower/Sieve/MoebiusContourBound.lean`:

```lean
leftAbscissa  K = 1 - zeroFreeConst / (16 * (Real.log K) ^ 9)
rightAbscissa K = 1 + zeroFreeConst / (2  * (Real.log K) ^ 9)
invZetaEdgeBound  K = …            -- the `1/ζ` bound on the contour
invZetaRightBound K = exp(22/4) * (1 + 1 / (zeroFreeConst / (2 * (Real.log K) ^ 9)))
```

and in the lemmas of `RHTower/Sieve/MoebiusContourBoundSharp.lean` that discharge
`‖invZeta (x + it)‖ ≤ invZetaEdgeBound K` on the contour.

## The arithmetic, and why the gain is 1/3 and not 1/2

Balancing the contour saving `x^{-δ(K)}` against the truncation error `1/K`:

| region width `δ(K)` | `1/ζ` bound | balance | exponent |
|---|---|---|---|
| `c/log⁹K` (current) | `log⁷K` | `log K = (log x)^{1/10}` | `1/10` |
| `1/log²K` (`exists_zeta_lower_strip`) | `C log²K` | `log K = (c log x)^{1/3}` | **`1/3`** |
| `c/log K` (the κ=1 region) | — | — | would be `1/2` |

**The binding constraint is the `1/ζ` strip, not the zero-free region.** The corpus now owns a
zero-free region of width `1/(10000 log|γ|)`, but `1/ζ` is only controlled on width `log^{-2}|γ|`
(`exists_zeta_lower_strip`), and the contour needs a `1/ζ` bound on its left abscissa, not merely
nonvanishing. So `κ_eff = 2` and the exponent is `1/3`. Getting `1/2` needs `1/ζ` control on the
full κ=1 region, which `mem:route_e/inv_zeta_width_ceiling_2026_08_06` shows this method does not
give.

## Upgrade path

1. Redefine `leftAbscissa K = 1 - 1 / (Real.log K) ^ 2`, `rightAbscissa K = 1 + 1 / (Real.log K) ^ 2`,
   and set `invZetaEdgeBound K`, `invZetaRightBound K` to the corresponding `C log²K`.
2. Re-prove the four `‖invZeta …‖ ≤ …` lemmas in `MoebiusContourBoundSharp.lean` from
   `exists_zeta_lower_strip` in place of the κ=9 estimate. Note its threshold is astronomical
   (`≈ exp(50000)`), so the statements acquire a large-`K` side condition — check whether the chain
   already carries one (`K₀ ≤ K` appears in `exists_norm_tsum_moebiusTwist_smoothWeight_le_general`,
   which is promising).
3. Propagate through `MoebiusTwistContourBoundGeneral`, `CoeffMajorant`, `MoebiusTwistSaving`,
   `MoebiusTwistMajorantRatio`; the exponent `1/10` becomes `1/3` and `log⁹` becomes `log²`
   throughout.

**Risk to manage:** this edits a working multi-module chain written by earlier sessions. Do it by
adding the new definitions alongside the old ones and building a parallel capstone first, not by
mutating the existing defs — the κ=9 chain should keep compiling until the κ=2 one is proved.

## Log

- 2026-08-06 -- opened; κ dependence located and the exponent arithmetic checked.

## Step 1–2 done: the κ=2 contour is proved, in parallel with the κ=9 one

Nothing in `MoebiusContourBound.lean` / `MoebiusContourBoundSharp.lean` was touched.  The general
rectangle lemma `norm_tsum_moebius_smoothWeight_le_sharp` (`PerronSharpSubstitution.lean`) is fully
parametric in `(c, d, T, Md, Mh, Mc)`, so the upgrade is a *second instantiation*, not a rewrite.

New modules (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`; `lint` passes):

1. `RHTower/Sieve/InvZetaStripBound.lean`
   - `strip_pt_ne_one` — a point off the real axis is not the pole.
   - `exists_norm_invZeta_strip_le` : `‖invZeta(x+it)‖ ≤ C log²|t|` on `|x-1| ≤ log^{-2}|t|`.
     Pure inversion of `exists_zeta_lower_strip` through `norm_invZeta_eq`.
   - `exists_norm_invZeta_contour_le` — same with the strip pinned to a parameter `K ≥ |t|`.
     Both hypotheses transport in the right direction: `1/log²K ≤ 1/log²|t|` widens the strip and
     `C log²|t| ≤ C log²K` weakens the bound.

2. `RHTower/Sieve/InvZetaUniformStrip.lean`
   - `exists_bound_invZeta_box` — `exists_bound_invZeta_low_box` generalised from height `1` to an
     arbitrary height `T`.  `exists_zero_free_rect` was already general in `T`; only the hard-coded
     `1` had to go.
   - `exists_norm_invZeta_uniform_strip` : **no height restriction.**
     `L₀ ≤ log K → |t| ≤ K → |x-1| ≤ log^{-2}K → ‖invZeta(x+it)‖ ≤ C log²K`.
     Large heights from the region branch, small heights from the compact box; the box constant is
     absorbed because `log K ≥ 1` forces `log²K ≥ 1`.  Fit condition: `log K ≥ 1/δ` — no square
     root needed, since `log²K ≥ log K`.

3. `RHTower/Sieve/ZetaUniformStripZeroFree.lean`
   - `exists_zeta_uniform_strip_zero_free` — the same two-branch fit for zero-freeness, stated for
     `s : ℂ` so a rectangle membership feeds it directly.

4. `RHTower/Sieve/MoebiusContourKappaTwo.lean`
   - `leftAbscissaTwo K = 1 - 1/log²K`, `rightAbscissaTwo K = 1 + 1/log²K`,
     `invZetaRightBoundTwo K = e^{22/4}(1 + log²K)` (the Euler-product bound at `d-1 = log^{-2}K`).
   - `exists_norm_tsum_moebius_smoothWeight_le_kappa_two` — the four-edge estimate at that
     rectangle, with `truncHeight K = (K-3)/2` unchanged and every `1/ζ` bound `= Ms·log²K`.

**What moved.**  The left abscissa went from `1 - c₉/(16 log⁹K)` to `1 - 1/log²K`; the price is
that the edge constants went from `O(log^{c})` to `O(log²K)`, which is negligible against the
`(N+H)^{leftAbscissa}` factor.  The saving exponent is therefore `1/3` in place of `1/10`.

**Step 3 (next).**  The consumer that optimises over `K` — the module producing
`exp(-c (log x)^{1/10})` — must be re-run at the new abscissa.  Locate it and instantiate the κ=2
capstone there; the balance is now `log²K` against `(N+H)^{-1/log²K}`, i.e. `log K ≍ (log x)^{1/3}`.

## Step 3 done: the saving is exposed at the new width

`RHTower/Sieve/MoebiusSavingKappaTwo.lean`:

- `rpow_leftAbscissaTwo` : `x^{c(K)} = x · exp(-log x / log²K)` for `c(K) = 1 - log^{-2}K`.
- `rightAbscissaTwo_sub_leftAbscissaTwo` : the rectangle width is *exactly* `2/log²K`.
- `exists_norm_tsum_moebius_smoothWeight_le_saving_two` — the κ=2 contour bound with the left-edge
  term written as `N+H` times `exp(-log(N+H)/log²K)`.

Both chains now terminate at the same place: `exists_norm_tsum_moebius_smoothWeight_le_saving`
(κ=9, denominator `16 log⁹K`) and `..._le_saving_two` (κ=2, denominator `log²K`).  Nothing
downstream consumes either yet, so the κ=2 branch is at full parity, with the better exponent
visible in the statement.

## Where the exponent now stops

Balancing `log²K` against `exp(-log(N+H)/log²K)` gives `log K ≍ (log x)^{1/3}` and the saving
`exp(-c(log x)^{1/3})`.  Going further needs a strip of width `log^{-1-ε}`, hence
`ζ'/ζ ≪ log^{1+ε}` on it — which the Landau/Borel–Carathéodory route cannot give (recorded ceiling).
A Vinogradov–Korobov region would license width `log^{-2/3-ε}` and the classical `3/5`, but that is
a separate programme (Vinogradov's mean value theorem is not in the corpus or mathlib).

## Literature check (arXiv sweep, this iteration)

- `arXiv:2603.21490`, *Zero-free regions inspired by work of Heath-Brown* (Mar 2026):
  `ζ(σ+it) ≠ 0` for `t ≥ 3`, `σ ≥ 1 - 1/(4.896 log t)`.  Same **shape** as our
  `exists_zero_free_region_explicit` (`1/10000`, past a large threshold) — a constant improvement
  only.  It does not move the Möbius exponent, which depends on the *power* of `log`, not the
  constant.  Do not spend effort chasing the constant.
- `arXiv:2508.15971` — Deninger foliated systems ↔ Connes–Consani adelic spaces.  Abstract only;
  no extractable unconditional statement visible without the full text.  Flagged, not adopted.
- Nothing found that supplies a Vinogradov–Korobov input in a formalisable form.

## Step 4: the exponent-`1/3` rate for the smoothed Möbius sum

The κ=9 chain's `exists_norm_tsum_moebius_smoothWeight_le_saving` had no consumer.  The κ=2 chain
now runs all the way to a rate, because the general rectangle lemma made every layer a fresh
instantiation rather than a rewrite.  Six new modules:

1. `RHTower/Sieve/MoebiusContourParamTwo.lean` — the balanced parameter
   `contourParamTwo x = ⌈exp(2(log x)^{1/3})⌉₊`, with `2(log x)^{1/3} ≤ log K ≤ 2(log x)^{1/3}+1`.
   - `le_saving_exponent_two` : `(log x)^{1/3}/9 ≤ (1/log²K)·log x` — the left edge's saving.
   - `exp_saving_right_two` : `exp((1/log²K)·log x) ≤ exp(-(7/4)(log x)^{1/3})·K` — the truncation
     height beats the right line's growth.

   **The factor `2` in the exponent is not cosmetic.**  At `log K = (log x)^{1/3}` exactly, the
   left-edge saving `exp(-log x/log²K)` and the right-line growth `x^{1/log²K}/K` cancel and
   nothing at all is saved.  Doubling separates them: the left keeps `1/9`, the right gets `7/4`.

2. `RHTower/Sieve/MoebiusContourKappaTwoGeneral.lean` — the κ=2 contour bound with cutoff-uniform
   constants, from `exists_bound_mellin_smoothWeight_uniform_upto` (horizontal edges at `j = 0`).
3. `RHTower/Sieve/MoebiusContourKappaTwoRatio.lean` — the same in terms of `L = N/H`, via the
   existing `sq_width_factor_le` / `width_factor_le`; the proof is `gcongr`.
4. `RHTower/Sieve/MoebiusRatePowers.lean` — the three edge powers at the balanced parameter.
   The shifted one is needed because the parameter is chosen at `Y+1` while the left edge's trivial
   size is `Y`; since `Y+1 ≤ Y²` the saving merely halves.
5. `RHTower/Sieve/MoebiusKappaTwoTerms.lean` — the four edge terms against a common majorant,
   purely arithmetic.  A horizontal edge reduces to the right line's inequality once its `log²K`
   cancels against the rectangle width `2 log^{-2}K`.
6. `RHTower/Sieve/MoebiusKappaTwoRate.lean` —
   ```
   exists_norm_tsum_moebius_smoothWeight_kappa_two_rate :
     ‖2π ∑' μ(n)·w(n)‖ ≤ coeffMajorantTwo C C' Ms L
         · (N+H+1) · (log(N+H+1))^{2/3} · exp(-(log(N+H+1))^{1/3}/18)
   ```
   for `0 < N`, `1 ≤ H`, `N/H ≤ L`, `2 ≤ N+H`, `1 ≤ log(N+H+1)`, `K₀ ≤ contourParamTwo (N+H+1)`.

All unconditional (`[propext, Classical.choice, Quot.sound]`).

**Comparison.**  The corpus's existing rate is for the *twisted* sum,
`exists_norm_sum_moebiusTwist_rate`, at exponent `1/10`.  This is the untwisted sum at `1/3`.

**Build note.**  The assembly first failed with a `linarith`/`whnf` heartbeat timeout.  The fix was
the same as before: lift the three coefficient-absorption steps to top-level lemmas
(`majorant_right_le`, `majorant_horizontal_le`, `majorant_left_le`) so each gets its own budget,
and replace every `nlinarith` on a degree-5 product by `mul_le_mul_of_nonneg_*` plus `linarith`.

**Step 5 (next).**  Transfer to the sharp sum.  The comparison costs `H+1` (the Möbius summand is
bounded by `1` on the transition window — cheaper than the Chebyshev case, which pays
`(H+1)·log(N+H)`).  Choosing `H = N/exp((log N)^{1/6})` keeps `L = exp((log N)^{1/6})`, so
`coeffMajorantTwo` grows like `exp(2(log N)^{1/6})` — negligible against `exp(-(log N)^{1/3}/18)`.
That gives `|∑_{n≤N} μ(n)| ≪ N·exp(-c(log N)^{1/3})`.

## Step 5 done: the sharp Möbius sum at exponent `1/3`

```
RHTower.Sieve.exists_norm_sum_moebius_kappa_two_rate :
  ∃ B ≥ 0, ∀ᶠ N in atTop,
    ‖∑_{n ≤ N} μ(n)‖ ≤ B · N · exp( -(log N)^{1/3} / 108 )
```

Unconditional (`[propext, Classical.choice, Quot.sound]`).  This is the quantitative form of the
corpus's `tendsto_norm_sum_moebius_div`, which had no rate at all.

### The width had to be re-tuned, not reused

`smoothWidth N = N/exp((log N)^{1/20})` is tuned to the exponent-nine saving.  Against the κ=2
saving it is **far too wide**: the smooth-versus-sharp comparison costs `H`, i.e. a saving of only
`exp(-(log N)^{1/20})`, which swamps `exp(-c(log N)^{1/3})`.  Nor can the window simply be narrowed
to `exp(-(log N)^{1/3})`: the contour bound's coefficient carries `(N/H)²`, so a window that narrow
costs `exp(2(log N)^{1/3})` and swamps the saving from the other side.

The balance is a *fraction* of the same power:

```
smoothRatioTwo N = exp( (log N)^{1/3} / 54 ),   smoothWidthTwo N = N / smoothRatioTwo N.
```

Then the price is `exp(t/27)`, the saving `exp(-t/18)`, their product `exp(-t/54)`; and the
comparison costs `N exp(-t/54)` — the same size.  `1/54` is where `L² · exp(-t/18)` meets `1/L`.
The polynomial factor `t²` costs one further halving, giving `1/108`.

### New modules

- `RHTower/Sieve/MoebiusWidthTwo.lean` — `smoothRatioTwo`, `smoothWidthTwo`, and
  `coeffMajorantTwo_le`: the rate's coefficient is a constant times `(L+2)²`.
- `RHTower/Sieve/MoebiusAbsorbTwo.lean` — the arithmetic of the absorption:
  `sq_ratio_le`, `log_shift_le` (the shift `N → N+H+1` at most squares the cutoff, so `t ≤ s ≤ 2t`),
  `sq_le_exp_div` (`t² ≤ 216²·exp(t/108)`, from `x + 1 ≤ exp x` squared), `mul_three_le`.
- `RHTower/Sieve/MoebiusSharpKappaTwo.lean` — `absorb_rate` (abstract, five variables),
  `smoothWidthTwo_eq`, `one_le_mul_exp_neg`, and the capstone.

### Traps hit

- `norm_sub_norm_le a b` gives `‖a‖ - ‖b‖ ≤ ‖a-b‖`, which is the *wrong direction* for bounding the
  sharp sum by the smooth one.  Use it with the arguments swapped, after `rw [norm_sub_rev]`.
- `Real.log_le_log` needs strict positivity of the *smaller* argument; `linarith` cannot supply
  `0 < N + smoothWidthTwo N + 1` unless `0 ≤ smoothWidthTwo N` is already in context.
- `1 ≤ Real.log N` does not give `0 < N` to `linarith` (mathlib's `log` is `0` off the positives);
  carry `0 < N` as a hypothesis rather than deriving it.

## Where `1/3` stands, and why the next gain needs a different mechanism

**Literature benchmark.**  `arXiv:2208.06141` (Lee–Leong) proves *explicit* unconditional bounds
`M(x) ≪ x exp(-η₁√(log x))` (exponent `1/2`) and
`M(x) ≪ x exp(-η₂(log x)^{3/5}(log log x)^{-1/5})` (Vinogradov–Korobov).  So `1/3` is below the
literature's exponent.  What is new here is that it is *formalized* and unconditional end to end.

**Why this route stops at `1/3`.**  The contour needs `1/ζ` polynomially bounded on the rectangle.
The transport of the `σ = 1 + log^{-2}` bound leftwards costs `‖ζ'/ζ‖ × (segment length)`, and
`ζ'/ζ ≪ log²` on the region is what the corpus has.  A segment of length `c/log|γ|` would therefore
cost `log²·(c/log) = c·log|γ|`, i.e. `‖ζ‖ ≫ |γ|^{-c}` — polynomial, useless.  The widest strip on
which `1/ζ` stays *polynomially bounded in the logarithm* is exactly width `≍ log^{-2}`, and that is
what fixes `1/3`.  This confirms the recorded ceiling rather than working around it.

**The exponent-`1/2` mechanism is not this one.**  The classical `exp(-c√(log x))` comes from the
**explicit formula over the zeros**, not from a `1/ζ` contour:

```text
ψ(x) - x = -∑_{|γ| ≤ T} x^ρ/ρ + O(x log²x / T),
|x^ρ| ≤ x·exp(-c log x / log|γ|),   #{ρ : |γ| ∈ [n, n+1]} ≪ log n,
```

and balancing `exp(-c log x/log T)` against `x/T` gives `log T = √(c log x)`.  That route needs the
zero-free region **and a zero-counting estimate**, but never needs `1/ζ` on the region at all.

The corpus already has the counting ingredient: `exists_wide_zero_count`
(`RHTower/Sieve/ZetaZeroCountWide.lean`), on `Re ρ ≥ 3/5`.  What is missing is a truncated explicit
formula.  That is the next target, and it is a genuinely different build from this contour chain —
not a further re-tuning of it.
