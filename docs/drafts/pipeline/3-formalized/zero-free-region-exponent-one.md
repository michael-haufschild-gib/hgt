# A zero-free region for zeta of exponent one

Status: formalized (2026-08-06). Unconditional.
Capstone: `RHTower.Sieve.exists_zero_free_region`
(`formal/GaloisForLFunctions/RHTower/Sieve/ZeroFreeRegionKappaOne.lean`).

## The constant is explicit (2026-08-06)

`exists_zero_free_region_explicit` states the same theorem with the width written out:

```lean
∃ T : ℝ, 3 ≤ T ∧ ∀ β γ : ℝ, T ≤ |γ| → β ≤ 1 →
  1 - 1 / 10000 / Real.log |γ| < β → riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0
```

**Only the threshold is existential.** The width is `1/(10000 log|γ|)`; the earlier description of
the constant as existential was wrong — the proof always produced `1/10000`, the statement merely hid
it. `exists_zero_free_region` is now a one-line corollary, so every consumer is unchanged.

For comparison, arXiv:2603.21490 (2026-03) gets `1/(4.896 log t)` from `t ≥ 3`: a factor ≈ 2000 in
the constant, and a threshold that is actually usable.

## Statement

```lean
theorem exists_zero_free_region :
    ∃ c T : ℝ, 0 < c ∧ 3 ≤ T ∧
      ∀ β γ : ℝ, T ≤ |γ| → β ≤ 1 → 1 - c / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0
```

`zeta` has no zero with `beta > 1 - c/log|gamma|` above the threshold height. Axioms:
`[propext, Classical.choice, Quot.sound]`.

## Why it matters

The corpus previously owned only `RHTower.Sieve.riemannZeta_ne_zero_of_re_gt`
(`1 - c/log^9 N < beta`), and the vendored `PNTPlus.ZetaZeroFree` is the same exponent `9`. Both go
through a mean-value estimate, and **that route cannot do better than `9`**: the width satisfies
`delta < C/(B0 M^4)` with `B0 ~ log N` and `M ~ log^2 N`, and `M ~ max|zeta|/R` is forced because
the growth bound `|zeta| << log N` only holds within `~1/log N` of `Re s = 1`. Improving the growth
bound does not move the exponent -- with Littlewood's `log/loglog` one only gains `(loglog)^5`.

The exit is to replace the mean value by the **logarithmic derivative**, which is what this card
builds. Landau's `M` enters only as `log M`, so a growth bound of size `log t` costs `log log t`
instead of `log t` -- that single change is the whole difference between the exponents `9` and `1`.

Route E's short-interval Moebius corridor requires a formalized region of exponent `kappa < 1`
(card `mr-splice-wide-range-mean-square.md`); `kappa = 1` with a `loglog` refinement also passes.
This card delivers `kappa = 1`; the refinement is the next step (see "Next").

## The chain

| step | module | statement |
|---|---|---|
| finite zero set on a ball | `HTGeometry/AnalyticBallZeroSet.lean` | `finite_zeros_of_analyticOnNhd_closedBall` |
| zero extraction | `HTGeometry/AnalyticBallFactorization.lean` | `exists_zeroFree_factor`, `eqOn_of_codiscreteWithin_ball` |
| finite-product form | `HTGeometry/AnalyticBallFinsetFactorization.lean` | `exists_finset_zeroFree_factorization`, `logDeriv_finset_prod_pow` |
| Borel-Caratheodory + Cauchy | `RHTower/Sieve/BorelCaratheodoryLogDeriv.lean` | `norm_deriv_div_le_of_norm_le` |
| Landau's lemma | `RHTower/Sieve/LandauLemma.lean` | `landau_logDeriv` |
| real-part form | `RHTower/Sieve/LandauRealPart.lean` | `neg_re_logDeriv_le` |
| three-four-one for `zeta'/zeta` | `RHTower/Sieve/ZetaLogDerivThreeFourOne.lean` | `zero_le_three_four_one_logDeriv` |
| pole term | `RHTower/Sieve/ZetaPoleLogDeriv.lean` | `exists_pole_bound` |
| crude growth | `RHTower/Sieve/ZetaCrudeGrowth.lean` | `norm_riemannZeta_le_crude` |
| Landau applied to `zeta` | `RHTower/Sieve/ZetaLandauInput.lean` | `zeta_landau_at` |
| the inequality | `RHTower/Sieve/DeLaValleePoussinInequality.lean` | `dlvp_inequality` |
| the region | `RHTower/Sieve/ZeroFreeRegionKappaOne.lean` | `exists_zero_free_region` |

Pre-existing corpus assets reused: `RHTower.borel_caratheodory`,
`RHTower.exists_analyticOnNhd_exp_eq_ball` (`RHTower/ArgumentVariation.lean`),
`RHTower.zetaEntire` and its nonvanishing, `ZetaRealBound.norm_riemannZeta_real_le`,
`ZetaPartialSumTruncation.norm_riemannZeta_le_partialSum`. Vendored, read-only:
`PNTPlus.ZetaInvBound1`.

## Two ideas that made it cheap

1. **No zero counting.** Landau's lemma is usually proved with a Jensen or Blaschke count of the
   zeros in the disc. It is not needed: split the zeros into those inside the half-disc and the
   rest, remove only the former, and observe that on the circle of radius `R` every removed zero
   satisfies `||w - rho|| >= R/2 >= ||c - rho||`, so **termwise** `||P1 c|| <= ||P1 w||` and the
   quotient obeys the *same* bound `M`. Removing all zeros in the ball does not work -- `|P|` is
   uncontrollable near the boundary.
2. **A deliberately crude growth bound.** `||zeta(w)|| <= 2 + 2||w||` on `Re w >= 1/2` suffices,
   because Landau consumes `log M`. It comes from the truncation at `N = 1`.

## Next

- **The Littlewood refinement.** Replacing the crude growth bound by
  `RHTower/Sieve/ZetaLineRate.lean` (`||zeta(1+it)|| <= 32 + 2L/(orderLowerBound L - 4/3)`,
  card `littlewood-zero-free-region.md`) sharpens `c/log|gamma|` to `c loglog|gamma| / log|gamma|`.
  That is the form Route E licenses.
- Supersede `ZeroFreeAssembly.riemannZeta_ne_zero_of_re_gt` at the call sites that only need a
  region (it is kept: its `zeroFreeConst` is explicit, whereas `c` here is existential).

## CORRECTION (2026-08-06): `exists_zero_count_bound` is vacuous

**The section below overstates its result and the description "this is the classical
`N(t+1) - N(t) = O(log t)`" is wrong.** `exists_zero_count_bound` counts the zeros retained by
Landau's lemma at radius `1/4` about `9/8 + iγ`, i.e. those with `‖ρ - (9/8+iγ)‖ ≤ 1/8`. Every such
point has `Re ρ ≥ 9/8 - 1/8 = 1`, and `ζ` has no zero there. **The retained family is empty and the
bound says nothing.** Proved in `RHTower/Sieve/ZetaNoZeroNearOne.lean`:
`zeta_ne_zero_near_nine_eighths` and `zeta_narrow_retained_empty`.

The classical count concerns the critical strip `0 ≤ Re ρ ≤ 1`; nothing here reaches it.

**What does carry content** is `exists_wide_zero_count` (`ZetaZeroCountWide.lean`), whose disc has
radius `21/40`, so retained zeros satisfy `Re ρ ≥ 9/8 - 21/40 = 3/5`
(`three_fifths_le_re_of_wide`). Those may exist unconditionally, and the bound is exactly what the
`ζ'/ζ` estimate consumes — so the *used* counting lemma is sound; only the standalone corollary was
empty.

**To reach the full strip** the disc would need radius `≥ 9/8`, hence `R ≥ 9/4` and `R₀ > 9/4`,
which pushes the disc into `Re w < 0` where the `N = 1` truncation gives no bound. A genuine
`N(T+1) - N(T)` count therefore needs the functional equation or a growth bound left of `Re s = 0` —
not available here.

## (superseded) Corollary: the zero-counting bound (2026-08-06)

`RHTower/Sieve/ZetaZeroCount.lean : exists_zero_count_bound` -- unconditional.

```lean
∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 3 ≤ |γ| →
  ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
    (∀ w, ‖w - (9/8 + i γ)‖ ≤ 1/8 → riemannZeta w = 0 → w ∈ Z) ∧
    (∀ ρ ∈ Z, riemannZeta ρ = 0) ∧ (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
    ∑ ρ ∈ Z, (m ρ : ℝ) ≤ C * Real.log (7 + 8 * |γ|)
```

This is the classical `N(t+1) - N(t) = O(log t)`, and it comes out of the same Landau inequality --
one only *keeps* the retained zeros instead of discarding them:

* each `rho` in the retained family has `‖rho - c‖ ≤ 1/8` and `Re rho ≤ 1`, so
  `Re (c - rho)^{-1} = (9/8 - Re rho)/|c - rho|^2 ≥ (1/8)·64 = 8` (`eight_le_re_inv`);
* the left-hand side is bounded **below** by the value on the real axis, because every von Mangoldt
  term satisfies `Re(Λ(n) n^{-σ-iγ}) ≥ -Λ(n) n^{-σ}` (`neg_re_logDeriv_ge`), and that value is
  `≤ 1/(σ-1) + A` by the pole bound.

So `8 ∑ m_rho ≤ 64 log M + (8 + A)` at `σ = 9/8`, and `log M = O(log|γ|)`.

The count is the missing input for the next two standard consequences:
`‖ζ'/ζ(s)‖ = O(log t)` and `‖1/ζ(s)‖ = O(log t)` inside the region -- both need to bound
`∑ m_rho/|s - rho|`, which is exactly what this supplies.

## Landau generalized over the evaluation point (2026-08-06)

`landau_logDeriv` and `neg_re_logDeriv_le` now quantify `z` **inside** the existential:

```
∃ Z1 m, (distances) ∧ (zeros) ∧ (every nearby zero is in Z1) ∧ (multiplicities ≥ 1) ∧
  ∀ z, ‖z - c‖ ≤ R/8 → f z ≠ 0 → ‖logDeriv f z - Σ_ρ m_ρ/(z-ρ)‖ ≤ 16 log M / R
```

`Z1` and `m` never depended on `z` (they are the zeros of `f` in the half-disc with their divisor
multiplicities); only the final Borel-Caratheodory/Cauchy step did, and that step is uniform on
`‖z - c‖ ≤ R/8`. **This is not cosmetic**: any argument that needs the *same* zero family at two
points — e.g. the count at the centre together with a bound at a point of the region — was
previously impossible, because two invocations return unrelated existential witnesses whose
multiplicities cannot be compared. The whole downstream chain rebuilds unchanged.

## Attempted next: `ζ'/ζ = O(log²|γ|)` in the region — NOT yet landed

The mathematics is settled and every input exists; only the Lean packaging failed. Design:

* centre `cpt = 9/8 + iγ`, `R = 21/20`, `R0 = 11/10`. The disc keeps `Re w ≥ 1/40` and
  `|Im w| ≥ 2`, and `‖z - cpt‖ ≤ R/8 = 21/160` reaches `σ ≥ 159/160` — below `1`, hence into the
  region. `R0 < 9/8` is what keeps the disc inside `Re w > 0` where the `N = 1` truncation applies.
* the crude bound generalises to any abscissa: `‖ζ w‖ ≤ 2 + ‖w‖/η` for `Re w ≥ η > 0`, `|Im w| ≥ 2`
  (`norm_riemannZeta_le_crude_of_re_ge`); with `η = 1/40` this gives `‖ζ‖ ≤ 91 + 40|γ|` on the disc,
  so `log M ≤ D·L` with `L = log|γ|` and `D` absolute.
* the count comes from the same `Z` at `z = cpt`: `Re (cpt - ρ)^{-1} ≥ (1/8)/(21/40)² = 200/441`,
  and the left side is `≥ -(8 + A)` by `neg_re_logDeriv_ge` and the pole bound, so
  `Σ m_ρ ≤ E·L`.
* each retained zero satisfies `Re ρ ≤ 1 - c/(2L)` (region, applied at `|Im ρ| ≥ T0`, using
  `log|Im ρ| ≤ log(2|γ|) ≤ 2L`), so `‖z - ρ‖ ≥ σ - Re ρ ≥ c/(4L)` when `σ ≥ 1 - (c/4)/L`.
* hence `‖ζ'/ζ(z)‖ ≤ B + (Σ m_ρ)·4L/c ≤ (320/21·D + 4E/c)·L²`.

**Why the build failed:** written as one theorem it exceeds the heartbeat limit — several `set`
locals plus `nlinarith` over a context with ~40 hypotheses. Two `linarith` calls also failed on
atoms differing only by a `set` abbreviation. The fix is to split into standalone lemmas with
explicit hypotheses (disc geometry; `log M ≤ D·L`; the count; the distance bound; the assembly),
each with a short context. The draft was removed rather than left broken.

## `ζ'/ζ = O(log²|γ|)` inside the region — DONE (2026-08-06)

`RHTower/Sieve/ZetaLogDerivRegionBound.lean : exists_logDeriv_zeta_bound`, unconditional.

```lean
∃ c' C T : ℝ, 0 < c' ∧ 0 < C ∧ 4 ≤ T ∧
  ∀ σ γ : ℝ, T ≤ |γ| → 1 - c' / Real.log |γ| ≤ σ → σ ≤ 1 →
    ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ C * Real.log |γ| ^ 2
```

The previous attempt failed only on Lean packaging; splitting it into four modules with short
contexts fixed it:

| module | content |
|---|---|
| `ZetaWideDisc.lean` | the disc of radius `11/10` around `9/8 + iγ`: `Re w ≥ 1/40`, `\|Im w\| ≥ 2`, `‖ζ w‖ ≤ 91 + 40\|γ\|`, analyticity. Plus `norm_riemannZeta_le_crude_of_re_ge` (crude bound at an arbitrary abscissa `η`). |
| `ZetaLandauWide.lean` | `wideD` (absolute), `log_wide_ratio_le` (`log M ≤ wideD·log\|γ\|`), and `zeta_landau_wide` — Landau at radius `21/20` with bound `(320/21)·wideD·log\|γ\|`, valid at every `z` within `21/160` of the centre. |
| `ZetaZeroCountWide.lean` | `wide_re_inv_ge` (`Re (c-ρ)^{-1} ≥ 200/441`) and `exists_wide_zero_count` — the count for **any** family satisfying Landau's inequality at the centre, so it composes with the previous module's output. |
| `ZetaLogDerivRegionBound.lean` | `wide_zero_re_le` (every retained zero has `Re ρ ≤ 1 - c/(2 log\|γ\|)`), then the assembly. |

Radii: `R = 21/20` and `R₀ = 11/10`, chosen so that `R₀ < 9/8` (disc inside `Re w > 0`, where the
`N = 1` truncation applies) while `R/8 = 21/160` still reaches `σ = 159/160 < 1`, i.e. into the
region. Landau reaches only an eighth of its radius, which is what forces `R > 1` and hence the
whole balancing act.

**The `z`-generalisation of `landau_logDeriv` is what makes this possible**: the count is taken at
the centre and the bound at the region point, and both need the *same* zero family with the *same*
multiplicities.

PNTPlus's corresponding `LogDerivZetaBnd` carries `log⁹|t|` on a width-`log^{-9}` strip; this is
`log²|t|` on a width-`log^{-1}` strip.

## Transporting `log‖·‖` along a segment (2026-08-06)

`RHTower/Sieve/LogNormSegment.lean`, unconditional. Three reusable lemmas:

* `norm_sub_le_segment` — the mean value inequality along a complex segment, for any function
  differentiable on it (the general form of the corpus's `norm_riemannZeta_sub_le`);
* `deriv_analyticLog_eq` — on a zero-free disc, an analytic logarithm `L` of `g` satisfies
  `deriv L = logDeriv g`;
* `abs_log_norm_sub_le` — **the point**: on a zero-free disc,
  ```
  |log‖g z₁‖ - log‖g z₂‖| ≤ (sup over the segment of ‖g'/g‖) * ‖z₁ - z₂‖.
  ```

`log‖g z‖ = Re (L z)` because `‖exp w‖ = exp (Re w)`, so the whole statement is the mean value
inequality applied to `L` and then `|Re w| ≤ ‖w‖`. **No branch cut appears anywhere** — the naive
route through `Complex.log` would hit one, and the route through `d/du log‖g(u+it)‖ = Re(g'/g)`
requires real-part derivatives of complex-valued functions of a real variable, where mathlib's
`Complex.reCLM` composition lands in a different `Module ℝ ℝ` instance path than the goal
(`RCLike.toInnerProductSpaceReal.toModule` vs `Semiring.toModule`) and fails to typecheck. The
analytic-logarithm route avoids both problems and reuses `RHTower.exists_analyticOnNhd_exp_eq_ball`.

This is the transport step for the `1/ζ` bound described in the memory
`route_e/inv_zeta_width_ceiling_2026_08_06`: with `σ₁ = 1 + L^{-2}` and `‖ζ'/ζ‖ ≤ A L²` it moves the
lower bound `‖ζ(σ₁+iγ)‖ ≫ L^{-3/2}` leftwards across the abscissa, reaching width `≍ log L / L²`
— versus PNTPlus's `L^{-9}`. The disc needed is thin (radius `≍ log L/L²` about the segment) and is
zero-free because every zero has `Re ρ ≤ 1 - c/(2L)` and `log L/L² ≪ 1/L`.

## The lower bound just right of the abscissa (2026-08-06)

`RHTower/Sieve/ZetaLowerNearAbscissa.lean`, unconditional.

* `neg_log_norm_riemannZeta_le_of_bound` — the reciprocal estimate with an **arbitrary** bound `B`
  at the doubled height: `-log‖ζ(σ+it)‖ ≤ (3/4) log(1 + 1/(σ-1)) + (1/4) log B`. (The earlier
  `neg_log_norm_riemannZeta_le` hard-codes the crude `B = 7 + 4|t|`, which is useless here — it
  costs `L/4`.)
* `exists_neg_log_zeta_upper` — at `σ₁ = 1 + log^{-2}|γ|`,
  ```
  -log‖ζ(σ₁ + iγ)‖ ≤ (7/4) · log log|γ| + C.
  ```
  i.e. `‖ζ(σ₁+iγ)‖ ≫ (log|γ|)^{-7/4}`.

The `(7/4)` is `(3/4)·2 + (1/4)·1`: the first term from `log(1 + log²|γ|)`, the second from the
**logarithmic** growth bound `‖ζ(σ₁+2iγ)‖ ≤ C₀ log|2γ|` — the vendored `PNTPlus.ZetaUpperBnd`,
applicable because `σ₁ > 1 > 1 - A/log|2γ|`. Using the crude linear bound instead would give
`L/4` and destroy the estimate.

**Choosing `σ₁ - 1 = log^{-2}` rather than `log^{-1}` is the whole point**: the segment-transport
budget is `≍ log log|γ| / log²|γ|`, which exceeds `σ₁ - 1` and therefore crosses the abscissa. At
`σ₁ - 1 = log^{-1}` it does not (see `mem:route_e/inv_zeta_width_ceiling_2026_08_06`).

Remaining for `1/ζ ≪ (log|γ|)^K` on width `≍ log log|γ|/log²|γ|`: feed this and
`exists_logDeriv_zeta_bound` into `abs_log_norm_sub_le`, with the thin zero-free disc around the
segment.

**Build note.** `lake env lean` and `lake build` print errors in *different formats* —
`file:line: error:` versus `error: file:line:`. A grep anchored to `^GaloisForLFunctions` silently
misses everything `lake build` reports. Grep for `error` unanchored.

## The thin disc (2026-08-06)

`RHTower/Sieve/ZetaThinDisc.lean`, unconditional. The geometry for transporting `log‖ζ‖` across the
abscissa: the disc of radius `3/L²` about `(1 + 1/L²) + iγ`, `L = log|γ|`.

* `thin_disc_re` — `Re w > 1 - 2/L²` there;
* `thin_disc_height` — `T₂ ≤ |Im w| ≤ 2|γ|` (heights stay within `3` of `γ`);
* `thin_disc_analytic` — `ζ` is analytic there (the disc avoids the pole);
* `thin_disc_zerofree` — **the point**: the disc is zero-free, because `Re w > 1 - 2/L²` and every
  zero has `Re ρ ≤ 1 - c/log|Im ρ| ≤ 1 - c/(2L)`, and `2/L² < c/(2L)` once `L > 5/c`.

The region's width `c/L` beats the disc's `2/L²` by a factor `L` — that is what lets a disc of
radius `≍ L^{-2}` sit entirely inside the zero-free region, and it is why the segment argument works
at `σ₁ - 1 = L^{-2}` but not at `L^{-1}`.

**Written as separate top-level lemmas on purpose.** The first attempt put all of this inside the
final theorem and hit the heartbeat limit — the same failure as the `ζ'/ζ` bound two steps back. A
`have`-chain of this length inside one proof does not elaborate; the identical content as top-level
lemmas with explicit hypotheses compiles in seconds.

Remaining for `1/ζ`: the segment endpoints and range, the `ζ'/ζ` bound along it (from
`exists_logDeriv_zeta_bound`), and `abs_log_norm_sub_le` — then combine with
`exists_neg_log_zeta_upper`.

## `1/ζ` on a strip of width `log^{-2}` — DONE (2026-08-06)

`RHTower/Sieve/ZetaInvStripBound.lean : exists_neg_log_zeta_upper_strip`, unconditional.

```lean
∃ K C T : ℝ, 0 ≤ K ∧ 4 ≤ T ∧ ∀ σ γ : ℝ, T ≤ |γ| →
  1 - 1 / Real.log |γ| ^ 2 ≤ σ → σ ≤ 1 + 1 / Real.log |γ| ^ 2 →
  -Real.log ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ K * Real.log (Real.log |γ|) + C
```

with `K = 7/4`, i.e. **`1/‖ζ‖ ≪ (log|γ|)^{7/4}` on `|σ - 1| ≤ log^{-2}|γ|`.** The vendored
`PNTPlus.ZetaLowerBnd` gives `(log|t|)^7` on width `log^{-9}|t|`: seven orders of width and a factor
four in the exponent.

The mechanism, and why the parameters are what they are:

* at `σ₁ = 1 + log^{-2}|γ|` the three-four-one estimate gives `‖ζ(σ₁+iγ)‖ ≫ (log|γ|)^{-7/4}`
  (`ZetaLowerNearAbscissa`);
* the segment from `σ₁` to any `σ` with `|σ-1| ≤ log^{-2}|γ|` has length `≤ 2 log^{-2}|γ|`;
* on it `‖ζ'/ζ‖ ≤ C_D log²|γ|` (`ZetaLogDerivRegionBound`), so the transport
  (`LogNormSegment.abs_log_norm_sub_le`) costs `C_D log²|γ| · 2 log^{-2}|γ| = 2 C_D` — a **constant**.

That exact cancellation is the whole point, and it is why `σ₁ - 1 = log^{-2}` and not `log^{-1}`:
at `log^{-1}` the segment is `log` times longer and the cost becomes `2 C_D log|γ|`, which destroys
the bound (see `mem:route_e/inv_zeta_width_ceiling_2026_08_06`).

Modules, all with short contexts by design:

| module | content |
|---|---|
| `ZetaThinDisc.lean` | the disc of radius `3/L²` about `σ₁+iγ`: real parts, heights, analyticity, **zero-freeness** (the region's width `c/L` beats the disc's `2/L²` by a factor `L`) |
| `ZetaThinSegment.lean` | the segment: parametrisation, range, endpoint/centre membership, distance, and `‖ζ'/ζ‖` along it |
| `ZetaInvStripBound.lean` | the assembly — nine lines of tactic once the pieces exist |

**Lean note.** `linarith` does not relate `1 / L^2` and `2 / L^2`: division by a non-numeral makes
each an independent atom. Supply `have : (2:ℝ)/L^2 = 2 * (1/L^2) := by ring` (and similarly for `3`)
whenever a goal mixes them. This is the same trap as `3 / δ` versus `3 * (1/δ)` recorded earlier.

## The exponent-one region, valid from height nine (2026-08-06)

`RHTower/Sieve/ZeroFreeRegionFromNine.lean : exists_zero_free_region_from_nine`, unconditional.

```lean
∃ c : ℝ, 0 < c ∧ ∀ β t : ℝ, 9 ≤ |t| → β ≤ 1 → 1 - c / Real.log |t| < β →
  riemannZeta ((β : ℂ) + (t : ℂ) * Complex.I) ≠ 0
```

`exists_zero_free_region` has the right *shape* but only past `T = exp(u₀²)` with `u₀ ≥ 202` —
`exp(40804)`, unusable as stated. The corpus's **explicit** exponent-nine region
`RHTower.riemannZeta_ne_zero_of_re_gt_one_sub` (constant `1/(2·27·28·224⁴)`) is valid from `|t| ≥ 9`,
and on the *bounded* range `[9, T]` its width `c₉/log⁹|t|` dominates `c/log|t|` as soon as
`c ≤ c₉/log⁸T` (`kappa_one_of_kappa_nine`). Shrinking the constant therefore extends the
exponent-one shape down to height `9`.

The constant is tiny — `c₉/log⁸T` with `log T ≥ 40804` — but the shape and range of validity are
what a consumer needs; the two regions are complementary rather than competing, and this makes that
explicit.

**Literature note.** arXiv:2603.21490 (2026-03-23) proves `ζ(σ+it) ≠ 0` for `t ≥ 3` and
`σ ≥ 1 - 1/(4.896 log t)` — the same shape with an explicit constant of order `0.2` from height `3`.
Reproducing that needs explicit numerical estimates (mollifiers, explicit `ζ` bounds), which the
no-computation constraint rules out here; it is recorded as the sharp target, not as a gap.

## `ζ'/ζ` from height ten (2026-08-06)

`exists_logDeriv_zeta_bound` is now a corollary of

```lean
exists_logDeriv_zeta_bound_of_region {c T₀ : ℝ} (hc0 : 0 < c)
  (hregion : ∀ β γ', T₀ ≤ |γ'| → β ≤ 1 → 1 - c / Real.log |γ'| < β → riemannZeta (β + iγ') ≠ 0) :
  ∃ c' C, 0 < c' ∧ 0 < C ∧ ∀ σ γ, max 4 (T₀ + 1) ≤ |γ| → 1 - c'/log|γ| ≤ σ → σ ≤ 9/8 →
    ‖logDeriv riemannZeta (σ + iγ)‖ ≤ C * log|γ| ^ 2
```

— the region is now a *hypothesis*, and the threshold is exposed as `max 4 (T₀ + 1)` rather than
hidden existentially. Two instantiations:

* `exists_logDeriv_zeta_bound` — the asymptotic region, as before;
* `exists_logDeriv_zeta_bound_from_ten` — the from-nine region, giving threshold **10**.

Only the constant `C` degrades. **The threshold has to be exposed, not existential**, or the
instantiation cannot name it.

**The trade-off is real, and it does not propagate everywhere.** `exists_zero_free_region_from_nine`
buys its low threshold with a tiny constant `c ≈ c₉/log⁸T`. Any downstream result whose proof needs
`log|γ| ≥ k/c` inherits an even *worse* threshold than before — e.g.
`exists_neg_log_zeta_upper_strip`, which requires `L ≥ 5/c` for the thin disc to sit inside the
region. The `ζ'/ζ` bound is different: its proof needs only `L ≥ 1`-type conditions and `T₀ + 1`, so
swapping the region is a pure win there. Check for `1/c` conditions before substituting.

## The strip bound, multiplicatively (2026-08-06)

`RHTower/Sieve/ZetaLowerStripMultiplicative.lean : exists_zeta_lower_strip`, unconditional:

```lean
∃ c T : ℝ, 0 < c ∧ 4 ≤ T ∧ ∀ σ γ : ℝ, T ≤ |γ| →
  1 - 1 / Real.log |γ| ^ 2 ≤ σ → σ ≤ 1 + 1 / Real.log |γ| ^ 2 →
  c / Real.log |γ| ^ 2 ≤ ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
```

— the logarithmic bound exponentiated, with `7/4` weakened to the integer `2` so that no real power
is needed. This is the form a contour argument consumes.

Two points that the logarithmic statement hides:

* **`log‖ζ‖` needs `ζ ≠ 0` to be invertible.** In Lean `Real.log 0 = 0`, so `-log‖ζ‖ ≤ B` is
  *satisfied* by `ζ = 0` and carries no information there. The nonvanishing has to be supplied
  separately: `zeta_ne_zero_on_thin_strip` shows the strip sits inside the zero-free region, since
  its width `log^{-2}|γ|` is below `c₀/log|γ|` once `log|γ| > 1/c₀`.
* **The exponent is now exposed.** `exists_neg_log_zeta_upper` and
  `exists_neg_log_zeta_upper_strip` state `7/4` literally instead of hiding it behind `∃ K`;
  otherwise the weakening `7/4 ≤ 2` cannot even be stated by a consumer. Same lesson as the
  region's constant: **existentially quantifying a constant that the proof computes makes the
  result unusable downstream.**

## Widths and constants, all exposed (2026-08-06)

Third and last pass of the same correction. `exists_logDeriv_zeta_bound_of_region` now states its
strip width in terms of the region's constant:

```lean
∃ C, 0 < C ∧ ∀ σ γ, max 4 (T₀ + 1) ≤ |γ| →
  1 - min (c/4) (1/160) / Real.log |γ| ≤ σ → σ ≤ 9/8 →
  ‖logDeriv riemannZeta (σ + iγ)‖ ≤ C * Real.log |γ| ^ 2
```

and `exists_logDeriv_zeta_bound_explicit` instantiates the explicit region to give the width
**`1/(40000 log|γ|)`**. Only `C` remains existential, and it genuinely is: it depends on the pole
constant `A`, which is a supremum over a compact set.

Summary of what is now visible rather than hidden:

| quantity | value |
|---|---|
| zero-free region width | `1/(10000 log\|γ\|)` |
| `ζ'/ζ` strip width | `1/(40000 log\|γ\|)` |
| `ζ'/ζ` bound | `C log²\|γ\|`, `C` existential |
| `1/ζ` strip width | `log^{-2}\|γ\|` |
| `1/ζ` bound exponent | `7/4` (weakened to `2` in the multiplicative form) |
| thresholds | existential, and astronomically large except the from-nine/from-ten variants |

**The recurring defect was uniform**: every one of these was computed by the proof and then hidden
behind an `∃`, which makes the statement true, unusable, and impossible to compare with the
literature. Expose any constant the proof actually produces.
