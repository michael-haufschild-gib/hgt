# Landau's lemma and the logarithmic-derivative zero-free region

Status: in progress (opened 2026-08-06)
Depends on: `littlewood-zero-free-region.md` (growth side, Z1-Z9, complete)

## Why this card exists

The corpus and the vendored `PNTPlus` both own a zero-free region of exponent `kappa = 9`
(`RHTower.Sieve.riemannZeta_ne_zero_of_re_gt`, `PNTPlus.ZetaZeroFree`). The Route E short-interval
Moebius corridor needs `kappa < 1` — concretely the Littlewood region
`sigma >= 1 - c loglog t / log t`.

**`kappa = 9` is structural, not sloppy.** In `ZeroFreeAssembly.lean` the region's width `delta`
satisfies `delta < C / (B0 * M^4)` where `B0 ~ L` bounds `|zeta(sigma+2i gamma)|` and `M ~ L^2`
bounds `|zeta'|` on the segment (`L = log N`). The `9` is `1 + 4*2`. And `M ~ L^2` is forced:
`M ~ max|zeta| / R` by Cauchy, and the radius `R` may not exceed `~ 1/L` because the growth bound
`|zeta| << log N` is only valid within `~ 1/log N` of `Re s = 1`.

Consequence, verified: **improving the growth bound does not move `kappa`.** With Littlewood's
`|zeta| << L/loglog L` one gets `delta <~ (loglog L)^5 / L^9`. The exponent is untouched.

The only exit is to replace the mean-value step `|zeta(sigma+i gamma)| <= M (sigma - beta)` by the
**logarithmic-derivative** step.

## The target

**Landau's lemma.** Let `f` be analytic on `ball c R`, `f c != 0`, and `|f z| <= e^M * |f c|` on the
ball. Then for `|z - c| <= R/4`,

```
| f'(z)/f(z)  -  sum_{rho : |rho - c| <= R/2} 1/(z - rho) |  <=  C * M / R
```

with the sum over zeros counted with multiplicity. Taking real parts and dropping every term but one
(each `Re 1/(z-rho) >= 0` when `Re z` exceeds every `Re rho`) gives

```
-Re f'(z)/f(z)  <=  C M / R  -  Re 1/(z - rho_0).
```

Fed into the three-four-one inequality for `-Re zeta'/zeta` this is de la Vallee Poussin.

## What already exists — do not rebuild

| piece | where |
|---|---|
| Borel-Caratheodory on a ball | `RHTower/ArgumentVariation.lean : borel_caratheodory` |
| analytic logarithm of a zero-free function on a ball | `RHTower/ArgumentVariation.lean : exists_analyticOnNhd_exp_eq_ball` |
| three-four-one for `log|zeta|` | `RHTower/Sieve/ZetaThreeFourOne.lean` |
| the `kappa = 9` assembly (to be superseded, not deleted) | `RHTower/Sieve/ZeroFreeAssembly.lean` |
| growth bound `|zeta(1+it)| << log t / loglog t` | `RHTower/Sieve/ZetaLineRate.lean` |
| growth bound on a rectangle, width `~ 1/log t` | `RHTower/Sieve/DirichletSigmaCapstone.lean` |
| `|zeta| <= C log|t|` on `[1 - A/log|t|, 2]` | `PNTPlus/ZetaBounds.lean : ZetaUpperBnd` (read-only) |

## Steps

1. **L1 — finite zero set.** The zeros of a nonzero analytic function in a closed ball form a finite
   set (mathlib: isolated zeros + compactness).
2. **L2 — factorisation.** `f = g * prod_{rho} (z - rho)^(m rho)` with `g` analytic and zero-free on
   the ball.
3. **L3 — the modulus of the product.** Lower bound for `|prod (z - rho)^m|` on the boundary circle,
   upper bound on the smaller disc: the standard `(R/2)^m` versus `(2R)^m` comparison.
4. **L4 — Borel-Caratheodory on `log(g/g(c))`.** Gives `|g'/g| <= C M / R` on `|z-c| <= R/4`.
5. **L5 — Landau's lemma.** Combine: `f'/f = g'/g + sum m/(z-rho)`.
6. **L6 — the real-part form and the one-zero drop.**
7. **L7 — the three-four-one inequality for `-Re zeta'/zeta`** (the corpus has the `log|zeta|` form;
   the derivative form is `sum_n Lambda(n) n^(-sigma) (3 + 4 cos(t log n) + cos(2 t log n)) >= 0`).
8. **L8 — de la Vallee Poussin:** `kappa = 1`.
9. **L9 — Littlewood refinement:** feed `ZetaLineRate` to get `c loglog t / log t`.

## Log

- 2026-08-06 -- card opened; the kappa analysis above verified against `quarter_comparison` and
  `deriv_const_le` in `ZeroFreeAssembly.lean`.
- 2026-08-06 -- **L7 done.** `RHTower/Sieve/ZetaLogDerivThreeFourOne.lean`:
  `zero_le_three_four_one_logDeriv` — `0 <= 3 Re(-zeta'/zeta(sigma)) + 4 Re(-zeta'/zeta(sigma+it))
  + Re(-zeta'/zeta(sigma+2it))` for `sigma > 1`, from
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` plus `3 + 4 cos + cos 2 = 2(1+cos)^2` and
  `vonMangoldt_nonneg`. Also `re_logDeriv_shift_le`, the consumable form. Unconditional.
- 2026-08-06 -- **L1 done.** `HTGeometry/AnalyticBallZeroSet.lean`:
  `finite_zeros_of_analyticOnNhd_closedBall`. Mathlib supplies everything —
  `MeromorphicOn.divisor_ball_support_finite` (compactness) and
  `MeromorphicNFOn.zero_set_eq_divisor_support` (zeros = divisor support), with the
  nowhere-locally-zero hypothesis discharged from one nonzero value by
  `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` on the preconnected ball.
- 2026-08-06 -- **L2 assets located.** `MeromorphicOn.extract_zeros_poles`
  (`Mathlib/Analysis/Meromorphic/FactorizedRational.lean:291`) gives the zero-free factor `g`
  directly. Three glue steps remain:
  (a) the divisor is nonneg for an analytic `f` (`Meromorphic/NormalForm.lean:552`), so the
      exponents are naturals;
  (b) `finprod` over a finite support becomes a `Finset.prod`;
  (c) the conclusion is only `=[codiscreteWithin U]`; upgrade to `EqOn` by
      `Mathlib/Analysis/Analytic/IsolatedZeros.lean:246` (`EqOn f g U` or the difference is
      codiscretely nonzero) on the preconnected ball.
  Note the ordering: take the zero set inside `closedBall c r` for `r < R` so that the quotient is
  zero-free on the whole open ball of radius `r` where Borel-Caratheodory will be applied.
- 2026-08-06 -- **L2 done.** `HTGeometry/AnalyticBallFactorization.lean`:
  `exists_zeroFree_factor` — an analytic `f` on `closedBall c R`, nonzero somewhere on the open
  ball, satisfies `f z = (prod^fin_u (z - u)^(divisor f (ball c R) u)) * g z` on the whole open
  ball, with `g` analytic and zero-free there.
  Supporting lemmas, all reusable:
  * `meromorphicOrderAt_ne_top_of_analytic_ball` — the non-degeneracy hypothesis of
    `extract_zeros_poles`, from one nonzero value;
  * `codiscreteWithin_ball_ne_bot` — the codiscrete filter of a nonempty ball is not `bot`
    (a point of `C` is not isolated);
  * `eqOn_of_codiscreteWithin_ball` — **the upgrade**: two analytic functions on a ball agreeing
    codiscretely agree everywhere. This is what turns `extract_zeros_poles`' conclusion into a
    genuine pointwise identity;
  * `divisor_nonneg_of_analytic_ball` — the exponents are nonnegative, so the factor is a
    polynomial and `Function.FactorizedRational.analyticAt` applies.
  Next: L3/L4 -- bound `|prod|` above and below on the circle, apply `borel_caratheodory` to
  `log (g / g c)`, then L5 = Landau's lemma.
- 2026-08-06 -- **L2b, L4, L5 done.**
  * L2b `HTGeometry/AnalyticBallFinsetFactorization.lean`:
    `exists_finset_zeroFree_factorization` (the factorisation as an honest `Finset` product with
    natural exponents, plus `f z = 0 <-> z in Z` on the ball), `logDeriv_sub_const_pow`,
    `logDeriv_finset_prod_pow` (the log-derivative of the zero polynomial is
    `sum_rho m_rho/(z - rho)`).
  * L4 `RHTower/Sieve/BorelCaratheodoryLogDeriv.lean`: `norm_deriv_div_le_of_norm_le` --
    for `g` analytic, zero-free and `<= M |g c|` on `ball c R`,
    `||g'(z)/g(z)|| <= 8 log M / R` on `||z - c|| <= R/4`. Route: analytic logarithm
    (`exists_analyticOnNhd_exp_eq_ball`), `Re log(g/g c) <= log M`, `borel_caratheodory` on the
    half-disc (the factor `2 rho/(R - rho) <= 2`), then `Complex.norm_deriv_le_of_forall_mem_
    sphere_norm_le` on the quarter-disc.
  * L5 `RHTower/Sieve/LandauLemma.lean`: `landau_logDeriv` --
    ```
    f analytic on ball c R0, R < R0, f c != 0, ||f w|| <= M ||f c|| on ball c R0, M > 1,
    ||z - c|| <= R/8, f z != 0
    ==> exists a finite Z1 of zeros with ||rho - c|| <= R/2 and multiplicities m,
        || logDeriv f z - sum_{rho in Z1} m_rho/(z - rho) || <= 16 log M / R.
    ```

  **The point that makes L5 cheap.** Split the zeros of `f` in the ball into `Z1` (inside the
  half-disc) and the rest, and put only `Z1` into the polynomial `P1`; let `h = f / P1`. On the
  circle `||w - c|| = R` every `rho in Z1` satisfies `||w - rho|| >= R/2 >= ||c - rho||`, so
  **termwise** `||P1 c|| <= ||P1 w||` and hence `||h w|| <= M ||h c||` there — with the *same* `M`.
  The maximum principle spreads that to `closedBall c R`, and `h` is zero-free on the half-disc, so
  L4 applies with radius `R/2`. **No zero-counting lemma (Jensen, Blaschke) is needed anywhere.**
  That was the step I expected to be the expensive one.

  Remaining: L6 (real parts; drop all but one zero) -- short; L8 de la Vallee Poussin; L9 the
  Littlewood refinement.
- 2026-08-06 -- **L6 done.** `RHTower/Sieve/LandauRealPart.lean`: `neg_re_logDeriv_le` --
  under Landau's hypotheses, if every retained zero lies weakly left of `z` then for **every**
  subfamily `S` of the retained zeros
  ```
  -Re (f'/f)(z)  <=  16 log M / R  -  sum_{rho in S} m_rho * Re (z - rho)^{-1}.
  ```
  `S = empty` is the no-zero bound; `S = {rho0}` is the zero-free-region step. Supporting:
  `re_inv_sub_nonneg` (`Re (z-rho)^{-1} = (Re z - Re rho)/|z-rho|^2 >= 0`) and `re_natCast_div`.

  **Steps L1, L2, L2b, L4, L5, L6, L7 are all done and unconditional.** What is left is only the
  arithmetic of de la Vallee Poussin (L8): pick `sigma = 1 + delta`, apply the three-four-one
  inequality `zero_le_three_four_one_logDeriv` with
  * at `sigma`: `-Re zeta'/zeta(sigma) < 1/(sigma-1) + O(1)` (the pole; corpus/PNTPlus own the
    Laurent expansion of `zeta` at `1`),
  * at `sigma + it`: L6 with `S = {beta + i gamma}`,
  * at `sigma + 2it`: L6 with `S = empty`,
  and optimise `delta`. The growth input `M` is `PNTPlus.ZetaUpperBnd` (`|zeta| <= C log|t|` on
  `[1 - A/log|t|, 2]`), giving `log M = O(log log t)`, hence `kappa = 1`; feeding
  `RHTower/Sieve/ZetaLineRate.lean` instead sharpens the constant.

  Note the shape: Landau's `M` enters only through `log M`, so a growth bound of size `log t` costs
  `log log t` -- this is exactly why the exponent drops from `9` to `1`.
- 2026-08-06 -- **The three inputs of L8 are built.**
  * `RHTower/Sieve/ZetaPoleLogDeriv.lean`: `logDeriv_riemannZeta_eq`
    (`logDeriv zeta s = logDeriv zetaEntire s - 1/(s-1)`, using the corpus's entire
    `RHTower.zetaEntire` and its nonvanishing on `Re s >= 1`) and `exists_pole_bound`:
    ```
    exists A, for all 1 < sigma <= 2 :  -Re zeta'/zeta(sigma)  <=  1/(sigma - 1) + A
    ```
    obtained by compactness of `[1,2]` for the continuous `-Re logDeriv zetaEntire`.
    **The coefficient of `1/(sigma-1)` is exactly `1`** -- essential: the Chebyshev route would
    give `log 4 > 4/3` and the three-four-one optimisation would fail.
  * `RHTower/Sieve/ZetaCrudeGrowth.lean`: `norm_riemannZeta_le_crude` --
    `||zeta w|| <= 2 + 2||w||` for `Re w >= 1/2`, `|Im w| >= 2`. Truncation at `N = 1` collapses
    the head to `1`; the two tail terms give `1/||w-1||` and `||w||/Re w`. Crude, but Landau
    consumes only `log M`, so linear growth costs `O(log t)` -- the classical DLVP input.
  * Landau strengthened: `landau_logDeriv` / `neg_re_logDeriv_le` now also export
    `(forall w, ||w - c|| <= R/2 -> f w = 0 -> w in Z1)` (so a *given* zero is retained) and
    `(forall rho in Z1, 1 <= m rho)` (multiplicities are genuine), both needed to keep the
    single zero `beta + i gamma` in the sum.

  **L8 plan, fully determined.** For a hypothetical zero `rho = beta + i gamma`, `|gamma| >= 3`,
  put `sigma = 1 + delta`, `c = sigma + i gamma`, `z = c`, `R = 1/4`, `R0 = 3/8`. Then the disc has
  `Re w >= 5/8` and `|Im w| >= |gamma| - 3/8`, so `ZetaCrudeGrowth` applies, and
  `M1 = (7 + 2|gamma|)/||zeta c||`. Landau retains every zero within `1/8` of `c`, in particular
  `rho` when `sigma - beta <= 1/8`. With `S = {rho}` at height `gamma` and `S = empty` at height
  `2 gamma`, the three-four-one inequality gives

  ```
  4/(sigma - beta)  <=  3/delta + 3A + 256 log M1 + 64 log M2.
  ```

  Lower bounds for `||zeta||` come from the vendored `PNTPlus.ZetaInvBound1`
  (`1/||zeta(sigma+ti)|| <= ||zeta sigma||^(3/4) ||zeta(sigma+2ti)||^(1/4)`) together with the
  corpus's `norm_riemannZeta_real_le` (`||zeta sigma|| <= 1 + 1/(sigma-1)`), so
  `log M1, log M2 = O(log|gamma|)`. Choosing `delta = c0/log|gamma|` with `c0` small enough that
  `4/c0 - 3/c0 > 5 * (Landau constant)` yields `1 - beta >= c/log|gamma|`: **kappa = 1**.
- 2026-08-06 -- **L8 done: the de la Vallee Poussin inequality.**
  * `RHTower/Sieve/ZetaLandauInput.lean`: `zeta_landau_at` -- Landau's lemma instantiated at
    `sigma + i gamma` for `1 < sigma <= 2`, `|gamma| >= 3`, with `R = 1/4`, `R0 = 3/8`. The disc
    stays in `Re w >= 5/8`, `|Im w| >= 2`, so `ZetaCrudeGrowth` gives `||zeta w|| <= 7 + 2|gamma|`
    there and `M = (7+2|gamma|)/||zeta(sigma+i gamma)||`. Conclusion, for every `S` inside the
    retained zeros:
    ```
    -Re zeta'/zeta(sigma+i gamma)
       <= 64 log((7+2|gamma|)/||zeta(sigma+i gamma)||) - sum_{rho in S} m_rho Re(sigma+i gamma-rho)^{-1}
    ```
  * `RHTower/Sieve/DeLaValleePoussinInequality.lean`:
    - `neg_log_norm_riemannZeta_le` -- `-log||zeta(sigma+it)|| <= (3/4)log(1+1/(sigma-1))
      + (1/4)log(7+4|t|)`, from the vendored `PNTPlus.ZetaInvBound1` together with the corpus's
      `norm_riemannZeta_real_le` and the crude bound at the doubled height;
    - **`dlvp_inequality`** -- for a zero `beta + i gamma` with `|gamma| >= 3`, `0 < delta <= 1/16`,
      `1 - beta <= 1/16`:
      ```
      4/(1 + delta - beta)  <=  3/delta + 3A
            + 320 * ( (5/4) log(7 + 8|gamma|) + (3/4) log(1 + 1/delta) )
      ```
      where `A` is the pole constant of `exists_pole_bound`.
    Unconditional; `[propext, Classical.choice, Quot.sound]`.

  **Remaining: L8b, the optimisation only.** Put `delta = c0/log|gamma|`. The right side is
  `3 log|gamma|/c0 + 400 log|gamma| + O(log log|gamma|)`, the left side `> 4 log|gamma|/(c0 + c)`
  if `1 - beta < c/log|gamma|`. A contradiction needs `4/(c0+c) > 3/c0 + 401`, i.e. `c0 < 1/401`
  and `c` small; `c0 = 1/500`, `c = 1/10000` works once `|gamma|` is large enough that the
  `log log` term is below `log|gamma|`. That last "eventually" is the only remaining Lean work.

  **Lean note (cost me several builds).** `linarith` does *not* identify `3 / delta` with
  `3 * (1 / delta)`: a goal containing `3 / delta` and hypotheses containing `1 / delta` are
  different atoms to it. Insert `have : (3:R)/delta = 3 * (1/delta) := by ring; rw [this]` first.
