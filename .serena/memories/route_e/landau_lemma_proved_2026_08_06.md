# Landau's lemma is proved in the corpus (L1-L7 done)

Card: `docs/drafts/pipeline/1-in-progress/landau-lemma-log-derivative.md`.
Why it matters: `mem:route_e/zero_free_kappa9_is_structural_2026_08_06`.
All declarations `[propext, Classical.choice, Quot.sound]`.

## The two capstones

`RHTower/Sieve/LandauLemma.lean` — `landau_logDeriv`:
```
f analytic on ball c R0,  R < R0,  f c != 0,  ||f w|| <= M ||f c|| on ball c R0,  M > 1,
||z - c|| <= R/8,  f z != 0
==>  exists finite Z1 (zeros with ||rho - c|| <= R/2) and multiplicities m,
     || logDeriv f z - sum_{rho in Z1} m_rho/(z - rho) ||  <=  16 log M / R
```

`RHTower/Sieve/LandauRealPart.lean` — `neg_re_logDeriv_le`: same hypotheses, and if every retained
zero lies weakly left of `z`, then for **every** subfamily `S ⊆ Z1`
```
-Re (f'/f)(z)  <=  16 log M / R  -  sum_{rho in S} m_rho * Re (z - rho)^{-1}.
```

## The insight that made it cheap

I expected to need a zero-counting lemma (Jensen / Blaschke). **Not needed.** Split the zeros into
`Z1` (inside the half-disc) and the rest; put only `Z1` into the polynomial `P1`; set `h = f/P1`.
On the circle `||w - c|| = R`, every `rho in Z1` has `||w - rho|| >= R/2 >= ||c - rho||`, so
**termwise** `||P1 c|| <= ||P1 w||`, hence `||h w|| <= M ||h c||` there **with the same M**. The
maximum principle spreads it inward, and `h` is zero-free on the half-disc, so Borel-Caratheodory
applies. The naive "remove all zeros in the ball" factorisation does *not* work — `|P|` is
uncontrollable near the boundary — and that is the whole reason for the half-disc split.

## Chain of modules

| step | module | main name |
|---|---|---|
| L1 finite zero set | `HTGeometry/AnalyticBallZeroSet.lean` | `finite_zeros_of_analyticOnNhd_closedBall` |
| L2 factorisation | `HTGeometry/AnalyticBallFactorization.lean` | `exists_zeroFree_factor`, `eqOn_of_codiscreteWithin_ball` |
| L2b Finset form | `HTGeometry/AnalyticBallFinsetFactorization.lean` | `exists_finset_zeroFree_factorization`, `logDeriv_finset_prod_pow` |
| L4 BC + Cauchy | `RHTower/Sieve/BorelCaratheodoryLogDeriv.lean` | `norm_deriv_div_le_of_norm_le` (`8 log M / R` on the quarter-disc) |
| L5 Landau | `RHTower/Sieve/LandauLemma.lean` | `landau_logDeriv` |
| L6 real parts | `RHTower/Sieve/LandauRealPart.lean` | `neg_re_logDeriv_le` |
| L7 three-four-one for `zeta'/zeta` | `RHTower/Sieve/ZetaLogDerivThreeFourOne.lean` | `zero_le_three_four_one_logDeriv` |

Pre-existing corpus assets used: `RHTower.borel_caratheodory` and
`RHTower.exists_analyticOnNhd_exp_eq_ball` (both `RHTower/ArgumentVariation.lean`).

## What remains (L8)

Only the de la Vallee Poussin arithmetic. With `sigma = 1 + delta`:
- `-Re zeta'/zeta(sigma) < 1/delta + O(1)` (pole),
- `-Re zeta'/zeta(sigma + i gamma) <= 16 log M/R - Re (s - rho)^{-1}` (L6, `S = {rho}`),
- `-Re zeta'/zeta(sigma + 2 i gamma) <= 16 log M/R` (L6, `S = empty`),
- combine with `zero_le_three_four_one_logDeriv`, optimise `delta`.
Growth input: `PNTPlus.ZetaUpperBnd` (`|zeta| <= C log|t|` on `[1 - A/log|t|, 2]`) gives
`log M = O(log log t)`, i.e. `kappa = 1`. `RHTower/Sieve/ZetaLineRate.lean` sharpens the constant.

**Landau's `M` enters only as `log M`** — that is precisely why the exponent drops from 9 to 1.

## Lean traps

- `Σ` may not appear in an identifier (`hreΣ` silently parses as `hre` and then fails oddly).
- `logDeriv_prod` needs `(f := ...)` supplied explicitly when `iota = C`.
- `HasDerivAt.pow` rewrites the lambda into `Pi.pow` form; use `HasDerivAt.fun_pow`, and
  `simp only [Nat.add_sub_cancel]` to normalise the `k + 1 - 1` exponent before `field_simp`.
- `mul_le_mul_left` is not an iff here; use `le_of_mul_le_mul_left`.
