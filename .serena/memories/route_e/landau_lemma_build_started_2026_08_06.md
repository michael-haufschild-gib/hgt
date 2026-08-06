# Landau-lemma build — L1, L2, L7 done

Card: `docs/drafts/pipeline/1-in-progress/landau-lemma-log-derivative.md`.
Motivation: `mem:route_e/zero_free_kappa9_is_structural_2026_08_06`.

## Done, unconditional

- **L7** `RHTower/Sieve/ZetaLogDerivThreeFourOne.lean` — `zero_le_three_four_one_logDeriv`:
  `0 <= 3 Re(-z'/z(s)) + 4 Re(-z'/z(s+it)) + Re(-z'/z(s+2it))` for `sigma > 1`.
  Route: `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (mathlib, in
  `Mathlib/NumberTheory/LSeries/Dirichlet.lean`), `Complex.re_tsum`, `vonMangoldt_nonneg`,
  `3 + 4cos + cos2 = 2(1+cos)^2`. The corpus's `re_prime_cpow_neg` (in `ZetaThreeFourOne.lean`)
  is stated for any positive natural, so it serves the von Mangoldt terms directly.
  Also `re_logDeriv_shift_le`, the consumable form.
- **L1** `HTGeometry/AnalyticBallZeroSet.lean` — `finite_zeros_of_analyticOnNhd_closedBall`.
- **L2** `HTGeometry/AnalyticBallFactorization.lean` — `exists_zeroFree_factor`:
  `f z = (finprod_u (z-u)^(divisor f (ball c R) u)) * g z` on the whole open ball, `g` analytic and
  zero-free.

## Mathlib assets that made L1/L2 cheap (do not rebuild)

- `MeromorphicOn.divisor_ball_support_finite` (`Analysis/Meromorphic/Divisor.lean:104`)
- `MeromorphicNFOn.zero_set_eq_divisor_support` (`Analysis/Meromorphic/NormalForm.lean:578`)
- `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd` (`NormalForm.lean:552`)
- `MeromorphicOn.extract_zeros_poles` (`Analysis/Meromorphic/FactorizedRational.lean:291`)
- `Function.FactorizedRational.finprod_eq_fun`, `.analyticAt` (same file, ~line 67/81)
- `AnalyticOnNhd.eqOn_or_eventually_ne_of_preconnected` (`Analytic/IsolatedZeros.lean:245`)
- `meromorphicOrderAt_ne_top_iff_eventually_ne_zero`
- `isPreconnected_ball` lives in `Mathlib/Analysis/Normed/Module/Connected.lean` (NOT in
  `Analysis/Convex/*`; `Mathlib.Analysis.Convex.Normed` does not exist in this toolchain).

## The reusable piece worth remembering

`HTGeometry.eqOn_of_codiscreteWithin_ball` — two analytic functions on a ball agreeing on a
codiscrete subset agree everywhere. Mathlib's meromorphic factorisation results conclude only
`=[codiscreteWithin U]`; this lemma is the bridge to a pointwise identity, and every future use of
`extract_zeros_poles` needs it. It rests on `codiscreteWithin_ball_ne_bot`, i.e. `NeBot (nhdsWithin z
{z}^c)` in `C`.

## Next

L3 (modulus of the factorised product on the circle) -> L4 (`RHTower.borel_caratheodory` applied to
an analytic logarithm of `g/g c`, using `exists_analyticOnNhd_exp_eq_ball` from
`RHTower/ArgumentVariation.lean`) -> L5 Landau's lemma -> L6 one-zero drop -> L8 DLVP (`kappa = 1`)
-> L9 Littlewood refinement via `RHTower/Sieve/ZetaLineRate.lean`.

## Repo hazard

Umbrella files (`GaloisForLFunctions/HTGeometry.lean` etc.) are edited concurrently by other agents;
an import added early in a session can be gone later. Re-check with `grep` before the final build.
`scripts/formal_tools.py index` writes only `LEAN_API.md`, `LEAN_GAPS.md`, `LEAN_OVERVIEW.md` — it
does **not** regenerate umbrellas, so it is not the culprit.
