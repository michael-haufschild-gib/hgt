# Mass-shifted adaptive mixed source parabolic floor

- **ID:** `mass-shifted-adaptive-mixed-source-parabolic-floor`
- **Stage:** 3-formalized
- **Type:** THEOREM / ARITHMETIC SOURCE CAPITAL
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`

## Conjecture loop

1. A denominator-free reset estimate follows from ordinary packet spread. **False:** corpus
   counterfamily forces adjacent-mean hyperbolic weight.
2. Uniform relative Gauss-bulk floor directly bounds actual source capital. **False as stated:**
   reciprocal-mass dilation contributes exact weight `w^4 = y^2`.
3. The same low edge feeds the drift-removed action used by both degree coercivity and hyperbolic
   reset. **True:** normalized `alpha` has weight `w^2`, normalized `beta` has weight `w^4`, so
   every term in cumulative dissipation has common weight `w^4`.
4. The uniform floor is the strongest degree-free conclusion. **False:** projective Gauss-root
   spread is strictly dominated by half the dimensionless source action, while corpus spread
   diverges along every cofinal mass-and-degree positive-block schedule.

## Paper theorem

For normalized and actual shifted-Xi Jacobi data in a common positive block,

```text
D_dim(w,n) = w^4 D_actual(w^2,n).
```

For `n >= 2`, `D_dim` contains `4 beta_1`. One universal far-right threshold gives
`beta_1 > 1/16`, hence

```text
1/4 < D_dim(w,n),
1/(4 w^4) < D_actual(w^2,n),
1/4 < w^4 J_n(w).
```

Here `J_n` is exactly literal drift-removed adaptive mixed/completed arithmetic source action.
Thus producer used by degree and reset laws cannot collapse on parabolic scale before its forced
`y^-2` coordinate weight is removed.

More sharply, for every `n >= 2`,

```text
2 projectiveGaussRootSpread(w,n) < D_dim(w,n).
```

Consequently, for every cofinal pair of schedules `w_l -> infinity`, `n_l -> infinity` carrying
positive actual Hankel blocks of order `n_l + 4`,

```text
w_l^4 J_{n_l}(w_l) -> infinity.
```

This excludes every bounded-renormalized-source false-RH escape, without selecting a fixed
observation dimension or a fixed linear reporter.

## Honest residual

Raw floor remains integrable in mass, and cofinal divergence has no proved rate or width in mass.
It therefore does not yet give RH: arbitrarily tall, arbitrarily narrow renormalized source spikes
remain compatible with current pointwise laws. Exact next burden is degree-uniform integral
propagation (an actual source Lipschitz/anti-spike theorem), or an arithmetic upper budget that
contradicts cofinal divergence.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceParabolicFloor
```

Capstones:

- `dimensionlessCumulativeJacobiDissipation_eq_fourth_mul_actual`;
- `four_mul_lowEdge_lt_dimensionlessCumulativeJacobiDissipation`;
- `exists_uniform_adaptiveMixedCompletedSourceAction_parabolicFloor`;
- `two_mul_projectiveGaussRootSpread_lt_dimensionlessCumulativeJacobiDissipation`;
- `tendsto_renormalized_adaptiveMixedCompletedSourceAction_along_cofinal_positive_blocks`.

Direct `lake env lean` and targeted module build pass. Axiom audit of all capstones reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is umbrella-wired. No computation, RH
premise, representing measure, fixed reporter, orientation map, or added axiom is used.
