# Theta modular-seam strict fluctuation law

- **ID:** theta-modular-seam-strict-fluctuation-law
- **Stage:** 1-in-progress
- **Type:** THEOREM-FIRST CROSS-ENDPOINT LAW / PAPER-PROVED / LEAN-PENDING-AUDIT
- **Source modules:**
  `RHTower/ThetaCuspLikelihoodSpectralMeasure.lean`,
  `RHTower/ThetaCuspLikelihoodModularSeam.lean`
- **Formal target:**
  `RHTower/ThetaCuspLikelihoodModularFluctuation.lean`

## Statement

Set

```text
B0 = thetaCuspLikelihoodCoordinate(0) = pi - 3/2,
mj = thetaCuspHigherLikelihoodSpectralMoment(B0,j),
sigma = thetaCuspFirstAtomBoundaryLogSlope.
```

Then

```text
sigma^2 (1+m0)^2 < (2*pi)^2 m0 m2.
```

Equivalently, the exact modular first-moment constraint lies strictly inside the order-two
Stieltjes moment cone; equality is excluded by the infinite support of the source likelihood
measure.

## Bottom-up derivation

1. `det_thetaCuspHigherLikelihoodSpectralMoment_hankel_pos` at `B=B0`, `q=2` gives
   `m0*m2-m1^2>0`.
2. `thetaCuspHigherLikelihoodSpectralMoment_seam_barycenter` gives
   `2*pi*m1=sigma*(1+m0)`.
3. Squaring the second identity and multiplying the strict determinant inequality by
   `(2*pi)^2>0` yields the statement.

This is not a rewrite of either parent. Modular stationarity alone allows a one-point carrier and
equality. Strict Hankel positivity alone does not identify `m1` with the theta boundary slope.

## Hostile audit

- Positive Laplace transforms and their Hankel positivity are classical; Pushnitski--Treil's
  positive-Hankel survey/inverse problem records the measure representation:
  https://arxiv.org/abs/2503.22189
- Dimitrov--Xu relate Laplace-transform Wronskians to positive correlation measures and discuss
  the Riemann Xi kernel:
  https://arxiv.org/abs/1606.05011
- Salazar gives a recent general order-moment/Hankel transport criterion with strictness controlled
  by measure support:
  https://arxiv.org/abs/2606.31647
- Coffey studies positivity and exact derivatives of Riemann xi from its theta kernel:
  https://doi.org/10.1016/j.cam.2003.09.003

Exact and phrase searches found no source combining the normalized higher-theta likelihood
spectral measure, its modular-seam barycenter, and the strict inequality above. This is a
noncollision result, not a priority claim.

## Lean status

- Scratch theorem elaborated with `lake env lean /tmp/hgt_theta_seam_fluctuation.lean`.
- Repository source written; direct source check, axiom audit, and final module build remain.
- No numerical experiment or computation was used.
