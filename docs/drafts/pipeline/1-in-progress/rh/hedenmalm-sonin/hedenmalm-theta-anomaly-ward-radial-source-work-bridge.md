# Hedenmalm theta anomaly: Ward radial-source-work bridge

- **Label:** `P-G127`
- **Route:** P
- **Parents:** `P-G124`, `P-G126`, `RouteRBurnolThetaSameFiberOrientation`
- **Status:** theorem and no-go proved in Lean; umbrella integration complete

## Conjecture tested

Let `f_rho` be completed first-divided Xi vector, `f_(rho#)=star(f_rho)`, and let `u_rho,v_rho`
be its invariant and anti-invariant real sectors from P-G126. First prove exact response
Pythagorean identity

```text
||u_rho||^2 + ||v_rho||^2 = ||f_rho||^2.
```

Consequently completed radial source work factors as

```text
W_rho = Im(z_rho)^2 ||f_rho||^2
      = Im(z_rho)^2 2 pi M^2 thetaRootEnergy(z_rho).
```

For a multiplicity copy `q`, define positive Ward radial gain

```text
A_q = burnolTwoPrimeFrameEnergy(z_q)^2 ||f_q||^2 > 0.
```

Conjecture exact cross-construction bridge

```text
normSq(WardAnomaly_q) = A_q W_(q.1),
WardEuclideanEnergy_q  = 2 A_q W_(q.1).
```

## Scientific decision gate

- **Success:** prove P-G124 Krein/Euclidean defect and P-G126 completed radial work are same positive
  obstruction under source-derived gain. This rules out Ward anomaly as independent passivity
  producer and localizes missing input to Green/boundary geometry capable of forcing radial work
  nonpositive or zero.
- **Failure:** isolate phase, multiplicity, or source normalization preventing identification.
- No RH premise, computation, axiom, abstract landing assumption, or renamed RH equivalence.

## Prior-research audit

- 2026-08-13 — Searched `formal/`, `docs/drafts/pipeline/2-fully-proven`,
  `docs/drafts/pipeline/3-formalized`, and `docs/drafts/pipeline/5-failed` for radial source work,
  line-pair norm decomposition, and Ward/work identities. Corpus contains P-G124 Ward defect,
  P-G126 radial work, same-fibre root energy, and Green boundary laws separately; no theorem joins
  these quantities or proves pair-response Pythagoras.
- Existing Green-square research explicitly requires quadratic Ward action before absolute
  completion. This conjecture tests whether current Ward defect supplies such a new action or only
  reweights already-positive source work.

## Conjecturing log

- 2026-08-13 — Opened exact positive-gain bridge. Paper proof uses line-conjugate norm invariance,
  parallelogram law, P-G126 source-work balance, and P-G124 exact anomaly/channel identities.

## Verification log

- 2026-08-13 — Direct foreground check passed:
  `lake env lean GaloisForLFunctions/RHTower/HedenmalmThetaAnomalyWardRadialSourceWorkBridge.lean`.
- 2026-08-13 — Exact module build passed:
  `lake build GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyWardRadialSourceWorkBridge`
  (`12949/12949`).
- 2026-08-13 — Axiom audit passed for all capstones; dependencies are exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-13 — Imported by `GaloisForLFunctions/RHTower.lean`. Formal lint and final umbrella
  build remain global audits; concurrent unrelated modules may independently affect them.

## Result and no-go closure

- Exact Pythagoras holds:
  `||u_rho||^2 + ||v_rho||^2 = ||f_rho||^2`.
- Completed radial work has three exact readings:
  `W_rho = Im(z_rho)^2 ||f_rho||^2`,
  `W_rho = Im(z_rho)^2 2 pi M^2 thetaRootEnergy(z_rho)`, and
  `W_rho = Im(z_rho) pi M thetaXiRankTwoBoundaryFlux(z_rho)`.
- Work is invariant under line conjugation. Pairing a zero with its functional-equation partner
  doubles quadratic work even though signed Green current cancels.
- Ward anomaly is not an independent neutralizer. Its squared norm is exactly
  `A_q W_(q.1)` and Euclidean Ward energy is `2 A_q W_(q.1)`, with `A_q > 0`.
- Positive survivor: Route P's completed resolvent work and Ward/Krein defect are one universal
  radial-dissipation invariant viewed through strictly positive gains. Any closing theorem must
  introduce independent signed passivity before quadratic scalarization; reflection pairing,
  realification, or Ward aggregation alone can only preserve or amplify off-line work.
