# Hedenmalm--Sonin escape analytic-gauge cusp no-go

- **Label:** `P-G130`
- **Route:** P
- **Parent:** `P-G129`
- **Status:** theorem proved in Lean; umbrella integration complete

## Conjecture tested

P-G129 proves that actual Sonin evaluator escape has transverse rate
`lambda=|Re rho-1/2|`.  A scalar normalization cancelling the escape uniformly on both sides of
the critical wall would therefore require modulus

```text
exp(-c |x|),   c > 0,
```

in a centered transverse coordinate `x`.  Test whether any scalar gauge holomorphic at the wall
can have this exact modulus.

## Scientific decision gate

- **Success:** retire every regular holomorphic scalar renormalization of two-sided Sonin escape.
  Surviving producer must be vector-valued, singular at the wall, or restricted to discrete Xi
  support rather than a neighborhood.
- **Failure:** locate regularity gap precisely and test whether a weaker analytic class can still
  carry the required cusp.
- Rephrasing nondifferentiability of `|x|` without deriving it from actual gauge modulus counts as
  theatre.  Proof must transport holomorphic differentiability through restriction, norm, and log.

## Prior-research audit

- 2026-08-13 — P-G129 joins actual Xi divisor support, literal Burnol evaluation vectors, and
  completed radial work.  Existing corpus contains one-sided escape laws and reflection no-gos but
  no exact obstruction to a scalar analytic normalization across the critical wall.
- 2026-08-13 — Cartier, head-flux, capacity, common-forcing, and positive Hilbert completions were
  re-audited.  Each absorbs or transports positive work; none supplies a source upper budget.

## Conjecturing log

- 2026-08-13 — C1 opened: exact two-sided escape cancellation forces an absolute-value cusp in
  scalar log modulus.
- 2026-08-13 — C2 opened: nonzero holomorphic scalar gauge has differentiable norm and log norm
  along the transverse real line, contradicting the cusp.
- 2026-08-13 — C3 opened: geometric aperture coefficient `N log r` is positive for `N>0`, `r>1`,
  so the no-go applies at every nontrivial tower scale.

## Verification log

- 2026-08-13 — Direct foreground check passed:
  `lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmSoninEscapeAnalyticGaugeCuspNoGo.lean`.
- 2026-08-13 — Imported by `GaloisForLFunctions/RHTower.lean`.
- 2026-08-13 — Exact module build passed:
  `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmSoninEscapeAnalyticGaugeCuspNoGo`
  (`12957/12957`).
- 2026-08-13 — Axiom audit passed for every new theorem; dependencies are exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-08-13 — Added and directly verified the stronger exported cusp theorem
  `not_differentiableAt_soninEscapeCancellingGaugeModulus`; exact rebuild passed (`12957/12957`).

## Result and pivot

- C1--C2 close without assumptions beyond positive rate and complex
  differentiability at the wall.
- C3 closes because `N log r>0` for every nontrivial geometric aperture tower.
- Scalar analytic sewing is retired as mathematically impossible.  Next loop will test
  the strongest survivor: a rank-two/vector-valued orientation bundle whose norm may be smooth
  while its smallest singular value carries the scalar cusp only after minimization.
