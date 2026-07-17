# Squared-Xi order-fourteen corner source exclusion

- **ID:** `squared-xi-order-fourteen-corner-source-exclusion`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-disproof route discriminator
- **Scientific status:** `[LEAN-VERIFIED] [UNCONDITIONAL] [NOT AN RH DISPROOF]`
- **Parent:** `squared-xi-order-fourteen-edge-corner.md`

## Statement

There is no multiplicity copy of a nontrivial Xi zero in the compact centered corner

`1/5 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 100`.

Consequently every order-fifteen reciprocal-power atom at a squared shift `y > 1/4` is strictly
positive.  This closes the fixed order-fourteen squared-seam disproof lane: it cannot supply a
negative source witness.

## Source proof

Let `mu_j` be the normalized even moments of the positive theta-cusp source and let
`M = normalizedPrimeArchMoment 0`.  The dominant first theta atom gives the unconditional floor

`mu_2 > 2151/500000`.

The endpoint resolvent identity and the already proved quartet orientation estimate give

`M - endpointResolvent <= thermalSecondMoment / 4`,

`thermalSecondMoment <= (84/83) * normalizedPrimeArchMoment 1`.

Together with

`normalizedPrimeArchMoment 1 = M^2/2 - mu_2/6`

and the sharpened elementary endpoint bound

`xiEndpointCompletedCurvature < 463/10000`,

these inequalities force `M < 29/625`, hence

`normalizedPrimeArchMoment 1 < 9/25000`.

On the other hand every fourth reciprocal atom has nonnegative real part.  Four FE--Schwarz copies
of a zero in the displayed corner contribute strictly more than `39/100000` to the same trace,
a contradiction.  The endpoint bound uses only rational logarithm inequalities and the exact
Euler--Mascheroni sequence at `6250 = 2*5^5`; the theta floor uses exact rational interval
integration.  No zero table or numerical integration enters the proof.  The stronger trace bound
is also the source budget used by the order-fifteen corner exclusion.

## Anti-theatre gate

This theorem is a route kill, not evidence that RH is false.  It removes the first unprotected
fixed squared-seam order and forces the RH-false search to a genuinely growing-order or different
source producer.  It must not be reported as an RH disproof.

## Gates

- [x] Dominant theta-atom fourth-moment floor proved in Lean.
- [x] Source inequalities and quartet contradiction proved on paper.
- [x] Source inequalities formalized in Lean.
- [x] Compact corner excluded in Lean.
- [x] Order-fifteen atom positivity formalized in Lean.

## Formalization

- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomFourthMomentFloor.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderFourteenCornerSourceExclusion.lean`
