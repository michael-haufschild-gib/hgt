# Squared-Xi order-fifteen corner source exclusion

- **ID:** `squared-xi-order-fifteen-corner-source-exclusion`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-disproof route discriminator
- **Scientific status:** `[LEAN-VERIFIED] [UNCONDITIONAL] [NOT AN RH DISPROOF]`
- **Parent:** `squared-xi-order-fifteen-edge-corner.md`

## Statement

There is no Xi multiplicity copy in the compact centered corner

`1/5 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 104`.

Consequently every order-sixteen reciprocal-power atom at every squared shift `y>1/4` is strictly
positive.  The fixed order-fifteen squared-seam lane cannot produce an RH-false source witness.

## Source proof

The exact first-theta-atom interval certificates give

`thetaCuspNormalizedEvenMoment 2 > 2151/500000`.

The factorable Euler--Mascheroni certificate and the rational logarithm certificate give

`xiEndpointCompletedCurvature < 463/10000`.

Combining these with the endpoint resolvent and thermal-orientation inequalities forces

```text
normalizedPrimeArchMoment 0 < 29/625,
normalizedPrimeArchMoment 1 < 9/25000.
```

Every individual fourth reciprocal-trace atom is nonnegative.  An atom in the displayed corner
is strictly greater than `9/100000`; its four distinct FE--Schwarz copies therefore contribute
strictly more than `9/25000` to the complete trace.  This contradicts the source upper bound.

No zero table, numerical integration, or RH assumption enters the proof.

## Anti-theatre gate

This is a route kill.  It proves a stronger RH-compatible sign at order fifteen and therefore
pushes the source search to order at least sixteen; it must not be reported as an RH disproof.

## Gates

- [x] Sharpened exact theta fourth-moment floor formalized.
- [x] Sharpened Euler--Mascheroni and endpoint-curvature bounds formalized.
- [x] Complete fourth reciprocal trace bounded by `9/25000` in Lean.
- [x] Compact-corner quartet lower bound formalized.
- [x] Corner excluded and global order-sixteen atom positivity formalized.

## Formalization

- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomFourthMomentFloor.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderFourteenCornerSourceExclusion.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderFifteenEdgeCorner.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderFifteenCornerSourceExclusion.lean`
