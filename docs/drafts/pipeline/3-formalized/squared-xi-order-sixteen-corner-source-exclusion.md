# Squared-Xi order-sixteen corner source exclusion

- **ID:** `squared-xi-order-sixteen-corner-source-exclusion`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-disproof route discriminator
- **Scientific status:** `[LEAN-VERIFIED] [UNCONDITIONAL] [NOT AN RH DISPROOF]`
- **Parent:** `squared-xi-order-sixteen-edge-corner.md`

## Statement

There is no Xi multiplicity copy in the compact centered corner

`9/50 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 118`.

Consequently every order-seventeen reciprocal-power atom at every squared shift `y>1/4` is
strictly positive. The fixed order-sixteen squared-seam lane cannot produce an RH-false source
witness.

## Source proof

Six rational first-theta-atom interval certificates on `[0,3/4]` give

```text
thetaCuspAtomRawEvenMoment 2 1 > 3/1250,
thetaCuspNormalizedEvenMoment 2 > 3/625.
```

Together with the factorable Euler--Mascheroni certificate, the endpoint-curvature bound,
endpoint resolvent, and thermal-orientation inequalities, this forces

```text
normalizedPrimeArchMoment 0 < 29/625,
normalizedPrimeArchMoment 1 < 7/25000.
```

Every individual fourth reciprocal-trace atom is nonnegative. An atom in the displayed corner
is strictly greater than `7/100000`; its four distinct FE--Schwarz copies therefore contribute
strictly more than `7/25000` to the complete trace. This contradicts the source upper bound.

No zero table, numerical integration, or RH assumption enters the proof.

## Anti-theatre gate

This is a route kill. It proves a stronger RH-compatible sign at order sixteen and therefore
pushes the source search to order at least seventeen; it must not be reported as an RH disproof.

## Gates

- [x] Six-interval exact theta fourth-moment floor formalized.
- [x] Complete fourth reciprocal trace bounded by `7/25000` in Lean.
- [x] Corrected compact-corner quartet lower bound formalized.
- [x] Corner excluded and global order-seventeen atom positivity formalized.
- [x] Exact target build passed.
- [x] Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Formalization

- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomFourthMomentFloor.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderFourteenCornerSourceExclusion.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderSixteenEdgeCorner.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderSixteenCornerSourceExclusion.lean`
