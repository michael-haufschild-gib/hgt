# Squared-Xi order-seventeen corner source exclusion

- **ID:** `squared-xi-order-seventeen-corner-source-exclusion`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-disproof route discriminator
- **Scientific status:** `[LEAN-VERIFIED] [UNCONDITIONAL] [NOT AN RH DISPROOF]`
- **Parent:** `squared-xi-order-seventeen-edge-corner.md`

## Statement

There is no Xi multiplicity copy in the compact centered corner

`4/25 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 132`.

Consequently every order-eighteen reciprocal-power atom at every squared shift `y>1/4` is
strictly positive. The fixed order-seventeen squared-seam lane cannot produce an RH-false source
witness.

## Source proof

Seven rational first-theta-atom interval certificates on `[0,7/8]`, with positive fifth-order
endpoint propagation, give

```text
thetaCuspAtomRawEvenMoment 2 1 > 263/100000,
thetaCuspNormalizedEvenMoment 2 > 263/50000.
```

Together with the factorable Euler--Mascheroni certificate, endpoint-curvature bound, endpoint
resolvent, and thermal-orientation inequalities, this forces

```text
normalizedPrimeArchMoment 0 < 29/625,
normalizedPrimeArchMoment 1 < 1/5000.
```

Every individual fourth reciprocal-trace atom is nonnegative. An atom in the displayed corner
is strictly greater than `5/100000`; its four distinct FE--Schwarz copies therefore contribute
strictly more than `1/5000` to the complete trace. This contradicts the source upper bound.

No zero table, numerical integration, or RH assumption enters the proof.

## Anti-theatre gate

This is a route kill. It proves another RH-compatible sign and therefore pushes the scalar source
search to order at least eighteen; it must not be reported as an RH disproof.

## Gates

- [x] Seven-interval exact theta fourth-moment floor formalized.
- [x] Complete fourth reciprocal trace bounded by `1/5000` in Lean.
- [x] Compact-corner quartet lower bound formalized.
- [x] Corner excluded and global order-eighteen atom positivity formalized.
- [x] Exact target build passed.
- [x] Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Formalization

- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomFourthMomentFloor.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderFourteenCornerSourceExclusion.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderSeventeenEdgeCorner.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderSeventeenCornerSourceExclusion.lean`
