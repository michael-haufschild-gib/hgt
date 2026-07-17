# Squared-Xi order-eighteen corner source exclusion

- **ID:** `squared-xi-order-eighteen-corner-source-exclusion`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-disproof route discriminator
- **Scientific status:** `[LEAN-VERIFIED] [UNCONDITIONAL] [NOT AN RH DISPROOF]`
- **Parent:** `squared-xi-order-eighteen-edge-corner.md`

## Statement

There is no Xi multiplicity copy in the compact centered corner

`7/50 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 147`.

Consequently every order-nineteen reciprocal-power atom at every squared shift `y>1/4` is
strictly positive. The fixed order-eighteen squared-seam lane cannot produce an RH-false source
witness.

## Source proof

The exact boundary estimate

```text
3/70 < exp(-pi)
```

follows from Mathlib's certified upper bound on `exp(1)`, the rational bound `pi<22/7`, and the
geometric exponential majorant at `1/14`. Substituting this sharper prefactor into the seven
rational first-theta-atom interval certificates gives

```text
thetaCuspAtomRawEvenMoment 2 1 > 269/100000,
thetaCuspNormalizedEvenMoment 2 > 269/50000.
```

The completed endpoint and thermal inequalities then force

```text
normalizedPrimeArchMoment 0 < 29/625,
normalizedPrimeArchMoment 1 < 9/50000.
```

Every fourth reciprocal-trace atom is nonnegative. An atom in the displayed corner is strictly
greater than `9/200000`; its four distinct FE--Schwarz copies therefore contribute strictly more
than `9/50000` to the complete trace, a contradiction.

No zero table, numerical integration, or RH assumption enters the proof.

## Anti-theatre gate

This is a route kill. It proves another RH-compatible sign and pushes the scalar source search to
order at least nineteen; it must not be reported as an RH disproof.

## Gates

- [x] Sharper symbolic `exp(-pi)` floor formalized.
- [x] Seven-interval exact theta fourth-moment floor strengthened.
- [x] Complete fourth reciprocal trace bounded by `9/50000` in Lean.
- [x] Compact-corner quartet lower bound formalized.
- [x] Corner excluded and global order-nineteen atom positivity formalized.
- [x] Exact target build passed.
- [x] Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Formalization

- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomFourthMomentFloor.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderFourteenCornerSourceExclusion.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderEighteenEdgeCorner.lean`
- `formal/GaloisForLFunctions/RHTower/XiOrderEighteenCornerSourceExclusion.lean`
