# Weighted square energy of the negative rectangular tail proves RH

- **ID:** `ccm-negative-part-square-energy-to-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM / HILBERT-SPACE RH PREDECESSOR
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `ccm-negative-part-dirichlet-energy-to-rh.md`

## Statement

Fix one admissible rectangular tail and write

```text
g_L(n) = max(0, -Re Q_Xi(chi_((log n)/2,L), chi_((log n)/2,L))).
```

If, for every `epsilon>0`,

```text
sum_(n>=N) g_L(n)^2 / n^(1+epsilon) < infinity,          (1)
```

then the Riemann hypothesis holds.

## Proof

For `sigma=1+epsilon`, split the weight into two equal factors:

```text
g_L(n) / n^sigma
  = (g_L(n) / n^(sigma/2)) * (1 / n^(sigma/2)).           (2)
```

The first factor is square summable by `(1)`.  The second is square summable because
`sum n^(-sigma)` converges for `sigma>1`.  Cauchy--Schwarz therefore gives

```text
sum_(n>=N) g_L(n) / n^(1+epsilon) < infinity.             (3)
```

The formalized negative-part Dirichlet-energy gate turns `(3)` into RH.

## Positive chain

```text
weighted L2 negative energy of one observable rectangular family
  -> weighted Cauchy--Schwarz
  -> negative-part L1 Dirichlet energy
  -> bounded observable-remainder transport
  -> nonnegative corrected Landau series
  -> exact rightmost-pole contradiction
  -> RH.                                                   (4)
```

This is the operator-facing formulation: a Gram, covariance, Sonin, Möbius, theta, or scattering
construction may target the literal square sum `(1)` instead of a pointwise lower bound.

## Non-circularity boundary

The square-energy estimate must be derived from the completed source.  It cannot be obtained from
Xi zero locations, Weil positivity, the shifted-zeta continuation, or an RH-equivalent limiting
measure.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularNegativePartSquareEnergyGate.lean`

Principal declarations:

- `realDirichletWeightedTerm`
- `LSeriesSummable_of_squareWeightedTerm_summable`
- `XiRectangularWeilTailNegativePartSquareEnergy`
- `xiRectangularWeilTailNegativePartEnergy_of_squareEnergy`
- `riemannHypothesis_of_xiRectangularWeilTailNegativePartSquareEnergy`

The exact module build passes.  The analytic transfer and RH capstone use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] weighted Cauchy--Schwarz transfer proved
- [x] square-energy condition converted to negative Dirichlet energy
- [x] composition to RH formalized
- [x] exact build and axiom check
- [ ] source-defined square-energy estimate proved
- [ ] RH
