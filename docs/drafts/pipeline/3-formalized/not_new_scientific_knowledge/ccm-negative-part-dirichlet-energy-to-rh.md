# Summable negative rectangular energy closes RH

- **ID:** `ccm-negative-part-dirichlet-energy-to-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM / TOP-DOWN RH PREDECESSOR
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `ccm-observable-power-lower-zero-free-region.md`

## Claim

Fix one admissible rectangular family and write

```text
Q_L(n) = Re Q_Xi(chi_((log n)/2,L), chi_((log n)/2,L)).
```

Let `x_- = max(0,-x)`.  Then

```text
for every epsilon>0,
  sum_(n>=N) Q_L(n)_- / n^(1+epsilon) < infinity
    -> RiemannHypothesis.                                  (1)
```

This is strictly weaker than an eventual pointwise subpower floor.  It permits arbitrarily large
negative spikes provided their logarithmic Dirichlet energy is sufficiently sparse.

## Proof

Let `S_L(n)` be the full positive-transverse divisor carrier and let
`g(n)=max(0,-S_L(n))`.  The bounded observable remainder gives

```text
g(n) <= Q_L(n)_- + B_L.                                   (2)
```

Hence `(1)` makes the correction L-series `sum g(n)n^(-s)` absolutely convergent on every
half-plane `re s>1`.

Assume false RH and let `delta>0` be the positive transverse supremum.  Choose
`0<beta<delta`.  The coefficients

```text
S_L(n)+g(n)=max(S_L(n),0)                                 (3)
```

are nonnegative.  Their Dirichlet series has the continuation

```text
2 * shiftedZetaCarrier_L(s) + sum g(n)n^(-s),             (4)
```

which is holomorphic on a Landau ball around `1+delta`: the second term is holomorphic on
`re s>1+beta`, while the first has the already formalized pole-free ball.  Scale-local Landau
transfer forces `(3)` to converge at some real `sigma<1+delta`.  Subtracting the summable
correction makes the original carrier converge there.  Exact shifted-pole order then bounds every
right Xi zero by `sigma-1<delta`, contradicting the definition of `delta`.

## Positive chain

```text
summable negative part of one source-defined observable
  -> summable negative-part correction of the divisor carrier
  -> nonnegative corrected coefficients
  -> local Landau transfer left of the rightmost Xi pole
  -> exact pole-order contradiction
  -> RH.                                                   (5)
```

## Why this is a useful source target

The condition is an energy statement rather than a uniform pointwise floor.  It can be supplied by
weighted `L2` control: Cauchy--Schwarz converts

```text
sum Q_L(n)_-^2 / n^(1+epsilon) < infinity
```

into `(1)` after splitting the exponent.  This creates a direct interface for Gram, Sonin,
Möbius-coisometry, Wigner--Eisenstein, or theta covariance estimates even when they cannot control
every sample.

## Non-circularity firewall

The negative energy must be proved from the prime--Gamma or operator source.  It may not be
obtained from Xi zero locations, the shifted-zeta continuation, Weil positivity, or any limiting
measure already equivalent to RH.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/CCMRectangularNegativePartEnergyGate.lean`

Principal declarations:

- `XiRectangularRightNegativePartEnergy`
- `exists_xiRectangularNegativePartLandauCoefficient_summable_left_of_boundary`
- `riemannHypothesis_of_xiRectangularRightNegativePartEnergy`
- `XiRectangularWeilTailNegativePartEnergy`
- `xiRectangularRightNegativePartEnergy_of_xiRectangularWeilTailNegativePartEnergy`
- `riemannHypothesis_of_xiRectangularWeilTailNegativePartEnergy`

The exact module build passes.  Both RH capstones use only `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] mathematical mechanism isolated
- [x] strictly weaker quantifier pattern than pointwise subpower control identified
- [x] general summable-correction Landau theorem formalized
- [x] observable-to-carrier negative-part transport formalized
- [x] exact RH capstone built and axiom-checked
- [ ] source-defined weighted negative-energy estimate proved
- [ ] novelty and significance audited
- [ ] RH
