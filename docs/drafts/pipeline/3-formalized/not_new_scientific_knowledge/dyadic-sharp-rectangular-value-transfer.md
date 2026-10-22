# The dyadic sharp bound sews into the rectangular adjacent-block floor

- **ID:** `dyadic-sharp-rectangular-value-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / VALUE-RELATION BRIDGE
- **Scientific status:** `[FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-EQUIVALENT INPUT]`

## Statement

Write

```text
W(n)=sum_(n/2<k<=n) Lambda(k)/sqrt(k).
```

For every real `x`, the continuous sharp dyadic prime window satisfies the exact floor identity

```text
sharpMovingPrimeWindowMass(log 2,x)=W(floor(exp x)).       (1)
```

Consequently an eventual estimate

```text
W(n)<=2(1-1/sqrt(2))*sqrt(n)+C*n^epsilon                  (2)
```

extends to every sufficiently large logarithmic height as

```text
sharpPrimePolarCoefficient(log 2,x)>=-2C*exp(epsilon*x).  (3)
```

There is no discretization remainder in `(1)`--`(3)`. Natural floor commutes exactly with division
by two, and `sqrt(floor(exp x))<=exp(x/2)` has the favorable sign.

The sharp-to-rectangular sewing identity then gives, at every sufficiently large integer sample,

```text
criticalMellinAdjacentBlock(log 2,log n)
  >=-C*(log 2)*n^epsilon.                                 (4)
```

Thus the all-epsilon version of `(2)` discharges the all-epsilon completed critical-Mellin
adjacent-block lower estimate with the explicit constant conversion
`D_epsilon=C_epsilon*log 2`.

## RH leverage

The same dyadic hypothesis already implies RH through the independently formalized sharp Landau
gate. Hence, for every fixed `L>0`, it also supplies the actual rectangular Weil tail

```text
Re Q_L(n)>=-C_epsilon*n^epsilon                           (5)
```

without using the still-open piecewise-linear Guinand--Weil source identity. This is a logical
discharge of the abstract `Q_L` hypothesis; equation `(4)` is the separate source-value transfer.

The module also exposes the requested theorem with no bundled proposition interface:

```text
RH iff exists N, forall epsilon>0, exists C_epsilon>=0,
  forall n>=N,
    Re Q_L(n)+C_epsilon*n^epsilon>=0.
```

## Lean realization

The implementation is

```text
GaloisForLFunctions.RHTower.CCM.CCMDyadicSharpRectangularTransfer.
```

Principal declarations:

```text
sharpMovingPrimeWindowMass_logTwo_eq_dyadicWeightedPrimeWindow_floorExp
continuous_sharpPrimePolarCoefficient_lower_of_dyadicWeightedPrimeWindow_upper
criticalMellinAdjacentBlock_logSample_lower_of_dyadicWeightedPrimeWindow_upper
criticalMellinAdjacentBlock_subpowerLower_of_dyadicWeightedPrimeWindow_subpowerUpper
riemannHypothesis_iff_exists_eventually_xiRectangularWeilLogCoefficient_subpowerLower
exists_eventually_xiRectangularWeilLogCoefficient_subpowerLower_of_dyadicWeightedPrimeWindow
```

## Boundary

This theorem does not prove `(2)`. The existing sharp-window theorem proves that the all-epsilon
form of `(2)` implies RH, so an unconditional proof of `(2)` is itself an RH proof. The positive
reformulation is precise: `(2)` is a single source inequality that simultaneously closes the sharp
Landau gate, the adjacent critical-Mellin source estimate, and the rectangular `Q_L` tail.

## Gates

- [x] exact integer-to-continuous dyadic window relation
- [x] pointwise sharp coefficient transfer
- [x] sharp-to-adjacent-block integral transfer
- [x] all-epsilon constant conversion
- [x] direct unbundled rectangular RH equivalence
- [x] direct dyadic-to-rectangular hypothesis discharge
- [ ] unconditional proof of the dyadic inequality
- [ ] RH
