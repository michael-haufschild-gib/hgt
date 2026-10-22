# Xi thermal-limit--prime square-energy spectrum

- **ID:** `xi-thermal-prime-square-energy-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOVELTY NOT ASSERTED]`
- **Statement:** A positive-transverse Xi divisor simultaneously creates a strict thermal/source
  value defect and exact exponent-doubled lower bounds for the square-sampled prime overshoot,
  even though all finite KMS systems and their thermodynamic limit remain positive.

## Main law

Let

```text
E(n) = (sum_(n/2<k<=n) Lambda(k)/sqrt(k)
        - 2*(1-1/sqrt(2))*sqrt(n))^+,

sigma_1 = abscissa(m |-> E(m^2)),
sigma_2 = abscissa(m |-> E(m^2)^2).
```

For a positive-transverse multiplicity copy `q` of a Xi zero `rho`, let

```text
lambda_q = xiZeroCopyReciprocalSquare(q),
delta_q  = Re(rho)-1/2 > 0.
```

Lean proves the atomwise collision

```text
0 < Im(lambda_q)^2,
2*Re(rho)   <= sigma_1,
4*Re(rho)-1 <= sigma_2.                                  (1)
```

Consequently, if the positive-transverse Xi divisor is nonempty and
`delta = xiRightTransverseSup`, then

```text
1 + 2*delta <= sigma_1,
1 + 4*delta <= sigma_2.                                  (2)
```

The thermodynamic value law holds simultaneously.  The explicit finite reciprocal-Xi systems
are KMS/Wightman moment sequences for every cutoff `M`, and their second moments converge to the
canonical positive thermal value `M_2`.  Their complete pointwise limit lies unconditionally in
the closed trace--Hankel cone.  Under the same explicit nonempty-divisor input,

```text
normalizedPrimeArchMoment(1) < M_2.                       (3)
```

The strictness is constructive at the divisor level: one supplied copy `q` gives a positive
summand in the convergent orientation energy, rather than being obtained indirectly from
`not RiemannHypothesis`.

## Quantitative source-saturation budget

Define the unconditional finite sixth reciprocal mass

```text
M_6 = sum_q ||xiSpectralPoint(q)^(-1)||^6.
```

For every global Xi half-plane width `alpha`, Lean proves the pointwise and summed estimates

```text
Im(lambda_q)^2 <= 4*alpha^2*||xiSpectralPoint(q)^(-1)||^6,
M_2-normalizedPrimeArchMoment(1) <= 4*alpha^2*M_6.          (4)
```

In particular, the intrinsic transverse radius satisfies the unconditional value law

```text
M_2-normalizedPrimeArchMoment(1)
  <= 4*xiRightTransverseSup^2*M_6.                         (5)
```

The prime square-energy abscissae feed this budget directly:

```text
sigma_1 <= 1+2*alpha  -> M_2-source(1) <= 4*alpha^2*M_6,
sigma_2 <= 1+4*alpha  -> M_2-source(1) <= 4*alpha^2*M_6.   (6)
```

Eliminating the transverse radius between `(2)` and `(5)` gives a direct value-to-exponent law:

```text
1 + sqrt((M_2-source(1))/M_6)   <= sigma_1,
1 + 2*sqrt((M_2-source(1))/M_6) <= sigma_2.                (7)
```

Here `M_6` is unconditionally finite and strictly positive.  Thus any positive thermodynamic
source mismatch forces a quantitatively positive prime-energy abscissa excess, without choosing
an off-line zero or retaining an intermediate divisor-width parameter.

At `alpha=0`, either critical abscissa bound therefore proves
`M_2 <= normalizedPrimeArchMoment(1)`.  This is exactly the reverse operator-state inequality and
hence proves RH through the already formalized thermal equivalence.

## Finite-system burden reduction

The explicit finite KMS second moments `m_N(1)` already converge unconditionally to `M_2` and
satisfy `m_N(1) <= M_2`.  Therefore Lean proves the exact one-sided criteria

```text
RH <-> eventually_N m_N(1) <= source(1),

RH <-> for every epsilon>0,
      eventually_N m_N(1) <= source(1)+epsilon.            (8)
```

Consequently, a physical or arithmetic argument need not identify a thermodynamic limit with the
source, construct one finite system carrying all source moments, or control the full moment tower.
It is enough to give a vanishing-error upper cap for the second moment of the growing finite
systems.  Finite KMS realizability and closed-cone persistence are already unconditional.

## Positive interpretation

Finite KMS positivity and closedness under pointwise thermodynamic limits hold on every Xi fibre.
They are therefore unconditional producers of the trace--Hankel cone, including fibres carrying
off-critical zeros.  Equations `(1)`--`(3)` identify the extra datum positively:

```text
source-value saturation = vanishing orientation = critical exponent collapse.
```

Thus the physical construction problem is no longer the realization of one infinite source
moment sequence by one finite system.  Growing finite systems are sufficient.  The remaining
physics obligation is value convergence to the continued prime--Gamma source, and already its
second coordinate must saturate the unconditional lower bound.

## RH proof impact

The theorem discharges the finite-system realization, KMS positivity, and persistence of
trace--Hankel positivity in the thermodynamic limit.  It closes the formal gap between that
operator-state construction and the square-sampled prime obstruction in both directions relevant
to an RH proof: a positive-transverse atom forces both defects, while a prime-energy abscissa upper
bound quantitatively forces thermal/source saturation through `(6)`.

Two positive sufficient proof obligations remain available:

```text
M_2 <= normalizedPrimeArchMoment(1),
sigma_1 <= 1   or   sigma_2 <= 1.
```

The first forces thermal/source saturation.  Either prime bound now discharges the first
automatically.  The present theorem does not prove one of these upper bounds and hence is not an
RH proof.

## Lean certificate

Formalization:

```text
formal/GaloisForLFunctions/RHTower/CCM/CCMSharpPrimeWindowSquareEnergySpectrum.lean
formal/GaloisForLFunctions/RHTower/XiThermalPrimeSquareEnergySpectrum.lean
```

Principal declarations:

- `xiRightZeroCopy_thermalOrientationTerm_pos`
- `xiRightZeroCopy_thermalPrimeSquareEnergySpectrum`
- `xiThermalOrientationEnergy_pos_of_nonempty_xiRightZeroCopy`
- `sequenceTraceHankelNonnegative_xiThermalPositiveMoment`
- `summable_xiThermalCubicReciprocalMass`
- `xiThermalCubicReciprocalMass_pos`
- `xiThermalOrientationEnergy_le_cubicReciprocalMass_of_halfPlaneBound`
- `xiThermalSourceGap_le_intrinsicTransverseCubicBudget`
- `one_add_sqrt_normalized_xiThermalSourceGap_le_squarePrimeWindowPositiveExcess_abscissa`
- `one_add_two_mul_sqrt_normalized_xiThermalSourceGap_le_squarePrimeWindowPositiveExcessSquare_abscissa`
- `xiThermalTruncation_one_le_secondMoment`
- `riemannHypothesis_iff_eventually_xiThermalTruncation_one_le_source`
- `riemannHypothesis_iff_eventually_xiThermalTruncation_one_le_source_add_eps`
- `xiThermalSourceGap_le_of_squarePrimeWindowPositiveExcess_abscissa`
- `xiThermalSourceGap_le_of_squarePrimeWindowPositiveExcessSquare_abscissa`
- `xiThermalSecondMoment_le_source_of_squarePrimeWindowPositiveExcess_abscissa_le_one`
- `xiThermalSecondMoment_le_source_of_squarePrimeWindowPositiveExcessSquare_abscissa_le_one`
- `riemannHypothesis_of_squarePrimeWindowPositiveExcess_abscissa_le_one`
- `riemannHypothesis_of_squarePrimeWindowPositiveExcessSquare_abscissa_le_one`
- `one_add_two_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcess_abscissa`
- `one_add_four_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcessSquare_abscissa`
- `xiThermalLimit_primeSquareEnergySpectrum`

Both focused modules build successfully.  `#print axioms` for the global square-spectrum laws and
the thermodynamic-limit master theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`; there are no project axioms, proposition interfaces, `sorryAx`, or unproved
hypotheses.

## Gates

- [x] 0 → 1: exact atomwise thermal/prime collision identified
- [x] 1 → 2: paper proof includes the quadratic source-saturation budget
- [x] 2 → 3: Lean modules built and trust surface checked
- [ ] 3 → 4: publication treatment and independent novelty audit
- [ ] RH: prove source saturation or a critical square-energy upper bound
