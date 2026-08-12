# Route P: cofinal scalar compact-moment no-go (P-G89)

Status: failed route with quantitatively formalized positive survivor

## Conjecture

P-G84's cofinal residual scalar, applied coefficientwise to P-G72's information-depleted compact
prime-power carrier, might yield completed seam moments.

## Numerical pre-certification

Direct source-formula summation gives approximate values

```text
cofinal Schur fraction       0.5533376622456
cofinal residual             0.4466623377544
reduced carrier moment 0     0.0598...
reduced carrier moment 1     0.00105195...
```

Completed-source rigorous ceilings already in corpus are `29/625 = 0.0464` and
`9/50000 = 0.00018`. Both candidate moments are too large. Lean proof uses no computation.

## Verdict

False, already at first moment.

## Formal proof

File:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCofinalReducedMomentNoGo.lean`

Bertrand's adjacent-prime bound implies each complementary Fisher pair is at most `4/5` of its
four-rate total. Positive probability averaging and summation give

```text
cofinal fraction <= 4/5,
cofinal residual >= 1/5.
```

Sharper source-algebra bounds at prime `2`, depth `0` prove

```text
raw squared weight > 33/1000,
information-depleted weight > (17/20)(33/1000),
squared reciprocal-gap node > 4/121.
```

Consequently that single reduced atom has first moment greater than `9/50000`, while the entire
completed seam first moment is less than `9/50000`. Hence local compact Markov germ equality is
impossible.

Headline declarations:

- `gammaSewnCriticalAdjacentPrime_CofinalFraction_le_four_fifths`;
- `gammaSewnCriticalCofinalResidualFactor_ge_one_fifth`;
- `gammaSewnCriticalCofinalReducedPrimeTwoDepthZero_firstMoment_lower`;
- `normalizedPrimeArchMoment_one_lt_integral_gammaSewnCriticalCofinalReducedCarrier`;
- `not_gammaSewnCriticalCofinalReducedMomentIdentification`.

## Positive survivor: covariance-spectral noncommutation

P-G88 remains exact at covariance level. P-G89 proves its scalar cannot be pushed unchanged through
the reciprocal-gap spectral map. Global inverse incidence mixes prime coordinates, whereas compact
moments weight each label by powers of its node. Therefore one scalar can preserve covariance
normalization but cannot simultaneously calibrate spectral moments.

This obstruction first forced node dependence. P-G90 subsequently proves that node dependence is
still insufficient for every nonnegative diagonal transfer inheriting physical packet residuals.
The surviving requirement is genuinely non-diagonal coupling before compact spectral pushforward,
so poles move rather than only residues changing on the original nodes.

## No-go closure audit

Negative statement, quantitative residual floor, explicit offending atom, finite compact carrier,
and positive replacement principle are all formalized. Do not re-attempt uniform scalar transfer.
P-G90 records closure of its diagonal successor class.
