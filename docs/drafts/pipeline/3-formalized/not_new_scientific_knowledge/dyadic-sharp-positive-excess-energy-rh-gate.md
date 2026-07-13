# Positive-excess Dirichlet energy of one dyadic prime window proves RH

- **ID:** `dyadic-sharp-positive-excess-energy-rh-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / PROOF-BURDEN REDUCTION
- **Scientific status:** `[FORMALIZATION] [NOVELTY UNAUDITED] [NOT CLAIMED NEW] [RH-SUFFICIENT]`

## Statement

Put

```text
W(n)=sum_(n/2<k<=n) Lambda(k)/sqrt(k),
c=2(1-1/sqrt(2)),
E(n)=(W(n)-c*sqrt(n))_+.
```

The exact sharp source coefficient is

```text
S(n)=2(c*sqrt(n)-W(n)),
```

so its negative part satisfies the pointwise value relation

```text
S(n)_-=2E(n).                                             (1)
```

For `n>=2`, this is also the exact polar-free relation

```text
2E(n)=negativePart(
  sharpPrimeNormalizedChebyshevIncrement(log 2,log n)).   (1a)
```

Thus the energy target can be attacked directly on the normalized Chebyshev error and its causal
Volterra increment, without separately estimating the prime and square-root polar channels.

The following averaged condition already implies RH:

```text
for every epsilon>0,
  sum_(n>=1) E(n)/n^(1+epsilon) < infinity.               (2)
```

The Hilbert-facing square-energy condition

```text
for every epsilon>0,
  sum_(n>=1) E(n)^2/n^(1+epsilon) < infinity             (3)
```

also implies RH.

## Why this reduces the proof burden

The requested pointwise estimate `E(n)<=C_epsilon*n^epsilon` implies `(2)` after using a smaller
exponent. Condition `(2)` does not require a bound at every index: it permits sparse overshoots as
long as their weighted positive mass is summable. It also ignores the favorable half of the
oscillation completely. Thus the RH proof no longer needs the displayed pointwise inequality; it
is enough to prove an averaged one-sided cancellation law for its positive excess.

## Mechanism

By `(1)`, adding `2E(n)` to `S(n)` replaces the source coefficient by its positive part. The
corrected Dirichlet series therefore has nonnegative coefficients. Under false RH, the exact
continued sharp source has a positive-transverse pole. Landau transfer moves absolute convergence
of the corrected series left of that pole, while `(2)` keeps the correction series holomorphic
there. Subtracting the correction would make the original sharp source series converge across the
pole, contradicting its formally proved order deficit.

Condition `(3)` implies `(2)` by weighted Cauchy--Schwarz.

There is also an exact sparse-exception version.  For an arbitrary set `A` of apertures it is
enough to prove the pointwise subpower inequality on `A^c` and charge only

```text
sum_(n in A) E(n)/n^(1+epsilon)
```

on `A`, for every `epsilon>0`.  A finite uncontrolled prefix may be included in `A`.  Thus neither
uniform pointwise control nor a global mean estimate is mandatory; the two proof modes may be
combined aperture by aperture.

The exceptional energy can be made independent of the prime values.  Chebyshev's elementary
bound gives the unconditional envelope

```text
E(n)<=sqrt(2)*(log 4+4)*sqrt(n).                          (4)
```

Hence the pointwise inequality may be abandoned completely on any set `A` satisfying

```text
for every epsilon>0,
  sum_(n in A) n^(-1/2-epsilon)<infinity.                 (5)
```

For example, any fixed lacunary family has this property.  It remains enough to prove the
pointwise all-epsilon bound on the complement of `A`.

## Lean realization

The implementation is

```text
GaloisForLFunctions.RHTower.CCMSharpPrimeWindowExcessEnergyGate.
```

Principal declarations:

```text
dyadicSharpPrimeSourceNegativePart_eq_two_mul_positiveExcess
negPart_sharpPrimeNormalizedChebyshevIncrement_eq_two_mul_positiveExcess
riemannHypothesis_of_dyadicSharpPrimeSourceNegativePartEnergy
riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessEnergy
riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessSquareEnergy
riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpperOff
dyadicWeightedPrimeWindowPositiveExcess_le_halfPower
riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpperOff_halfPower
```

The theorem uses only source-defined finite von Mangoldt values, ordinary Dirichlet-series
summability, and the already formalized sharp-source continuation. It introduces no zero-defined
witness into the hypothesis.

## Boundary

Neither `(2)` nor `(3)` is proved unconditionally here. Each is a strictly more flexible target
than the original pointwise inequality, but each remains RH-bearing. A targeted search did not
locate this exact fixed-dyadic positive-excess criterion; this card makes no novelty claim until a
dedicated primary-literature audit is complete.

## Gates

- [x] exact positive-excess/source-negative-part relation
- [x] nonnegative Landau correction
- [x] correction continuation and two-stage Landau transfer
- [x] positive-excess Dirichlet-energy criterion
- [x] positive-excess square-energy criterion
- [x] sparse-exception pointwise/energy decomposition
- [x] unconditional square-root excess envelope
- [x] prime-independent half-power-thin exception criterion
- [x] direct unbundled theorem surfaces
- [ ] unconditional proof of `(2)` or `(3)`
- [ ] dedicated novelty audit
- [ ] RH
