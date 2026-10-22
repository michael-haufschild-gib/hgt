# Perfect-square sampling preserves the dyadic sharp RH inequality

- **ID:** `dyadic-sharp-quadratic-sampling-law`
- **Stage:** 3-formalized
- **Type:** VALUE RELATION / PROOF-BURDEN REDUCTION
- **Scientific status:** `[FORMALIZATION] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`

## Main law

Put

```text
W(n) = sum_(n/2 < k <= n) Lambda(k)/sqrt(k),
c = 2*(1-1/sqrt(2)).
```

Lean proves that the eventual all-epsilon estimate

```text
W(n) <= c*sqrt(n) + C_epsilon*n^epsilon
```

is equivalent to its restriction to perfect squares:

```text
W(m^2) <= c*m + C_epsilon*(m^2)^epsilon.
```

A square-sample bound from `m>=M` extends to every `n>=M^2`, after changing only the
epsilon-dependent constant.  Hence the square samples alone discharge the existing dyadic
prime-window RH gate.

## Exact stability mechanism

For `N=(floor(sqrt(n))+1)^2`, one has

```text
n <= N,
N-n <= 2*floor(sqrt(n))+1.
```

The window at `n` is contained in the window at `N` together with the lower boundary slice
`n/2 < k <= N/2`.  The elementary bound `Lambda(k)<=log(k)` gives the formal pointwise estimate

```text
W(n) <= W(N) + 3*sqrt(2)*log(N).
```

Also `sqrt(N)-sqrt(n)<=1` and `N<=4n`.  Applying the square-sample estimate at exponent
`epsilon/2` and `log N=O_epsilon(n^(epsilon/2))` proves the full estimate at exponent `epsilon`.

## Prime-only and theta strengthening

The square restriction composes exactly with the previously formalized removal of proper prime
powers.  Thus the square-sample condition is unchanged when `W(m^2)` is replaced by

```text
P(m^2) = sum_(m^2/2 < p <= m^2) log(p)/sqrt(p).
```

The remaining condition is also equivalent to a value relation only for the prime Chebyshev
error `theta(x)-x`:

```text
dyadicCriticalThetaMellinErrorIncrement(m^2)
  <= C_epsilon*(m^2)^epsilon.
```

Therefore this one-sided theta-error increment bound at perfect squares already proves RH.  No
proper prime powers and no nonsquare apertures remain in that source obligation.

## Rectangular-source strengthening

The square restriction also composes with the exact diagonal-derivative reading of the
rectangular prime--polar source.  It is enough to prove the source slope lower bound only at
`n=m^2`:

```text
2*(sqrt(2)-1)/m-C_epsilon*(m^2)^epsilon
  <= dyadicAdjacentBlockDiagonalRightSlope(m^2).
```

There is a second axiom-clean capstone with the corresponding explicit width-only correction for
`dyadicPrimePolarSourceDiagonalRightSlope(m^2)`.  Either square-only slope estimate implies the
full prime-window estimate and hence RH.

## Lean implementation

The axiom-clean implementation is

```text
GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowSquareSampling
```

with principal declarations

```text
dyadicWeightedPrimeWindow_le_upperSquare
dyadicWeightedPrimeWindow_le_upperSquare_add_log
eventually_dyadicWeightedPrimeWindow_upper_of_squareSamples
eventually_dyadicWeightedPrimeWindow_upper_iff_squareSamples
squareSample_dyadicWeightedPrimeWindow_upper_iff_primeOnly
squareSample_dyadicWeightedPrimeOnlyWindow_upper_iff_thetaErrorIncrement
eventually_dyadicWeightedPrimeWindow_upper_iff_squareThetaErrorIncrement
riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_square_upper
riemannHypothesis_of_eventually_squareThetaErrorIncrement_upper
riemannHypothesis_of_eventually_squareAdjacentBlockDiagonalRightSlope_lower
riemannHypothesis_of_eventually_squarePrimePolarSourceDiagonalRightSlope_lower
```

## Significance boundary

This removes almost all aperture values and every proper prime power without weakening the RH
gate.  It does not estimate the remaining square samples.  The mechanism is an elementary local
stability bridge and is not claimed as new scientific knowledge.

The integer-polynomial trace-Hankel criterion uses polynomials as test vectors; the square
aperture `m^2` here is an arithmetic sampling index.  The two uses of polynomial structure are not
currently connected by a Lean theorem, so this card does not claim that the `Q(P)` criterion
supplies the square-sample estimate.

## Gates

- [x] exact square-sampling relation isolated
- [x] pointwise square-window stability formalized in Lean
- [x] all-epsilon square-sample equivalence formalized in Lean
- [x] proper-prime-power channel removed on the square samples
- [x] square-sampled theta-error equivalence formalized in Lean
- [x] direct square-sample-to-RH capstones formalized
- [x] square-only rectangular-slope-to-RH capstones formalized
- [x] focused module build
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formal lint and generated-index checks
- [ ] unconditional square-sampled theta-error upper bound
