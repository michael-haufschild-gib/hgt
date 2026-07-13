# The dyadic RH window is unchanged after removing proper prime powers

- **ID:** `dyadic-prime-only-window-reduction`
- **Stage:** 3-formalized
- **Type:** VALUE RELATION / PROOF-BURDEN REDUCTION
- **Scientific status:** `[FORMALIZATION] [POSITIVE STATEMENT] [CLASSICAL INPUT] [NOT AN RH PROOF]`

## Statement

Write

```text
W(n) = sum_(n/2 < k <= n) Lambda(k)/sqrt(k),
P(n) = sum_(n/2 < p <= n) log(p)/sqrt(p),
H(n) = W(n)-P(n).
```

Lean proves the exact positive splitting

```text
W(n)=P(n)+H(n),
0<=H(n),
H(n)<=2*sqrt(2)*log(n)                 (n>=1).
```

The last estimate is unconditional.  On the dyadic interval, `k^(-1/2)` is at most
`sqrt(2)*n^(-1/2)`.  Chebyshev's elementary proper-prime-power estimate

```text
psi(n)-theta(n)<=2*sqrt(n)*log(n)
```

then gives the displayed logarithmic bound.  In particular, for every `epsilon>0`,

```text
H(n)<=(2*sqrt(2)/epsilon)*n^epsilon.
```

It follows with unchanged eventual and all-epsilon quantifiers that

```text
W(n)<=2*(1-1/sqrt(2))*sqrt(n)+C_epsilon*n^epsilon
```

is equivalent to the same assertion with `W(n)` replaced by the prime-only value `P(n)`.  Hence
the prime-only assertion already implies RH through the existing sharp-window theorem.

## Theta value relation

Let

```text
E_theta(x)=theta(x)-x.
```

The prime-only window also satisfies the exact Abel relation

```text
P(n)=2*(1-1/sqrt(2))*sqrt(n)+D_theta(n),
```

where

```text
D_theta(n)
 = E_theta(n)/sqrt(n)-E_theta(n/2)/sqrt(n/2)
   +(1/2)*(integral_1^n E_theta(t)t^(-3/2)dt
            -integral_1^(n/2) E_theta(t)t^(-3/2)dt).
```

Thus the remaining estimate can be attacked entirely through two theta values and one local
critical-Mellin primitive.  No proper prime power, Xi zero, or bundled proposition interface
remains in this source obligation.

## Lean implementation

The implementation is

```text
GaloisForLFunctions.RHTower.CCMSharpPrimeWindowPrimeReduction
```

with principal declarations

```text
dyadicWeightedPrimeWindow_eq_primeOnly_add_higherPrimePower
dyadicWeightedHigherPrimePowerWindow_le_log
dyadicWeightedHigherPrimePowerWindow_le_subpower
dyadicWeightedPrimeWindowSubpowerUpper_iff_primeOnly
riemannHypothesis_of_eventually_dyadicWeightedPrimeOnlyWindow_upper
criticalMellinError_thetaCoefficient
dyadicWeightedPrimeOnlyWindow_eq_main_add_thetaErrorIncrement
dyadicWeightedPrimeOnlyWindow_upper_iff_thetaErrorIncrement
dyadicWeightedPrimeWindowSubpowerUpper_iff_thetaErrorIncrement
riemannHypothesis_of_eventually_dyadicCriticalThetaMellinErrorIncrement_upper
```

The exact module compiles.  The reduction claims no unconditional proof of the remaining
prime-only theta-error estimate; that estimate is still RH-bearing.

## Gates

- [x] exact prime/proper-prime-power splitting
- [x] unconditional logarithmic bound for the proper-prime-power channel
- [x] all-epsilon equivalence to the prime-only window
- [x] direct prime-only hypothesis-to-RH theorem
- [x] exact theta-error Abel value relation
- [x] all-epsilon equivalence to a single one-sided theta-error increment estimate
- [x] direct theta-error-increment hypothesis-to-RH theorem
- [x] exact module build
- [ ] unconditional subpower upper bound for the theta-error increment
