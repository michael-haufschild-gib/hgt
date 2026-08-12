# Route-P adjacent-prime cofinal Feshbach assembly

- **ID:** `P-G84`
- **Stage:** `1-in-progress`
- **Type:** exact infinite physical block assembly
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `../../5-failed/route-p-complete-graph-multiplicity-no-go.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalAdjacentPrimeCofinalFeshbach.lean`

## Conjecture P-G84.A: canonical bounded incidence is summable

Use literal hostile harmonic aperture and consecutive primes

```text
p_n = nthPrime(n),  q_n = nthPrime(n+1),  e >= 0.
```

Retain P-G82's four-cell physical packet and raw Cauchy partition weight unchanged. Conjecture:
adjacent-prime denominator and numerator are absolutely summable over `(e,n)`, their cofinal Schur
fraction lies strictly in `(1/2,1)`, and the resulting physical residual remains positive and
strictly sub-half at every prime-power label.

**Verdict: true, unconditionally proved.**

## Paper proof

Let `delta = log(2)/2-a_crit > 0`. Exact boundary-rate separation gives a uniform denominator gap.
For an adjacent pair `p<q`, Bertrand's bound gives `q <= 2p`, hence `log(q) <= 2log(p)`. Each raw
Pluecker term is bounded by

```text
(9216 a_crit^2 / delta^4) * log(p)^2 / ((e+1/2)^2 p^4).
```

Summing six minors bounds partition mass. Total Fisher is bounded by
`(20/3)log(p)^2`. Consequently the denominator term is bounded by

```text
(368640 a_crit^2 / delta^4)
  * (e+1/2)^(-2) * log(p)^4 / p^4.
```

Depth majorant is a shifted `p`-series. Prime majorant is dominated by the natural-number series
`log(n)^4/n^4`. Their product is summable. P-G82's pointwise strict inequalities then give
summable positive lower and upper gaps:

```text
0 < N - D/2,    0 < D-N.
```

The denominator is positive, so cofinal fraction `N/D` lies in `(1/2,1)`. Absolute summability
makes this countable sum independent of finite exhaustion order.

## New knowledge

P-G83 and P-G84 separate two notions previously conflated:

```text
local packet positivity does not control incidence;
bounded incidence plus critical rate decay does control cofinal assembly.
```

Route P now has first exact infinite source-native physical Feshbach assembly. No fitted damping,
prime cutoff, numerical axiom, or conditional premise appears. Physical raw packet weights remain
literal. This closes infinite summability and exhaustion order for canonical adjacent-prime
packetization.

## Lean realization

Headline declarations:

- `gammaSewnCriticalAdjacentPrime_order`;
- `summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm`;
- `summable_gammaSewnCriticalAdjacentPrime_NumeratorTerm`;
- `hasSum_gammaSewnCriticalAdjacentPrime_CofinalNumerator`;
- `hasSum_gammaSewnCriticalAdjacentPrime_CofinalDenominator`;
- `gammaSewnCriticalAdjacentPrime_CofinalFraction_mem`;
- `gammaSewnCriticalAdjacentPrime_CofinalReducedWeight_mem`.

```text
lake build GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalAdjacentPrimeCofinalFeshbach
Build completed successfully (12736 jobs).
```

Capstone `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Next conjecture P-G85

Identify which part of P-G78's all-prime weak Köthe Gram kernel is represented by adjacent-prime
cofinal assembly. Required theorem must either:

1. derive adjacent incidence from global Gamma/polar Feshbach geometry and prove exact response
   equality; or
2. exhibit a nonzero de-duplication/flux-at-infinity defect, then construct and formalize the
   corrected source-forced incidence current.

Do not infer identification from positivity or absolute summability alone.

## Honest boundary

P-G84 does not identify adjacent path with P-G78's all-prime weak kernel, prove completed-seam
moment equality, supply archimedean/polar sewing, complete Julia saturation, or prove RH.
