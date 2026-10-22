# Route-P all-prime information virial divergence

- **ID:** `P-G58`
- **Stage:** `1-in-progress`
- **Type:** nonlinear analytic-doublet no-go / global source-carrier exclusion
- **Status:** `[PAPER-PROVED] [LEAN DIRECT GREEN] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-information-wold-gauss-virial-bridge.md`
- **Corpus weld:** `MobiusLaplaceCriticalDilationNoGo`, `SectorPrimeZeroUniqueness`

## Conjecture

P-G55--P-G57 identify each local geometric-KL pressure with Burnol holonomy virial

```text
V(u)=u cosh(u)-sinh(u).
```

Test whether local finiteness survives all-prime gluing and supplies missing finite global source
norm.  Nonlinear unstable branch predicts opposite: valuation-one terms should already reproduce
P-G35 analytic-doublet divergence.

## Result

Lean proves sharp elementary lower bound

```text
u >= 2  ==>  exp(u)/4 <= V(u).                            (P-G58a)
```

At prime `p`, valuation-one physical information term is exactly

```text
K_p,1(t)=4 p^(-1) V(2t log p).                            (P-G58b)
```

For every `t>0`, prime escape makes `2t log p>=2` cofinitely.  Therefore

```text
1/p <= K_p,1(t)                                           (P-G58c)
```

cofinitely, and Euler prime-harmonic divergence gives

```text
not Summable_p K_p,1(t).                                  (P-G58d)
```

For physical strip `0<t<1/2`, every higher valuation term is nonnegative and prime-power series
sums to actual centered geometric KL chirality.  Hence

```text
K_p,1(t) <= KL_p(t),
not Summable_p KL_p(t).                                   (P-G58e)
```

## Conjecture loop verdict

### Conjecture P-G58.A

Use sum of local geometric KL divergences as finite all-prime Route-P source energy.

**Killed.** `(P-G58d)` and `(P-G58e)` prove valuation-one layer and complete per-prime KL are
nonsummable at every positive physical horizontal depth.

### Higher universal principle

P-G35 analytic doublet and P-G58 information geometry are linear and nonlinear shadows of same
Euler instability.  Local convexification does not regularize all-prime source gluing: unstable
reciprocal branch amplifies `p^-1` into `p^(-1+2t)` scale.  A viable producer must cancel that
branch before applying positive information/holonomy/Wold descendants; no positive descendant can
be globalized first.

## Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaRoutePAllPrimeInformationVirialDivergence.lean`

Headline declarations:

- `exp_div_four_le_sourceHorizontalHolonomyVirial`;
- `sourceHorizontalPrimeGeometricKLScaleTerm_zero_eq`;
- `eventually_one_div_prime_le_sourceHorizontalPrimeGeometricKLScaleTerm_zero`;
- `not_summable_sourceHorizontalPrimeGeometricKLScaleTerm_zero`;
- `sourceHorizontalPrimeGeometricKLScaleTerm_zero_le_chirality`;
- `not_summable_sourceHorizontalPrimeGeometricKLChirality`.

## Honest boundary

P-G58 is not RH.  It produces new global impossibility theorem and removes information geometry
as finite source carrier; it does not construct pre-completion cancellation.

## Next hard gate

Search coefficient-faithful signed precursor before positive descendant chain.  Required object
must cancel valuation-one unstable branch without discarding Euler coefficients, retain exact
Gamma completion, and land in existing global reflection-defect equality.  First test:
nonabelian relative-index pairing or signed determinant curvature whose local logarithm contains
both reciprocal branches before taking norm/KL.
