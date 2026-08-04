# Prime-depth BV--Wold singular depth lowering

- **ID:** prime-depth-bv-wold-singular-depth-lowering
- **Stage:** 3-formalized
- **Type:** THEOREM / CROSS-ROUTE SYNTHESIS / SOURCE-GRAPH CLASSIFIER
- **Formal module:** `GaloisForLFunctions/RHTower/PrimeDepthBVWoldSingularDepthLowering.lean`

## Theorem

Let

```text
L_e(rho,p) = log A_(p,e)(rho) + r(p),
r(p) = 2 log(p)/p^2.
```

Define source-pointed inverse-Wold transport

```text
B_r(f)(p) = p (f(p)-r(p)) + r(p).
```

Then, unconditionally,

```text
B_r(L_(e+1)(rho)) = L_e(rho).
```

The depth-two family `L_2(rho)` is summable for every Xi divisor.  Its image under the singular
affine lowering lies in the same trace-class sequence space exactly when
`Re(rho)=1/2`.  Equivalently,

```text
L_2(rho) in Dom(B_r : l1 --> l1)  iff  Re(rho)=1/2.
```

The universal divisor statement is equivalent to RH.  This is a classifier, not the missing
source-side proof of domain admission.

## New knowledge

The recent route atlas asked for a singular, source-pointed, adjacent-grade, off-diagonal graph
landing.  Wold depth identifies its analytic normal form:

- depth raising multiplies anomaly by `p^-1` and regularizes it into Schatten-1;
- informative inverse transport is the unbounded prime multiplier;
- physical/unit-double remainder is an affine basepoint and must be subtracted before lowering;
- criticality is domain invariance across the `2 -> 1` Schatten wall.

This unifies boundary-completeness singularity, Hellinger adjacent-grade landing, Route-R Wold
depth, and physical trace cancellation without serializing their detectors.  Remaining producer
is now concrete: construct source-derived depth-two carrier and prove it lies in graph domain of
`B_r` before selecting a divisor.

## Lean certificate

- `prime_mul_woldCoeff_succ`
- `primeDepthBVWoldRenormalizedDepthLowering_relativeLogCoefficient`
- `summable_primeDepthBVWoldXiRelativeLogCoefficient_two`
- `summable_renormalizedDepthLowering_relativeLogCoefficient_two_iff`
- `relativeLogCoefficient_two_mem_renormalizedDepthLoweringTraceDomain_iff`
- `primeDepthBVWoldXiSingularDepthLoweringLanding_iff_riemannHypothesis`

All proofs unconditional.  Axiom/build/lint audit recorded after targeted module verification.
