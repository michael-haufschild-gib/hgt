# Paying the outside mass of a Turán cluster

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** Remove the outside-mass premise in the bounded-cluster camera;
  test its consequences for A78 and clustered zero visibility.

## Question

`TheTuranCameraSeesBoundedClusters` detects an arbitrary cluster of at most
`N` zeros without internal separation, provided its exterior weighted
mass is smaller than the Turán signal. Can existing local-count, depth,
annular-gap, or cancellation estimates prove that bound for actual ζ?

## Constraint

A proof must pay the explicit loss `turanConstant N M`; a bound with an
uncontrolled constant or a renamed outside-mass premise does not suffice.
The existing inverse-square deep-ordinate leakage bound and the
sector-coherent Turán theorem are the initial connection to test.

## Checked partial discharge

`TheStripPaysTheVeryDeepCameraNoise` removes the low-centre mass premise
from the hyperbolic camera when `3c log T≤(1-3c)α`: choose
`A=(1-3c)α/2`, so the putative very-deep zeros have depth greater than
`A/(3c log T)≥1/2` and do not exist. The Blaschke-product condition remains.

## Width-centered camera

Let `b=zetaZeroWidth` and replace `K(u)` by `e^(-bu)K(u)`.
Every zero has relative depth at most zero. Its transform is bounded by
`profileMass(v)/(1+δ²(γ-t)²)` at positive lags `y≥δ`.
If only the exterior zeros of depth at least `b-d` have ordinate gap `g`,
their complete norm mass is bounded by

`profileMass(v) [(1+g²)/(δ²g²)+exp(-d(y-δ))] lorentzMass(t)`.

The unit-scale mass is proved `O(log |t|)`. Thus fixed positive `g,d`,
`δ≈log T`, and `y-δ≈log T` make the exterior bound tend to zero.
A sector cluster of at most `N` zeros within `η` of the top retains signal
`(∫v)/2 · κ(N,M) exp(-η((M+N)h+δ))`, without internal separation.

Centering has a controlled prime cost: the mean square acquires
`exp(-2b(y-δ))`; the constant is uniform in `b` and the centre.
The exterior-mass module is checked in Lean. The near-top Turán receiver,
prime cost, and explicit-formula remainder are written, not yet checked.

## Remaining

Track the centered explicit-formula remainder for a density consequence.
The exterior estimate removes an analytic mass premise, but does not yet
prove the required sector-cluster and deep-gap geometry for actual ζ.
It therefore does not close A78 in full.
