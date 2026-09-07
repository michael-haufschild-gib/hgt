# CCM-FU: finite source control and cofinal coverage

- **Stage:** 1-in-progress
- **Type:** [BRIDGE] / source-production target
- **Parent:** [complete adaptive prime ceiling](ccm-fu-adaptive-prime-ceiling.md)
- **Closed:** Arbitrary finite-field directional control, exact actual-state/energy transport, common-parent prime supply, and arbitrarily long bounded batches with a complete finite preparation budget.
- **Open:** Quantitative transport of those witnesses through changing retained fields and complete compatible cofinal coverage under one energy budget.

## Full proof chain

Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints
→ signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green
→ RH. The primary obligation remains complete compatible source coverage
under a uniform budget. The [growing coupled batches](../3-formalized/ccm-fu-coupled-prime-batches.md)
control the head/{2} plane after one fixed core and leave other source primes
unprocessed. Arbitrary finite-field source control is now formal; using it
within an exhaustive admissible history remains necessary.

## Closed finite-field source theorem

For any finite set S of primes, group every actual Möbius dilation channel
by `primeFactors(d) intersect S`. Let V_S(M) be the complete resulting vector
on all subsets of S at integer cutoff M. Its directional pairing is exactly

`<y,V_S(M)>=sum_(d<=M) y(primeFactors(d) intersect S)*C_d(M)`.

The [finite retained-source certificate](../3-formalized/ccm-fu-finite-retained-directional-control.md)
proves that every nonzero real direction has actual cutoffs with both strict
signs. There are a nonempty finite cutoff family K and c>0 such that every
direction y has some M in K with `<y,V_S(M)> >= c*norm(y)`.

There are also a common `0<delta<=1` and positive margin for independently
clipped profiles `(1-clip(M))*V_S(M)+clip(M)*V_S(M+1)`, whenever
`0<=clip(M)<=delta`. These are complete actual profiles, with their coordinate
pairing identified in Lean. The theorem is uniform over directions and clips
for this fixed S; it has no uniform-in-S assertion.

## Closed arithmetic and analytic chain

For a real retained functional y, define

`f_y(d)=mu(d)*y(primeFactors(d) intersect S)`,
`P_y(w)=sum_(R subset S) mu(product R)*y(R)*(product R)^(-w)`,
`E_S(w)=product_(p in S)(1-p^(-w))`.

The exact weighted series is `L(f_y,w)=P_y(w)/(zeta(w)*E_S(w))`, absolutely
convergent on Re(w)>1. Its convolution g_y with the literal divisor increment
has summatory norm bounded by `24*(sum_R norm(y(R)))*N^(3/2)`. The continuous
primitive H_y is its square-root Abel integral, agrees exactly with every
integer source pairing, and is affine in sqrt(x) between consecutive cutoffs.
Its exact absolutely convergent Mellin expression on Re(s)>2 is

`M_y(s)=P_y(s-1/2)/E_S(s-1/2)`
` *(-zeta'(s-1/2)/zeta(s-1/2)-zeta(s-1/2)+2*gamma)`
` /(2*s*(s-1/2))`.

The [source-to-Mellin transport](../3-formalized/ccm-fu-retained-source-mellin-transport.md)
proves these statements with every clipped endpoint retained. The
[spectral bridge](../3-formalized/ccm-fu-finite-retained-spectral-separation.md)
proves literal numerator injectivity, arbitrarily high surviving simple
critical poles at s=1+it, and low-height closed-ball analyticity of M_y(4-z).

A hypothesized one-sided functional gives a real nonnegative H_y. The finite
positive measure with density `norm(x^(-5)*H_y(x))` has nonnegative logarithmic
variable and exact complex MGF germ M_y(4-z). Landau transfer through radius
13/4 makes its reconstructed Mellin transform analytic on Re(s)>3/4. The
meromorphic discrepancy vanishes near four and hence has infinite order
everywhere on that connected half-plane. Its surviving order -1 pole is
impossible, forcing y=0. Negation gives both strict signs. Compactness of the
finite coordinate unit sphere extracts K and c; finite source-mass bounds
give the common clipping tolerance.

The positive measure, MGF germ, Landau transfer, continuation identity,
directional separation, finite witness extraction and clipping stability are
closed. No numerical source values or zero-location assumptions enter.

## Coverage gate

The [actual arbitrary-field batch theorem](../3-formalized/ccm-fu-arbitrary-retained-prime-batches.md)
closes partial-state identification and the complete energy pairing. For every
finite retained field S it constructs a fixed complementary core P and, at
arbitrarily late parent cutoffs M, distinct actual prime batches of any
prescribed finite length. Every subset used to prepare P has energy at most
`722*2^|P|*M^2`; every batch prefix stays below the prepared energy. All
retained coordinates are included, and actual common-parent prime windows
have the prescribed quotients and clipping bounds. The budget depends on S.

The [support and common-head bridge](ccm-fu-retained-support-cost.md) gives
necessary full-field witness costs and exact source correlations. Possible
actual labels have product below M and number at most M-1. All coordinates
are product-scale samples of one coprime-to-product(S) head, and the full
prepared energy is its exact product-weighted sum of squares. Complete
ambient-direction witnesses must extend beyond product(S), or beyond
q*product(S) when all primes below q are retained. This is an aperture cost,
not an energy lower bound.

No uniform upper bound yet controls max(K), inverse margins, clipping
tolerances, prime-window capacity or preparation energy as S grows. The
common head also changes with S; its joint arithmetic and scale control
remains the source-production target.
The exact state identification, copied prime-window profiles and every
finite preparation step are now controlled for fixed S. The remaining
obligation is to keep these costs within one parent energy budget as S
changes and every active source prime is eventually processed.

Processing the core first is not an admissible default: the existing middle
singleton obstruction forces superquadratic energy and survives arbitrary
scalar reserves. Arbitrary-field control must be propagated through genuine
nonisolated interleavings before that state forms. Existence of finite
witnesses for each S does not by itself construct the required exhaustive
cofinal schedule.

## Computation decision

No numerical experiment is scheduled. The qualitative finite-field question
is answered by the Lean source theorem. Screening more fixed retained sets
would not resolve the missing uniform costs and would have a predicted
outcome. Any future experiment must isolate an unresolved quantitative
mechanism that can discriminate actual coverage strategies; freeze that
question under the scientific-method rules before computing on RunPod.

## Current Lean sources

- `RetainedPrimeMobiusEulerIdentity`, `RetainedPrimeDivisorConvolution`:
  complete weighted arithmetic source and exact convolution.
- `SquareRootSummatoryMellin`, `RetainedPrimeSourceMellin`,
  `RetainedPrimeSourceInterpolation`: actual Mellin transport and endpoints.
- `RetainedPrimeLandauCarrier`, `FiniteDirichletMellinContinuationObstruction`,
  `RetainedPrimeLandauSeparation`, `RetainedPrimeFiniteSourceMargin`:
  positive carrier, pole contradiction and finite clipping-stable witnesses.
- `MobiusDivisorCoupledTwoSourceCone`, `MobiusDivisorCoupledTwoPrimeBatches`:
  explicit actual two-coordinate prime-window and partial-schedule transport.
- `RetainedPrimeStateTransport`, `RetainedPrimeDescentOrders`,
  `RetainedPrimeWindowSupply`, `RetainedPrimeBoundedBatches`: exact arbitrary
  finite-field state/energy transport, safe actual pool orders, common-parent
  growing supply, and unconditional batches with complete preparation bounds.

Complete coverage, PE4/PE4G/PE4C, SD1 and RH remain open.
