# CCM-FU: finite retained-source cone and coverage

- **Stage:** 1-in-progress
- **Type:** [BRIDGE] / derived theorem candidate
- **Parent:** [complete adaptive prime ceiling](ccm-fu-adaptive-prime-ceiling.md)
- **Target:** Source-derived directional control on an arbitrary finite retained prime field, followed by coverage-compatible use of that control.

## Full proof chain

Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints
→ signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green
→ RH. Complete compatible source coverage under a uniform budget remains
the primary obligation. The [growing coupled batches](../3-formalized/ccm-fu-coupled-prime-batches.md)
control only the head/{2} plane after one fixed core; they leave other source
primes unprocessed. The present bridge does not replace that obligation.

## Frozen analytic bridge

For a finite set S of primes, classify each actual Möbius dilation channel
by `primeFactors(d) intersect S`. Let V_S(M) be the resulting complete field
on subsets of S. Equivalently, at any finite bound T>=M, process every prime
below T except S. The proposed bridge is that the positive cone of the actual
vectors V_S(M), over all integer cutoffs M, is the entire retained field.
Finite-dimensional compactness would then provide one finite source witness
and a uniform positive directional margin for this fixed S.

This is a derived theorem candidate selected from corpus source identities,
Landau transfer and zero-density machinery. It is not a new primary universal
conjecture. Its truth is not certified until the complete analytic transport
and unconditional Lean proof close.

## Proposed source-separation proof

For a real functional y on subsets of S, put

`a_y(d)=mu(d)*y(primeFactors(d) intersect S)`.

Write D(n) for the literal prime-free divisor defect. Its exact difference
is `D(n)-D(n-1)=log(n)-tau(n)+2*gamma`, for n>=1. Let

`A_y(x)=sum_(d<=x) a_y(d)*D(floor(x/d))`,
`H_y(x)=integral_(1..x) A_y(t)/(2*sqrt(t)) dt`.

At integer x=M, H_y(M) is exactly y paired with V_S(M). Between successive
integers it is affine in sqrt(x), so nonnegative integer values imply
nonnegativity on the whole real ray. No numerical source values enter.

For Re(w)>1, the proposed exact Euler decomposition is

`sum_d a_y(d)/d^w = P_y(w)/(zeta(w)*E_S(w))`,
`P_y(w)=sum_(R subset S) y(R)*mu(product R)*(product R)^(-w)`,
`E_S(w)=product_(p in S)(1-p^(-w))`.

The proposed Mellin formula, initially for Re(s)>3/2, is

`integral_(1..infinity) H_y(x)*x^(-s-1) dx`
`= P_y(s-1/2)/E_S(s-1/2)`
`  *(-zeta'(s-1/2)/zeta(s-1/2)-zeta(s-1/2)+2*gamma)`
`  /(2*s*(s-1/2))`.

The right side is holomorphic near every real s>1/2: finite Euler factors
do not vanish there, zeta has no positive-real zero, and the two poles at
s=3/2 cancel. A nonnegative H_y would therefore have Mellin convergence
through Re(s)>1/2 by Landau transfer. Every simple critical zero rho would
force `P_y(rho)=0` by the pole of the logarithmic derivative.

The corpus has an unconditional superlinear simple-critical-zero count and
a linear zero-count bound for any nonzero entire function of finite
exponential type. Applying these to `P_y(1/2+i*z)` forces P_y identically
zero. Distinct products of subsets of S and independence of their real
exponentials then force every coordinate of y to vanish. The same reasoning
applies to a nonpositive functional by negation.

Every formula and analytic passage above needs an exact proof; no unstated
Mellin interchange, pole cancellation, or coefficient injectivity is admitted.

## Corpus inputs located

- `MobiusDivisorCoupledTwoSourceCone` and `MobiusDivisorCoupledTwoPrimeBatches`:
  literal two-coordinate control and actual partial schedules.
- `LandauIntegralTransfer` and `MobiusLaplaceLandauOscillation`: positive
  integral-carrier continuation and pole contradiction mechanisms.
- `CCMRectangularTwoSidedOscillation`: positive Dirichlet coefficients and
  Landau continuation from one-sided source control.
- `XiSimpleCriticalExponentialTypeBound`: a finite-exponential-type
  annihilator gives a linear simple-critical-zero counting bound.
- `Zeta23SimpleCriticalDensity`: unconditional superlinear simple-critical
  census.
- `XiSimpleCriticalSuperlinearConsumer`: incompatibility of linear upper
  and superlinear lower counting bounds.

## Computation decision

No numerical experiment is scheduled. The candidate analytic mechanism
predicts full finite-dimensional source cones, so merely screening more
finite retained sets would not meet the requirement to compute only genuinely
unresolved, potentially surprising questions. If an analytic obstruction
changes this assessment, freeze a distinct discriminating question first.

## Coverage gate

Even a proof for every fixed S supplies no uniform control on witness cutoffs,
directional margins, clipping tolerances, prime-pool capacity or preparation
energy as S changes. Those quantities must be propagated through an actual
complete compatible schedule. Fixed-field cone fullness alone is not SD1,
the full adaptive ceiling or RH.
