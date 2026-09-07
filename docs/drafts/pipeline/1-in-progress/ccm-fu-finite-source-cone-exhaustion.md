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

For Re(w)>1, the exact Euler decomposition, now formal in Lean, is

`sum_d a_y(d)/d^w = P_y(w)/(zeta(w)*E_S(w))`,
`P_y(w)=sum_(R subset S) y(R)*mu(product R)*(product R)^(-w)`,
`E_S(w)=product_(p in S)(1-p^(-w))`.

The exact Mellin formula is formal with absolute convergence for Re(s)>2:

`integral_(1..infinity) H_y(x)*x^(-s-1) dx`
`= P_y(s-1/2)/E_S(s-1/2)`
`  *(-zeta'(s-1/2)/zeta(s-1/2)-zeta(s-1/2)+2*gamma)`
`  /(2*s*(s-1/2))`.

The candidate right side is formally analytic whenever Re(s)>1/2 and
|Im(s)|<=4, including the cancelled pole at s=3/2. More precisely, its
pullback by s=4-z is differentiable on every closed ball |z|<=R<7/2.
For a positive carrier centered at Mellin abscissa four, those balls are
the inputs to Landau transfer through Re(s)>1/2. The literal source transform and its initial domain are closed. Constructing
the positive measure and identifying its complex MGF germ are still necessary. The candidate
right side formally has surviving simple critical poles at unbounded height.

The corpus has an unconditional superlinear simple-critical-zero count and
a linear zero-count bound for any nonzero entire function of finite
exponential type. Applying these to `P_y(1/2+i*z)` forces P_y identically
zero. Distinct products of subsets of S and independence of their real
exponentials then force every coordinate of y to vanish. The same reasoning
applies to a nonpositive functional by negation.

The [spectral separation bridge](../3-formalized/ccm-fu-finite-retained-spectral-separation.md)
is unconditional in Lean. It closes coefficient injectivity, the exact
finite Möbius subset numerator, arbitrarily high simple-critical
nonannihilation, pole survival through finite Euler and integration-clock
denominators, and all required low-height Landau balls. Its 28 new public
declarations use only foundational axioms and no computational premises.

The [exact source-to-Mellin transport](../3-formalized/ccm-fu-retained-source-mellin-transport.md)
is closed in Lean. It proves the full weighted Euler identity, exact divisor
convolution and clipped square-root Abel pairing; the source-specific
summatory bound `24*(sum_R norm(y(R)))*N^(3/2)`; the absolutely convergent
Mellin identity on Re(s)>2; exact integer endpoints; and affine interpolation
in sqrt(x). Nonnegative real parts at all integer cutoffs therefore imply
nonnegative real part on the entire real ray. These are 43 public declarations
in five modules, without numerical premises.

Positive-measure construction, its complex MGF germ, Landau continuation
and the analytic identity needed for the pole contradiction remain open.
The arbitrary finite retained-source cone theorem is not yet claimed.

### Positive-carrier construction target

Use the absolute center-four density `norm(x^(-5)*H_y(x))` on the positive
ray and logarithmic variable `log(x)`. The density vanishes below one and
is integrable by the exact Mellin theorem, so the resulting measure is
finite and its logarithmic variable is nonnegative almost everywhere.
Real retained coordinates give a real primitive. Under the hypothesized
one-sided integer functional, exact interpolation makes the primitive
nonnegative, identifying the absolute density with the signed source.
Real exponential tilts then translate the Mellin exponent, and the complex
MGF germ is the existing continuation evaluated at `4-z`. This is the next
proof-facing bridge; no numerical experiment is needed for these identities.

### Closed arithmetic transport

For p outside S, set y0(R)=y(R) and y1(R)=y(insert p R).
Restrict each old weighted Möbius sequence to indices not divisible by p.
The new sequence is the first restriction minus the p-dilation of the
second. The old sequence itself is its restriction minus its p-dilation,
because Möbius vanishes on the repeated-prime terms. This gives the exact
recursion

`L(a_(insert p S),y) = (L(a_S,y0)-p^(-w)*L(a_S,y1))/(1-p^(-w))`.

The finite subset numerator has the matching recursion, and the empty
retained set is the ordinary Möbius series times y(empty). These identities
and absolute convergence on Re(w)>1 prove the infinite Euler identity. No numerical test is needed for these exact
coefficient and reindexing statements.

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
- `CCMSimplePrimeDivisorSource`: exact pole-filled `-zeta'/zeta-zeta`
  continuation and cancellation at the arithmetic pole.
- `FiniteDirichletCriticalNonannihilation`, `FiniteDirichletDivisorPoleSurvival`,
  `RetainedPrimeDirichletNumerator`: closed finite numerator and pole bridge.

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
