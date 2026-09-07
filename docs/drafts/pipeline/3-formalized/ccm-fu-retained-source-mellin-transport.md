# CCM-FU: exact retained-source Mellin transport

- **Stage:** 3-formalized
- **Type:** [BRIDGE] / derived theorem
- **Parent:** [finite source cone and coverage](../1-in-progress/ccm-fu-finite-source-cone-exhaustion.md)
- **Result:** The complete literal retained source has the exact completed-source Mellin transform, with absolute convergence, exact integer endpoints and one-sided interpolation.

## Scope

Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints
→ signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green
→ RH. This theorem supplies the arithmetic and integral transport for the
[spectral separation bridge](ccm-fu-finite-retained-spectral-separation.md).
Positive-carrier continuation, arbitrary finite-field cone fullness and
complete compatible source coverage under one uniform energy budget remain open.

## Exact statements

For a finite set S of primes and arbitrary complex coordinates y(R), put

`f_y(d)=mu(d)*y(primeFactors(d) intersect S)`,
`P_y(w)=sum_(R subset S) mu(product R)*y(R)*(product R)^(-w)`,
`E_S(w)=product_(p in S)(1-p^(-w))`.

The complete weighted Möbius series is absolutely convergent for Re(w)>1:

`L(f_y,w)=P_y(w)/(zeta(w)*E_S(w))`.

Let D be the literal prime-free divisor defect and let b(n) be its actual
increment `log(n)-tau(n)+2*gamma` for n>=1, with zero at n=0 in the arithmetic
function representation. Let g_y=f_y*b be their Dirichlet convolution. Then

`sum_(n<=N) g_y(n)=sum_(d<=N) f_y(d)*D(floor(N/d))`,
`sum_(d<=M) y(primeFactors(d) intersect S)*C_d(M)`
`=sum_(k=1..M-1)(sqrt(k+1)-sqrt(k))*sum_(n<=k)g_y(n)`.

Here C_d(M) is the complete literal Möbius dilation channel. The endpoint
at d=M vanishes exactly; no cutoff correction is discarded. For Re(w)>3/2,
absolute convolution and exact Möbius inversion give

`L(g_y,w)=P_y(w)/E_S(w)*(-zeta'(w)/zeta(w)-zeta(w)+2*gamma)`.

Define A_y(t)=sum_(n<=floor(t))g_y(n) and

`H_y(x)=integral_(1..x) A_y(t)/(2*sqrt(t)) dt` for x>=1,

with H_y(x)=0 below one. Its construction is a multiplicative convolution
of the weighted summatory profile with the indicator of (1,infinity).
The source-specific bound is unconditional:

`norm(sum_(n<=N)g_y(n)) <= 24*(sum_(R subset S)norm(y(R)))*N^(3/2)`.

For Re(s)>2, H_y therefore has the absolutely convergent Mellin transform

`integral_(1..infinity) H_y(x)*x^(-s-1) dx`
`=P_y(s-1/2)/E_S(s-1/2)`
` *(-zeta'(s-1/2)/zeta(s-1/2)-zeta(s-1/2)+2*gamma)`
` /(2*s*(s-1/2))`.

This is exactly the previously defined `finiteDirichletDivisorMellin`, with
its pole-filled continuation, matching prime set and literal constant.
Re(s)>2 is sufficient for its germ at four; no sharper initial domain is
claimed here.

At every integer M, H_y(M) is exactly the displayed source pairing. For
k>=1 and k<=x<=k+1,

`H_y(x)=H_y(k)+(sqrt(x)-sqrt(k))*A_y(k)`.

Consequently, if the real parts of all integer source pairings are
nonnegative, Re(H_y(x)) is nonnegative throughout x>=1. This implication
supplies sign transport for a candidate positive carrier; it does not
assert that any nonzero y satisfies its premise.

## Dependency-closed proof

For p outside S, restrict f_y to p-free indices. Multiplication by p changes
its sign there; indices divisible by p twice vanish by Möbius squarefreeness.
Hence the old sequence is its p-free restriction minus its p-dilation. Inserting
p into the retained field uses the same decomposition with the two coordinate
maps y(R) and y(insert p R). Injective L-series reindexing makes dilation
multiply the series by p^(-w). The finite subset numerator obeys the same
recursion. The empty-set case is the ordinary Möbius inverse-zeta identity.
A finite coordinate-norm majorant proves absolute convergence throughout
Re(w)>1 and justifies the recursive subtraction.

The corpus's exact Möbius convolution of b is the completed
prime–polar–Gamma atom. Its L-series is the von-Mangoldt logarithmic derivative,
minus zeta, plus the delta constant 2*gamma. Absolute convolution identifies
the actual retained g_y. Finite summatory interchange and the clipped channel
formula give the exact discrete square-root Abel identity.

The existing divisor-defect estimate `abs(D(n))<=24*sqrt(n)` bounds each
summatory convolution term. Summing the finite coordinate-norm majorant
gives the stated N^(3/2) bound. The corpus summatory-step Mellin theorem
supplies the factor 1/(s-1/2). Mellin's absolutely convergent multiplicative
convolution theorem supplies the second factor 1/s; the square-root clock
contributes 1/2. Indicator support identifies the convolution with the
literal truncated integral.

On each open unit interval the summatory profile is constant. The fundamental
theorem of calculus for sqrt, and finite adjacent-interval integration, give
both the exact integer sum and interpolation formula. A real affine function
of a monotone clock lies between its endpoint values, yielding the one-sided
ray statement without a numerical test.

## Lean modules

- `RetainedPrimeMobiusEulerIdentity`: 17 public declarations.
- `RetainedPrimeDivisorConvolution`: 11 public declarations.
- `SquareRootSummatoryMellin`: 8 public declarations.
- `RetainedPrimeSourceMellin`: 2 public declarations.
- `RetainedPrimeSourceInterpolation`: 5 public declarations.

All five modules passed scratch development and exact-file `lake env lean`
checks; only their needed oleans were emitted. All five imports are wired
into RHTower. No umbrella or dependency build was run. No numerical
experiment or computational premise was used. All 43 new public declarations
were axiom-audited once: only `propext`, `Classical.choice` and `Quot.sound`
occur. Global formal lint passed with existing large-file warnings. Generated
formal indexes and the research search index were refreshed. Owned Lean
processes completed and temporary scratch/audit files were removed.

## Remaining proof gates

Construct the positive measure for a real retained functional, identify its
complex MGF germ with the literal Mellin expression centered at four, apply
the existing low-height Landau balls, and prove continuation identity across
the resulting half-plane. The surviving high poles should then exclude a
nonzero one-sided functional. That implication and the finite-dimensional
compactness producing actual cutoff witnesses and margins are not yet formal.

Even a proof for each fixed S supplies no uniform control on witness cutoffs,
clipping tolerances, prime-pool capacity or preparation energy as S grows.
Complete compatible cofinal coverage, PE4/PE4G/PE4C, SD1 and RH remain open.
