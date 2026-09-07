# CCM-FU: signed terminal modular mean

- **Stage:** 3-formalized
- **Type:** [BRIDGE], derived source estimate.
- **Parent:** [complete reserve-extension induction](../1-in-progress/ccm-fu-reserve-extension-induction.md).
- **Goal:** Complete signed Abel source bound, CCM-FU chain, RH.
- **Proved:** The actual unit-channel limit
  `K_1(M)/sqrt(M) -> c`, with `c=log(2*pi)/2-gamma-1/4`.
- **Uniform extension:** For every epsilon>0 there is one T>=1 such that
  every positive dilation d with `M/d>=T` satisfies
  `|K_d(M)-c*sqrt(M)|<=epsilon*sqrt(M)`, including clipped endpoints.

The existing exact smooth mean and second-centered Abel identity isolate one
leading-order terminal term: the sum of modular primitives over
all moduli up to `sqrt(M)`. Bounding its summands separately produces the
coefficient band. The signed sum now collapses that band to one exact
coefficient. This is a derived analytic estimate, not a replacement
for the signed source bound or an assumption about RH.

Write `B_d=(d^2-1)/(12d)`, `P_d(M)=-r(d-r)/(2d)`, `r=M mod d`.
Then `B_d+P_d(M)=(d/2)*B_2({M/d})-1/(12d)`, where B_2 has zero mean.
The terminal estimate `sum_(d<=sqrt(M)) (B_d+P_d(M))=o(M)` is proved.

For each fixed nonzero Fourier frequency, split off a small initial modulus
interval by the trivial prefix bound. On the remaining interval, the literal reciprocal
phase `h*M/d` has second derivative comparable to `1/sqrt(M)`.
The corpus second-derivative test bounds every partial exponential sum by
`O(M^(1/4))`, with constants depending on epsilon and frequency. Finite
Abel summation restores the d weight, giving `o(M)`. Absolute summability
of the B_2 Fourier coefficients permits dominated passage through the
frequency sum. The reciprocal correction is harmonic and negligible.

More explicitly, with `N^2<=M<=4N^2`, positive frequency h and
`A=floor(N/k)+1`, every partial sum on `[A,b]`, b<=N, has norm at most
`(24*k^3*h+12)*sqrt(N)` once `N>=8h`. The complete modulus-weighted
sum has norm at most `3N*(N/k+1+(24*k^3*h+12)*sqrt(N))`.
First taking N large, then k large, gives the required cancellation.

Let C(M) be the centered hyperbola Abel term, T(M) the terminal modular
sum, and `w(M)=sqrt(M+1)-sqrt(M)`. The exact square-birth accounting gives
`|C(M)+floor(sqrt(M))/24-w(M)*T(M)|<=5*H_floor(sqrt(M))/48`.
The terminal estimate and harmonic error therefore give `C(M)/sqrt(M)->-1/24`.
Combining with smooth mean `a=log(2*pi)/2-gamma-1/6` gives the unit
coefficient `a-1/12=c`. Exact square-root interpolation transfers both
sides of the unit error estimate with the same nonnegative weights to
every positive dilation on a common quotient tail.

Lean modules are `RHTower/DivisorTerminalModularMean.lean` and
`RHTower/DivisorUnsignedChannelExactMean.lean`. Their five new public
theorems cover the Bernoulli mean, literal modular mean, centered Abel
coefficient, complete unit coefficient, and uniform dilation error.
Scratch and exact-file checks pass; only these two new oleans were emitted.
Each new public declaration was axiom-audited once and depends only on
`propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into
`RHTower.lean`. No numerical experiment, full build or umbrella build was run.
The corpus index is refreshed. The global lint run reports five unrelated
modules unreachable from their umbrella: `AutomorphicCoinduction`,
`CongruenceMaassCorrespondence`, `MaassHomogeneousSpaceCorrespondence`,
`RealUpperBorelPrincipalSeries`, and `SymmetricPowerArchimedeanExponents`.
Both modules from this proof are wired and pass their exact-file checks.
The previously verified stale dependency traces would expand a Lake dependency
audit into unrelated rebuilding; that audit remains unperformed.

The exact unit coefficient and uniform large-quotient error are now source
theorems. They do not bound the complete signed Möbius sum: the remaining
finite quotient profiles and changing signed retained fields still require
arithmetic compensation. The reserve-versus-geometric-cost inequality,
two-prime ceiling, complete reserve-extension induction and RH remain open.
