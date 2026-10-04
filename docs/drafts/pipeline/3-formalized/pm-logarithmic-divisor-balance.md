# PM: complete logarithmic balance of the actual centered divisor energy

- **ID:** pm-logarithmic-divisor-balance
- **Stage:** 3-formalized
- **Type:** THEOREM (dependency-closed finite identities)
- **Lean:** `GaloisForLFunctions/RHTower/PMPowerDampedMobiusLogConvolution.lean`.

## Exact source and statement

Use the existing literal coefficients c_epsilon(n), density alpha=Re(1/zeta(1+epsilon)), centered coefficients r(n)=c_epsilon(n)-alpha, and centered prefixes R(N)=sum_(1<=n<=N)r(n). Define

`b(d)=Lambda(d)*(1-d^(-epsilon))`,
`l(n)=sum_(d|n)Lambda(d)*d^(-epsilon)`.

For every real epsilon and every natural n,

`c_epsilon(n)*log n = sum_(d|n)b(d)*c_epsilon(n/d)`,
`r(n)*log n = sum_(d|n)b(d)*r(n/d)-alpha*l(n)`.

The kernel b is nonnegative for epsilon>=0; l is nonnegative for every real epsilon. The density and every existing coefficient are retained exactly.

For every natural N, define the full dilation covariance D_N, lower-prefix covariance P_N and forcing covariance F_N by

`D_N=sum_(1<=n<=N) R(n)/[n(n+1)] * sum_(1<=d<=n)b(d)*R(floor(n/d))`,
`P_N=sum_(1<=n<=N) R(n)/[n(n+1)] * sum_(0<=k<n)R(k)*[log(k+1)-log k]`,
`F_N=sum_(1<=n<=N) R(n)/[n(n+1)] * sum_(1<=d<=n)Lambda(d)d^(-epsilon)*floor(n/d)`.

The exact signed energy law is

`sum_(1<=n<=N)log(n)*R(n)^2/[n(n+1)] = D_N+P_N-alpha*F_N`.

There are no hypotheses about energy, zeros, cancellation, positivity of R, or convergence. This is a finite identity for the complete actual source.

## Paper proof

Let T_epsilon be multiplication of an arithmetic function by n^(-epsilon). Complete multiplicativity of this weight makes T_epsilon preserve finite Dirichlet convolution, and it commutes with multiplication by log n. Twist the existing identity `mu*log=-(Lambda convolution mu)` to obtain the logarithmic derivative of the damped Mobius coefficient. Apply the logarithmic Leibniz rule to `c_epsilon=mu_epsilon convolution zeta`. Since `zeta*log=Lambda convolution zeta`, collecting the two terms gives `c_epsilon*log=(Lambda-T_epsilon Lambda) convolution c_epsilon`, exactly the first displayed law.

Subtract alpha*log n and use `sum_(d|n)Lambda(d)=log n`. Splitting Lambda into b+T_epsilon Lambda gives the centered law and its explicit negative forcing. Nonnegativity of b follows from d^(-epsilon)<=1 for d>=1; the zero index has Lambda(0)=0. Nonnegativity of l follows term by term.

Sum the centered law over 1<=n<=N and apply the exact divisor swap `(n,d)->(d,n/d)`. The first term becomes `sum_(d<=N)b(d)R(floor(N/d))`. The forcing is `alpha*sum_(d<=N)Lambda(d)d^(-epsilon)*floor(N/d)`. Finite Abel summation gives

`R(N)log N = sum_(n<=N)r(n)log n + sum_(k<N)R(k)[log(k+1)-log k]`.

This supplies the complete prefix recurrence. Multiply it by R(N)/[N(N+1)] and sum through the outer cutoff. Distribute finite sums exactly to obtain the three-covariance energy identity, retaining every mixed term and every natural floor.

## Contribution and remaining problem

The law exposes the actual centered arithmetic term `D_N-alpha*F_N` that must be controlled together with the lower-prefix operator. The forcing has a fixed minus sign before multiplication by R, but its covariance does not inherit a sign. No energy upper bound follows merely from kernel positivity. The active coercivity attempt is [logarithmic covariance](../1-in-progress/pm-logarithmic-covariance-balance.md). RH and cofinal small-positive-damping admission remain open.

## Corpus and verification

Search169 was partial with inventory65077 complete and mixed compiler freshness; all candidate/source statements and ingredients were inspected. Applicable source inputs were found in the literal PM divisor/centered-energy definitions, the finite logarithmic derivation, Mobius log recursion, and divisor swap. All twelve public exports (five definitions and seven theorems) are audited. Targeted `lake --old build GaloisForLFunctions.RHTower.PMPowerDampedMobiusLogConvolution` passed, compiling the leaf in60s and replaying existing dependencies. Mandatory `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusLogConvolution.lean` passed with exit0 and no diagnostics. All twelve separate /tmp axiom queries passed with only propext, Classical.choice and Quot.sound. Umbrella wired once, generated indexes refreshed and whitespace checks passed. No full/umbrella build, numerical experiment, heartbeat increase, added axiom or RH premise.

Formal lint exits1 on twelve unrelated unreachable leaves: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MertensProductDiamondPintz, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving, and HTGeometry.CompactMonoidMeasureAlgebra. No finding names this leaf. No global lint pass or RH conclusion is claimed.
