# Both signs of the prime error at every large cutoff

For every zero $\rho=\beta+i\gamma$ with $1/2<\beta<1$, there is $c_\rho>0$ such that, at every sufficiently large integer $N$, both signs satisfy
$$\sum_{\sqrt N<n\le N}\frac{\max(\pm(\psi(n)-n),0)}n\ge c_\rho N^\beta.$$
Consequently RH is equivalent to the following condition. For each $1/2<b<1$, arbitrarily large $N$ admit one sign for which the displayed mass is at most $K_bN^b$. The sign may depend on $N$. The proof applies even if the real parts of the zeros have no largest element. [Lean criterion and both-sign lower bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/EveryRightZeroForcesBothSignsOfThePrimeError.lean)

## Two alternating rows

Set $a(n)=(-1)^{n+1}$, $c(n)=\Lambda(n)-1$, $b=a*c$ for $n\ge1$. The prefix $A(N)$ of $a$ is $N\bmod2$. The prefix $P(N)$ of $b$ is the complete divisor count of the prime excess at $N$ minus twice that count at $\lfloor N/2\rfloor$. This cancels the linear term, giving $P(N)=O(\sqrt N)$. [Completed divisor count](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheCompletedCofactorRowRetainsThePrimeError.lean) · [Formal parity identity and square-root bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheAlternatingDivisorCountHasSquareRootError.lean)

Write $h(s)=1-2^{1-s}$. The continued Dirichlet symbols are $D=h\zeta$ and $B=-h(\zeta'+\zeta^2)$. At a right zero of multiplicity $k+1$, $h(\rho)\ne0$. Thus $D$ vanishes to order $k+1$, while $B^{(k)}(\rho)=d=-h(\rho)\zeta^{(k+1)}(\rho)\ne0$.

## Recovering absolute mass

For $u=a,b$ define $F_{u,x}(s)=\sum_{n\le x}u(n)(x/n)^s$ and $U(x)=\sum_{n\le x}u(n)$. Abel summation gives $F_{u,x}(s)=x^sD_u(s)+O(x^\theta)$ uniformly on a fixed closed disk about $\rho$ in $\Re s>\theta$, with $\theta=0,1/2$ respectively. Put
$$Q_u(x)=\left.\partial_s^k\big(F_{u,x}(s)-U(x)\big)\right|_{s=\rho}.$$
The subtraction makes $Q_u$ continuous at integer cutoffs and gives $Q_u(1)=0$. Cauchy's inequality and the symbol orders give $Q_b(x)=d x^\rho+O(\sqrt x)$.

For $j\le x\le y\le j+1$, the difference $Q_a(y)-Q_a(x)$ is the same derivative of $((y/x)^s-1)F_{a,x}(s)$, including the right endpoint since its new term cancels. The contribution from $x^sD(s)$ vanishes. On the fixed circle $|(y/x)^s-1|\ll_\rho\log(y/x)$. Cauchy's inequality on the bounded remainder and summation over crossed integers give $|Q_a(y)-Q_a(x)|\ll_\rho\log(y/x)$ for every $1\le x\le y$.

Finite divisor summation gives $Q_b(N)=\sum_{n\le N}c(n)Q_a(N/n)$. Partial summation and $Q_a(1)=0$ bound its absolute value by $C_\rho\sum_{n<N}|E(n)|/n$. The terms $n\le\sqrt N$ cost $O(\sqrt N)$ by Chebyshev's estimate. This gives the lower bound for $|E|$. [Symbol derivatives](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheAlternatingPrimeSymbolsAtARightZero.lean) · [Uniform Cauchy estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/UniformTailsOfShortDirichletPolynomials.lean) · [Finite wave and logarithmic increment bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ALocalPrimeWaveAtEveryRightZero.lean)

## Separating the two signs

Put $g(v)=\log v+(v^{-1}-1)/2$ for $v\ge1$ and $G_u(x)=\sum_{d\le x}u(d)g(x/d)$. Both $g(1)$ and $G_a(1)$ vanish. For $j<x<j+1$,
$$xG_a'(x)=A(j)-\frac1{2x}\sum_{d\le j}d\,a(d).$$
For $j=2l$ the right side is $l/(2x)$, and for $j=2l+1$ it is $1-(l+1)/(2x)$. Thus $1/6\le xG_a'(x)\le3/4$ on every open cell with $x>1$. Continuity at their endpoints gives
$$\tfrac16\log(1+1/n)\le w_n:=G_a(N/n)-G_a(N/(n+1))\le\tfrac34\log(1+1/n)\qquad(1\le n<N).$$

Partial summation gives $\sum_{n<N}w_n E(n)=G_b(N)$. Since $0\le vg'(v)\le1$, the summatory bound on $b$ gives $|G_b(N)|\ll\sum_{n<N}\sqrt n/n\ll\sqrt N$. The two weighted sign masses differ by $O(\sqrt N)$, while their sum dominates a fixed multiple of $\sum |E(n)|/n$. Removing $n\le\sqrt N$ again costs $O(\sqrt N)$. The sign comparison uses only the arithmetic divisor identity.

[Kernel composition and partial summation](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/FiniteDilationsOfArithmeticKernels.lean) · [Positive weights and signed estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PositiveWeightsForTheTwoSignsOfThePrimeError.lean)

For the converse criterion, a right zero gives a contradiction at any exponent $1/2<b<\beta$, even when the sign varies along the chosen cutoffs. Under RH, $|E(n)|\ll_b n^b$, and $\sum_{n\le N}n^{b-1}\le N^{b-1/2}\sum_{n\le N}n^{-1/2}\le 2N^b$ gives the required mass bound at every cutoff.

The main Lean declarations are `both_prime_sign_masses_at_every_large_cutoff` and `riemannHypothesis_iff_cofinal_one_signed_prime_means`. They use `alternatingSymbols_first_surviving_derivative`, `exists_alternating_prime_kernel_at_zero` and `abs_primeMeanWeight_sum_le`.
